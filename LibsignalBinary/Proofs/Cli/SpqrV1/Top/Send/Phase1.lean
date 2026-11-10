/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Phase 1 Prologue & Shared Epilogues for `spqr::send::<signal_session_ratchet::Coins>`

Proves `.rodata` jump-table extraction, the stack-allocating prologue (`+0 -> +76`), and
shared cleanup/return epilogues (`+904`, `+4608`, `+4632 -> s0.lr`) for the CLI image.
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

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b := by
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry]
  rw [Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff]

/-! ## 1. `.rodata` Jump Table Extraction from `img.FrozenLoaded` -/

/-- Extract `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base` (`0x9d4f0`, `22` bytes) from `img.FrozenLoaded s`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendStatesJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 340) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 344))) (n := 22) (bs := spqrSendStatesJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base` (`0x9d506`, `22` bytes) from `img.FrozenLoaded s`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendEncodeJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6608) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6612))) (n := 22) (bs := spqrSendEncodeJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base` (`0x9d51c`, `20` bytes) from `img.FrozenLoaded s`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendDropJumpTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6448) (ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>" + 6452))) (n := 20) (bs := spqrSendDropJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

/-- Extract the full `CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt img.base` bundle from `img.FrozenLoaded s`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendRoAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt img.base ∗ P := by
  unfold CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendStatesJumpTable himg hF ?_
  refine CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendEncodeJumpTable himg hF ?_
  refine CryptoVerification.Cli.SpqrV1.Top.Send.rodata_spqrSendDropJumpTable himg hF ?_
  refine rodata_v1StateJumpTables himg hF ?_
  refine rodata_statesFromPbJumpTable himg hF ?_
  refine rodata_statesIntoPbJumpTable himg hF ?_
  exact GF.UnacceleratedMul.rodata_reduceTable himg hF hP

/-! ## 2. Stack Address Normalization & Shared Epilogue (`+4632..+4668`) -/

/-- Epilogue (`+4632 -> s0.lr`):
    adds `0x1000 + 0xf20 = 0x1f20` (`7968`) to `sp = s0.sp - 0x1f80`, restores `x19..x30`
    from `s0.sp - 96`, and executes `ret`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_epilogue_4632 {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 4632#64)
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
  rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 4632 36
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-- Prologue (`+0 -> +76`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 0x1f80`,
    `x19 = ret`, `x0 = stV`, `x8 = x21 = x26 = sp + 0x1260`, and probes `[s0.sp - 4192]` and `[sp]`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_prologue {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (tripleRatchetProgAtExt b ext)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 76#64) s0
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
  rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc ⊢
  spqr_send_fetches_range_cli b (Rust.withPanics ext) 0 76
  dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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

/-! ## 3. Shared Cleanup Epilogues (`+4608` and `+896..+920`) -/

/-- Shared `st.chain` drop + register-restore epilogue (`+4608 -> s0.lr`):
    drops `ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh` (calling `CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName` when `some`), rejoins `memRegion (s0.sp - 0x1f80#64) 0x1f20`,
    and runs `CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_epilogue_4632`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_chain_drop_epilogue_4608 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (optCh : Option ChainPB) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 4608#64)
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
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]"))
      (dropProtoSpqrChainSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#2]")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChain_fnOff (by decide))
    hdrop
  refine EncoderFromPb.seq_clean
    (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (A.pool ∗ Rest))
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 4608 24
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, dropProtoSpqrChainSpec,
      chainPBSize, BitVec.ofNat_eq_ofNat] at hpc hdrop_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
    have hep := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_epilogue_4632 (ext := ext) s0 s2 (A.pool ∗ Rest) hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

/-- Shared `st.version_negotiation.auth_key` dealloc + `st.chain` drop + register-restore epilogue
    (`+904 -> s0.lr`, `+904 -> +4608..`):
    loads `w1` from `[sp + 0x38]`, calls `__rust_dealloc(w1, w0.toNat, 1)`, and jumps to `+4608`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_vn_chain_drop_epilogue_904 {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hdrop : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 904#64)
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
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := Drop.sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  refine EncoderFromPb.seq_clean
    (mid := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEntry b + 4608#64)
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
  · rw [← CryptoVerification.Cli.SpqrV1.Top.Send.fnAddr_spqrSend_eq b ext] at hpc ⊢
    spqr_send_fetches_range_cli b (Rust.withPanics ext) 904 20
    dsimp only [tripleRatchetProgAtExt, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::send::<libsignal_cli_ratchet::Coins>" = entry
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
    have hep := CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_chain_drop_epilogue_4608 hdrop s0 s2 optCh Rest hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨hPf, hsp_f, hcc_f, htr_f.trans htr2⟩

end CryptoVerification.SpqrV1.Top.Send
