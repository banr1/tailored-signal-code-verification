/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>` Phase 1c: `<States>::from_pb` Call, Error Path, and Jump-Table Dispatch

**Checked by Lean.**

Verifies the pre-call setup at `+224`, the `.error (.err err)` cleanup return path at `+248`,
and the `.ok st0` `32 + 896`B relocation (`sp + 0x1260 -> sp + 0x950`) and 11-way jump-table 1
dispatch (`0x30954..0x309cc`) to `spqrSendEntry b + statesSendArmOffset st0`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

/-! ## Pre-Call Step (`+224 -> statesFromPb`, `0x3093c..0x30950`) -/

@[local arm64_norm, local wp_norm]
theorem sp_add_30_add_80 (sp : BitVec 64) : (sp + 0x30#64) + 128#64 = sp + 0xb0#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_8 (sp : BitVec 64) : (sp + 0x1260#64) + 8#64 = sp + 0x1268#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_16 (sp : BitVec 64) : (sp + 0x1260#64) + 16#64 = sp + 0x1270#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_24 (sp : BitVec 64) : (sp + 0x1260#64) + 24#64 = sp + 0x1278#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1260_add_32 (sp : BitVec 64) : (sp + 0x1260#64) + 32#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_8 (sp : BitVec 64) : (sp + 0x1268#64) + 8#64 = sp + 0x1270#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_16 (sp : BitVec 64) : (sp + 0x1268#64) + 16#64 = sp + 0x1278#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_1268_add_24 (sp : BitVec 64) : (sp + 0x1268#64) + 24#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_930_add_8 (sp : BitVec 64) : (sp + 0x930#64) + 8#64 = sp + 0x938#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_930_add_16 (sp : BitVec 64) : (sp + 0x930#64) + 16#64 = sp + 0x940#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_8 (sp : BitVec 64) : (sp + 0x950#64) + 8#64 = sp + 0x958#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_16 (sp : BitVec 64) : (sp + 0x950#64) + 16#64 = sp + 0x960#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_24 (sp : BitVec 64) : (sp + 0x950#64) + 24#64 = sp + 0x968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_950_add_32 (sp : BitVec 64) : (sp + 0x950#64) + 32#64 = sp + 0x970#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_8 (sp : BitVec 64) : (sp + 0x958#64) + 8#64 = sp + 0x960#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_16 (sp : BitVec 64) : (sp + 0x958#64) + 16#64 = sp + 0x968#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_958_add_24 (sp : BitVec 64) : (sp + 0x958#64) + 24#64 = sp + 0x970#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_608 (sp : BitVec 64) : (sp + 4096#64) + 608#64 = sp + 0x1260#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_640 (sp : BitVec 64) : (sp + 4096#64) + 640#64 = sp + 0x1280#64 := by bv_omega
@[local arm64_norm, local wp_norm]
theorem sp_add_4096_add_96 (sp : BitVec 64) : (sp + 4096#64) + 96#64 = sp + 0x1060#64 := by bv_omega
@[local arm64_norm, local wp_norm]
private theorem bv_add_add_lit_p1d (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

theorem fnAddr_statesFromPb_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName =
      spqrSendEntry b + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::v1::chunked::states::States>::from_pb") := by
  dsimp only [tripleRatchetProgAtExt, spqrSendEntry]
  rw [Program.fnAddr_rebase, statesFromPb_fnOff]
  bv_omega

/-- Pre-call setup (`0x3093c..0x30950`, `+224 -> spqrSendEntry b + 170056#64`):
    computes `x8 = sp + 0x1260`, `x0 = sp + 0xb0`, `x21 = sp + 0x1260`, and branches with link
    (`x30 = spqrSendEntry b + 248#64`) to `<States>::from_pb` (`0x5a0a4`). -/
theorem spqr_send_pre_states_from_pb_224
    {b : BitVec 64} {ext : String → Option (State → State)}
    {s0 s : State} {sp : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendEntry b + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 0x30#64)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = sp + 0xb0#64 →
      sf.readReg64 .x8 = sp + 0x1260#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = sp + 0x30#64 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      sf.readReg64 .x30 = spqrSendEntry b + 248#64 →
      SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName) sf P post) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName) s P post := by
  rw [fnAddr_statesFromPb_eq b ext] at hnext ⊢
  rw [← fnAddr_spqrSend_eq b ext] at hpc hnext ⊢
  spqr_send_fetches_range b (Rust.withPanics ext) 224 24
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_steps
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩ (by simp only [arm64_norm, *])

/-! ## `States.from_pb = .error (.err err)` Return Path (`+248 -> s0.lr`) -/

theorem resultChunkedStatesAt_err_entails_head32_896 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : LibsignalSpqrV1.Error) :
    resultChunkedStatesAt A (F := F) a (.error (.err err)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
        ((a + 8#64) ↦₆₄ w1) ∗
        ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗
        memRegion (a + 32#64) 896 := by
  unfold resultChunkedStatesAt
  have hm8 : ((a + 8#64) ↦₈ spqrErrorByte err) ∗ memRegion (a + 9#64) 919 ⊢
      memRegion (a + 8#64) 920 := by
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 919) (b' := a + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 8#64) (spqrErrorByte err))
  refine Entails.trans (sepConj_mono_right hm8) ?_
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 912) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 904) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 896) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_sp_930_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x930#64) 24 =
      (∃∗ d0 : BitVec 64, ((sp + 0x930#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x938#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x940#64) ↦₆₄ d2)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 8) (k := 16)
        (b' := sp + 0x938#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x938#64) (n := 8) (k := 8)
        (b' := sp + 0x940#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x930#64),
      ProofLib.memRegion_eight (sp + 0x938#64),
      ProofLib.memRegion_eight (sp + 0x940#64)]

theorem words3_930_entails_memRegion_24 (sp w1 w2 w3 : BitVec 64) :
    ((sp + 0x930#64) ↦₆₄ w1) ∗ ((sp + 0x938#64) ↦₆₄ w2) ∗ ((sp + 0x940#64) ↦₆₄ w3) ⊢
      memRegion (sp + 0x930#64) 24 := by
  rw [memRegion_sp_930_split_24 sp]
  exact sepConj_mono (Entails.sepExists_intro w1)
    (sepConj_mono (Entails.sepExists_intro w2) (Entails.sepExists_intro w3))

theorem words4_and_896_1260_entails_memRegion_928 (sp w0 w1 w2 w3 : BitVec 64) :
    ((sp + 0x1260#64) ↦₆₄ w0) ∗ ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗ ((sp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (sp + 0x1280#64) 896 ⊢
      memRegion (sp + 0x1260#64) 928 := by
  have h928 : memRegion (sp + 0x1260#64) 928 =
      (∃∗ d0 : BitVec 64, ((sp + 0x1260#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x1268#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x1270#64) ↦₆₄ d2)) ∗
      (∃∗ d3 : BitVec 64, ((sp + 0x1278#64) ↦₆₄ d3)) ∗
      memRegion (sp + 0x1280#64) 896 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 8) (k := 920)
          (b' := sp + 0x1268#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1268#64) (n := 8) (k := 912)
          (b' := sp + 0x1270#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1270#64) (n := 8) (k := 904)
          (b' := sp + 0x1278#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x1278#64) (n := 8) (k := 896)
          (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (sp + 0x1260#64),
        ProofLib.memRegion_eight (sp + 0x1268#64),
        ProofLib.memRegion_eight (sp + 0x1270#64),
        ProofLib.memRegion_eight (sp + 0x1278#64)]
  rw [h928]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1)
      (sepConj_mono (Entails.sepExists_intro w2)
        (sepConj_mono_left (Entails.sepExists_intro w3))))

theorem memRegion_b0_to_1260_split_930 (fsp : BitVec 64) :
    memRegion (fsp + 0xb0#64) (0x1260 - 0xb0) ⊢
      ∃∗ s0_930 : BitVec 64, ∃∗ s1_938 : BitVec 64, ∃∗ s2_940 : BitVec 64,
        memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
        ((fsp + 0x930#64) ↦₆₄ s0_930) ∗
        ((fsp + 0x938#64) ↦₆₄ s1_938) ∗
        ((fsp + 0x940#64) ↦₆₄ s2_940) ∗
        memRegion (fsp + 0x948#64) (0x1260 - 0x948) := by
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 0x1260 - 0x930)
        (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 0x1260 - 0x948)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide),
      memRegion_sp_930_split_24 fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro s2_940
  apply Entails.sepExists_elim; intro s1_938
  apply Entails.sepExists_elim; intro s0_930
  refine Entails.sepExists_right s0_930
    (Entails.sepExists_right s1_938 (Entails.sepExists_right s2_940 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem rejoin_b0_to_1f20_after_states_err (fsp w0 w1 w2 w3 : BitVec 64) :
    memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      ((fsp + 0x930#64) ↦₆₄ w1) ∗
      ((fsp + 0x938#64) ↦₆₄ w2) ∗
      ((fsp + 0x940#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1280#64) 896 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) ⊢
      memRegion (fsp + 0xb0#64) (0x1f20 - 0xb0) := by
  have h930 := words3_930_entails_memRegion_24 fsp w1 w2 w3
  have h1260 := words4_and_896_1260_entails_memRegion_928 fsp w0 w1 w2 w3
  have hreord :
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      ((fsp + 0x930#64) ↦₆₄ w1) ∗
      ((fsp + 0x938#64) ↦₆₄ w2) ∗
      ((fsp + 0x940#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      ((fsp + 0x1260#64) ↦₆₄ w0) ∗
      ((fsp + 0x1268#64) ↦₆₄ w1) ∗
      ((fsp + 0x1270#64) ↦₆₄ w2) ∗
      ((fsp + 0x1278#64) ↦₆₄ w3) ∗
      memRegion (fsp + 0x1280#64) 896 ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) =
      (((fsp + 0x930#64) ↦₆₄ w1) ∗ ((fsp + 0x938#64) ↦₆₄ w2) ∗ ((fsp + 0x940#64) ↦₆₄ w3)) ∗
      (((fsp + 0x1260#64) ↦₆₄ w0) ∗ ((fsp + 0x1268#64) ↦₆₄ w1) ∗
       ((fsp + 0x1270#64) ↦₆₄ w2) ∗ ((fsp + 0x1278#64) ↦₆₄ w3) ∗
       memRegion (fsp + 0x1280#64) 896) ∗
      memRegion (fsp + 0xb0#64) (0x930 - 0xb0) ∗
      memRegion (fsp + 0x948#64) (0x1260 - 0x948) ∗
      memRegion (fsp + 0x1600#64) (0x1f20 - 0x1600) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h930 (sepConj_mono_left h1260)) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 0xb0#64) (n := 0x930 - 0xb0) (k := 0x1f20 - 0x930)
        (b' := fsp + 0x930#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x930#64) (n := 24) (k := 0x1f20 - 0x948)
        (b' := fsp + 0x948#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x948#64) (n := 0x1260 - 0x948) (k := 0x1f20 - 0x1260)
        (b' := fsp + 0x1260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 0x1260#64) (n := 928) (k := 0x1f20 - 0x1600)
        (b' := fsp + 0x1600#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

/-- `States.from_pb = .error (.err err)` path (`+248 -> +872 -> +4608/+904 -> s0.lr`):
    copies the `Err` header from `sp + 0x1260..0x1280` via `sp + 0x930..0x948` to `ret` (`x19`),
    drops `pq.versionNegotiation` (if `some`) and `pq.chain`, and returns to `s0.lr`. -/
theorem spqr_send_states_from_pb_err_step
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdropChain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A))
    (s0 s : State) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendEntry b + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1260 - 0xb0) ∗
        resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
        memRegion ret 72 ∗
        A.pool ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          spqrSendResultAt A ret none ∗
          A.pool ∗
          stackAt s0.sp spqrSendStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  by_cases hslt : BitVec.slt w0 1#64 = true
  · have hge_false := slt_one_true_iff hslt
    refine EncoderFromPb.seq_clean
      (mid := spqrSendEntry b + 4608#64)
      (P_mid :=
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗
        (spqrSendResultAt A ret none ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
      spqr_send_fetches_range b (Rust.withPanics ext) 248 28
      spqr_send_fetches_range b (Rust.withPanics ext) 872 36
      dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split := resultChunkedStatesAt_err_entails_head32_896 A (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
              (sepConj_mono herr_split
                (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro rw8
      apply ProofLib.SepWP.exists_left; intro rw16
      apply ProofLib.SepWP.exists_left; intro rw24
      apply ProofLib.SepWP.exists_left; intro ew1
      apply ProofLib.SepWP.exists_left; intro ew2
      apply ProofLib.SepWP.exists_left; intro ew3
      apply ProofLib.SepWP.exists_left; intro s0_930
      apply ProofLib.SepWP.exists_left; intro s1_938
      apply ProofLib.SepWP.exists_left; intro s2_940
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := rejoin_b0_to_1f20_after_states_err fsp LibsignalTripleRatchetRepr.noneCap ew1 ew2 ew3
        have hret := err_ret_entails_sendResultAt_none A ret ew1 ew2 ew3
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              DecodeState.optVersionNegotiationPBTailAt A w0 w1 (fsp + 64#64) vn)) ∗
            (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
            ((ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn_drop) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
      have hep := spqr_send_chain_drop_epilogue_4608 hdropChain s0 s2 chain
        (spqrSendResultAt A ret none ∗ Rest)
        hsp0_align hpc2 hrun2 hsp2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine SepWP.seq (mid := spqrSendEntry b + 904#64)
      (Mid := fun s1 P1 =>
        0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
          A.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool ∗
          (spqrSendResultAt A ret none ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · rw [← fnAddr_spqrSend_eq b ext] at hpc ⊢
      spqr_send_fetches_range b (Rust.withPanics ext) 248 28
      spqr_send_fetches_range b (Rust.withPanics ext) 872 36
      dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "spqr::send::<libsignal_session::HookRng>" = entry
      examples_hide_fetches
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split := resultChunkedStatesAt_err_entails_head32_896 A (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
              (sepConj_mono herr_split
                (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro rw8
      apply ProofLib.SepWP.exists_left; intro rw16
      apply ProofLib.SepWP.exists_left; intro rw24
      apply ProofLib.SepWP.exists_left; intro ew1
      apply ProofLib.SepWP.exists_left; intro ew2
      apply ProofLib.SepWP.exists_left; intro ew3
      apply ProofLib.SepWP.exists_left; intro s0_930
      apply ProofLib.SepWP.exists_left; intro s1_938
      apply ProofLib.SepWP.exists_left; intro s2_940
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
             DecodeState.optVersionNegotiationPBTailAt A w0 w1 (fsp + 64#64) vn) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600) ∗
             (ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40 ∗
             A.pool ∗
             spqrSendSavedRegs fsp s0 ∗
             Rest) by ac_rfl))
          (sepConj_mono_left hvn_drop)) ?_
      wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      refine ⟨hw0_pos, hw0_lt, hw1_ne, ?_,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
      have hb0 := rejoin_b0_to_1f20_after_states_err fsp LibsignalTripleRatchetRepr.noneCap ew1 ew2 ew3
      have hret := err_ret_entails_sendResultAt_none A ret ew1 ew2 ew3
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
           ((fsp + 2352#64) ↦₆₄ ew1) ∗
           ((fsp + 2360#64) ↦₆₄ ew2) ∗
           ((fsp + 2368#64) ↦₆₄ ew3) ∗
           memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
           ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
           ((fsp + 4712#64) ↦₆₄ ew1) ∗
           ((fsp + 4720#64) ↦₆₄ ew2) ∗
           ((fsp + 4728#64) ↦₆₄ ew3) ∗
           memRegion (fsp + 4736#64) 896 ∗
           memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
          ((ret ↦₆₄ 18446744073709551615#64) ∗
           ((ret + 8#64) ↦₆₄ ew1) ∗
           ((ret + 16#64) ↦₆₄ ew2) ∗
           ((ret + 24#64) ↦₆₄ ew3) ∗
           memRegion (ret + 32#64) 40) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32 ∗
           A.live w1 w0.toNat 1 ∗
           memRegion w1 w0.toNat ∗
           ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hb0 (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by ac_rfl)
    · intro s1 P1 hpc1 hrun1 ⟨hw0_pos, hw0_lt, hw1_ne, hP1, hsp1, hx23_1, htr1, hvregs1⟩
      refine SepWP.weaken_pre hP1 ?_
      have hep := spqr_send_vn_chain_drop_epilogue_904 hA.dealloc hdropChain s0 s1 w0 w1 chain
        (spqrSendResultAt A ret none ∗ Rest)
        hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-! ## `States.from_pb = .ok st0` Relocation and Jump-Table 1 Dispatch (`+248 -> Arm`) -/

@[simp, arm64_norm, wp_norm]
theorem chunkedStatesWord0_add_one_beq_zero {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    (chunkedStatesWord0 st0 + 1#64 == 0#64) = false := by
  cases st0 with
  | ct1Sampled s => exact polyEncoderTagVal_add_one_beq_zero s.sending_ct1.s
  | _ => rfl

theorem pointsToBytes_8_eq_one_cell (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 8) :
    (a ↦ₛ bs) ⊢ ∃∗ w : BitVec 64, ⌜bs = unpack64 w⌝ ∗ (a ↦₆₄ w) := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp only [List.length] at hlen; omega)
  refine Entails.sepExists_right (pack64 b0 b1 b2 b3 b4 b5 b6 b7) ?_
  have hpack : unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
    dsimp only [pack64]
    exact ProofLib.unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7
  rw [hpack]
  apply Entails.pure_right rfl
  rw [ProofLib.pointsTo64_eq_pointsToBytes, hpack]
  exact Entails.refl _

theorem pointsToBytes_920_split_3words_896 (a : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 920) :
    (a ↦ₛ bs) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) := by
  let b16 := bs.take 16
  let r16 := bs.drop 16
  let b8 := r16.take 8
  let bs896 := r16.drop 8
  have hb16 : b16.length = 16 := by simp [b16, hlen]
  have hr16 : r16.length = 904 := by simp [r16, hlen]
  have hb8 : b8.length = 8 := by simp [b8, hr16]
  have hbs896 : bs896.length = 896 := by simp [bs896, hr16]
  have hsplit : (a ↦ₛ bs) = (a ↦ₛ b16) ∗ ((a + 16#64) ↦ₛ b8) ∗ ((a + 24#64) ↦ₛ bs896) := by
    have hbs1 : bs = b16 ++ (b8 ++ bs896) := by
      simp only [b16, r16, b8, bs896, List.take_append_drop]
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append a b16, hb16,
        ProofLib.pointsToBytes_append (a + 16#64) b8, hb8]
    have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
    rw [ha24]
  rw [hsplit]
  refine Entails.trans
    (sepConj_mono (pointsToBytes_16_eq_two_cells a hb16)
      (sepConj_mono_left (pointsToBytes_8_eq_one_cell (a + 16#64) hb8))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w2
  have hpull :
      ((⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2)) ∗
       (⌜b8 = unpack64 w3⌝ ∗ ((a + 16#64) ↦₆₄ w3)) ∗
       ((a + 24#64) ↦ₛ bs896)) =
      ⌜b16 = unpack64 w1 ++ unpack64 w2⌝ ∗ ⌜b8 = unpack64 w3⌝ ∗
        ((a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro hw12
  apply Entails.pure_left; intro hw3
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_)))
  have hbs_eq : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
    calc bs = b16 ++ (b8 ++ bs896) := by simp only [b16, r16, b8, bs896, List.take_append_drop]
      _ = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 := by
          rw [hw12, hw3]
          simp only [List.append_assoc]
  exact Entails.pure_right ⟨hbs_eq, hbs896⟩ (Entails.refl _)

theorem words3_and_896_entails_pointsToBytes_920 (a w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    (a ↦₆₄ w1) ∗ ((a + 8#64) ↦₆₄ w2) ∗ ((a + 16#64) ↦₆₄ w3) ∗ ((a + 24#64) ↦ₛ bs896) ⊢
      (a ↦ₛ bs) := by
  subst hbs
  simp only [List.append_assoc]
  rw [pointsToBytes_append a (unpack64 w1), unpack64_length, ← pointsTo64_eq_pointsToBytes a w1,
      pointsToBytes_append (a + 8#64) (unpack64 w2), unpack64_length,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) w2,
      pointsToBytes_append ((a + 8#64) + 8#64) (unpack64 w3), unpack64_length,
      ← pointsTo64_eq_pointsToBytes ((a + 8#64) + 8#64) w3]
  have ha16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  have ha24 : (a + 16#64) + 8#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24]
  exact Entails.of_eq (by ac_rfl)

theorem chunkedStatesAt_1260_entails_reloc (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A (sp + 0x1260#64) st0 ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        ((sp + 0x1280#64) ↦ₛ bs896) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x1260#64) st0, sp_add_1260_add_8 sp]
  refine Entails.trans (sepConj_mono_right (Relocatable.of_chunkedStatesTail920At A st0 (sp + 0x1268#64))) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hlen920
  have hsplit := pointsToBytes_920_split_3words_896 (sp + 0x1268#64) hlen920
  rw [sp_add_1268_add_8 sp, sp_add_1268_add_16 sp, sp_add_1268_add_24 sp] at hsplit
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hsplit)) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs896
  refine Entails.sepExists_right bs (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_sp_950_split_4words_896 (sp : BitVec 64) :
    memRegion (sp + 0x950#64) 928 =
      (∃∗ d0 : BitVec 64, ((sp + 0x950#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x958#64) ↦₆₄ d1)) ∗
      (∃∗ d2 : BitVec 64, ((sp + 0x960#64) ↦₆₄ d2)) ∗
      (∃∗ d3 : BitVec 64, ((sp + 0x968#64) ↦₆₄ d3)) ∗
      memRegion (sp + 0x970#64) 896 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x950#64) (n := 8) (k := 920)
        (b' := sp + 0x958#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x958#64) (n := 8) (k := 912)
        (b' := sp + 0x960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 8) (k := 904)
        (b' := sp + 0x968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x968#64) (n := 8) (k := 896)
        (b' := sp + 0x970#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x950#64),
      ProofLib.memRegion_eight (sp + 0x958#64),
      ProofLib.memRegion_eight (sp + 0x960#64),
      ProofLib.memRegion_eight (sp + 0x968#64)]

theorem reassemble_chunkedStatesAt_950 (A : RustAlloc) {F : ShaCompress} (sp : BitVec 64)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (w1 w2 w3 : BitVec 64)
    {bs bs896 : List (BitVec 8)}
    (hbs : bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896) :
    ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
      ((sp + 0x958#64) ↦₆₄ w1) ∗
      ((sp + 0x960#64) ↦₆₄ w2) ∗
      ((sp + 0x968#64) ↦₆₄ w3) ∗
      ((sp + 0x970#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ⊢
      chunkedStatesAt A (sp + 0x950#64) st0 := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) st0, sp_add_950_add_8 sp]
  refine sepConj_mono_right ?_
  have h920 := words3_and_896_entails_pointsToBytes_920 (sp + 0x958#64) w1 w2 w3 hbs
  rw [sp_add_958_add_8 sp, sp_add_958_add_16 sp, sp_add_958_add_24 sp] at h920
  have hreord :
      ((sp + 0x958#64) ↦₆₄ w1) ∗ ((sp + 0x960#64) ↦₆₄ w2) ∗
      ((sp + 0x968#64) ↦₆₄ w3) ∗ ((sp + 0x970#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs =
      (((sp + 0x958#64) ↦₆₄ w1) ∗ ((sp + 0x960#64) ↦₆₄ w2) ∗
       ((sp + 0x968#64) ↦₆₄ w3) ∗ ((sp + 0x970#64) ↦ₛ bs896)) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left h920) ?_
  exact relocatedHeap_recompose (fun dst => chunkedStatesTail920At A dst st0) bs (sp + 0x958#64)

theorem reassemble_1260_after_memcpy (sp w0 w1 w2 w3 : BitVec 64)
    {bs896 : List (BitVec 8)} (hlen896 : bs896.length = 896) :
    ((sp + 0x1260#64) ↦₆₄ w0) ∗ ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗ ((sp + 0x1278#64) ↦₆₄ w3) ∗
      ((sp + 0x1280#64) ↦ₛ bs896) ⊢
      memRegion (sp + 0x1260#64) 928 := by
  have hm : ((sp + 0x1280#64) ↦ₛ bs896) ⊢ memRegion (sp + 0x1280#64) 896 := by
    rw [← hlen896]; exact pointsToBytes_entails_memRegion (sp + 0x1280#64) bs896
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm)))) ?_
  exact words4_and_896_1260_entails_memRegion_928 sp w0 w1 w2 w3

theorem spqrSendStatesJumpTableAt_eq_words (b : BitVec 64) :
    spqrSendStatesJumpTableAt b =
      spqrSendStatesJumpTableWordsAt (b + bv% (ls_xref% 0x30a94 0x30a98)) :=
  spqrSendStatesJumpTableBytes_eq (b + bv% (ls_xref% 0x30a94 0x30a98))

/-- Combined `States.from_pb = .ok st0` relocation + jump-table 1 dispatch
    (`+248 -> spqrSendEntry b + statesSendArmOffset st0`, `0x30954..0x309cc`):
    relocates `chunkedStatesAt A (sp + 0x1260) st0` to `chunkedStatesAt A (sp + 0x950) st0`
    and dispatches across all 11 `States` variants to `spqrSendEntry b + statesSendArmOffset st0`. -/
theorem spqr_send_states_from_pb_ok_step
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hA : AllocContracts b A ext)
    {s0 s : State} {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} {Frame : SepProp}
    {target_pc : BitVec 64} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendEntry b + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hnext : ∀ sf : State,
      sf.pc = spqrSendEntry b + statesSendArmOffset st0 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = chunkedStatesWord0 st0 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x950#64 →
      sf.readReg64 .x25 = sp + 0x550#64 →
      sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x28 = sp + 0x1060#64 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      SepWP (tripleRatchetProgAtExt b ext) target_pc sf
        ((chunkedStatesAt A (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTableAt b) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt b ext) target_pc s
      ((resultChunkedStatesAt A (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTableAt b) ∗ Frame) post := by
  rw [hfrom]
  dsimp only [resultChunkedStatesAt]
  have hsplit_ok :
      ((chunkedStatesAt A (sp + 0x1260#64) st0 ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTableAt b) ∗ Frame) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
         ((sp + 0x1268#64) ↦₆₄ w1) ∗
         ((sp + 0x1270#64) ↦₆₄ w2) ∗
         ((sp + 0x1278#64) ↦₆₄ w3) ∗
         ((sp + 0x1280#64) ↦ₛ bs896) ∗
         relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
         memRegion (sp + 0x930#64) 24 ∗
         memRegion (sp + 0x950#64) 928 ∗
         spqrSendStatesJumpTableAt b ∗ Frame) := by
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left (chunkedStatesAt_1260_entails_reloc A sp st0))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w1
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w2
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w3
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs896
    refine Entails.sepExists_right bs (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hsplit_ok ?_
  apply ProofLib.SepWP.exists_left; intro bs
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs896
  refine SepWP.pure_elim fun ⟨hbs, hlen896⟩ => ?_
  rw [memRegion_sp_930_split_24 sp, memRegion_sp_950_split_4words_896 sp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d3_968
  apply ProofLib.SepWP.exists_left; intro d2_960
  apply ProofLib.SepWP.exists_left; intro d1_958
  apply ProofLib.SepWP.exists_left; intro d0_950
  apply ProofLib.SepWP.exists_left; intro s2_940
  apply ProofLib.SepWP.exists_left; intro s1_938
  apply ProofLib.SepWP.exists_left; intro s0_930
  have hmemcpy := spqrSend_memcpy_ok hA
  have hadrp := fnAddr_adrp_309b0 (H := Rust.withPanics ext) hb
  rw [← fnAddr_spqrSend_eq b ext] at hpc hnext
  spqr_send_fetches_range b (Rust.withPanics ext) 248 124
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.call_subroutine_frame hmemcpy
    (x := (sp + 0x970#64, sp + 0x1280#64, bs896))
    (F := ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
      ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗
      ((sp + 0x1278#64) ↦₆₄ w3) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
      ((sp + 0x930#64) ↦₆₄ w1) ∗
      ((sp + 0x938#64) ↦₆₄ w2) ∗
      ((sp + 0x940#64) ↦₆₄ w3) ∗
      ((sp + 0x950#64) ↦₆₄ d0_950) ∗
      ((sp + 0x958#64) ↦₆₄ d1_958) ∗
      ((sp + 0x960#64) ↦₆₄ d2_960) ∗
      ((sp + 0x968#64) ↦₆₄ d3_968) ∗
      spqrSendStatesJumpTableAt b ∗ Frame)
    (ret_pc := entry + 308#64)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by unfold State.spAligned; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    ?_
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen896, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm]⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro s1 hpc1 hrun1 hsp1 hcc1
    dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr1⟩ => ?_
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp only [arm64_norm, *]
    have htr1' : s1.trace = s0.trace := by rw [htr1]; simp only [arm64_norm, *]
    have hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19 := by rw [hcc1.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = chunkedStatesWord0 st0 := by rw [hcc1.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = sp + 0x1260#64 := by rw [hcc1.2.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22 := by rw [hcc1.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_1 : s1.readReg64 .x23 = s.readReg64 .x23 := by rw [hcc1.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx24_1 : s1.readReg64 .x24 = sp + 0x950#64 := by rw [hcc1.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx25_1 : s1.readReg64 .x25 = sp + 0x550#64 := by rw [hcc1.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx26_1 : s1.readReg64 .x26 = sp + 0x1260#64 := by rw [hcc1.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx28_1 : s1.readReg64 .x28 = sp + 4192#64 := by rw [hcc1.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx29_1 : s1.readReg64 .x29 = s.readReg64 .x29 := by rw [hcc1.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s := by rw [hcc1.2.2.2.2.2.2.2.2.2.2.2]; simp only [wp_norm, arm64_norm, *]
    have hreasm :
        ((sp + 0x970#64) ↦ₛ bs896) ∗
        ((sp + 0x1280#64) ↦ₛ bs896) ∗
        ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
        ((sp + 0x930#64) ↦₆₄ w1) ∗
        ((sp + 0x938#64) ↦₆₄ w2) ∗
        ((sp + 0x940#64) ↦₆₄ w3) ∗
        ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x958#64) ↦₆₄ w1) ∗
        ((sp + 0x960#64) ↦₆₄ w2) ∗
        ((sp + 0x968#64) ↦₆₄ w3) ∗
        spqrSendStatesJumpTableWordsAt (b + bv% (ls_xref% 0x30a94 0x30a98)) ∗ Frame ⊢
        (chunkedStatesAt A (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTableAt b) ∗ Frame := by
      rw [← spqrSendStatesJumpTableAt_eq_words b]
      have hst := reassemble_chunkedStatesAt_950 A sp st0 w1 w2 w3 hbs
      have h930 := words3_930_entails_memRegion_24 sp w1 w2 w3
      have h1260 := reassemble_1260_after_memcpy sp (chunkedStatesWord0 st0) w1 w2 w3 hlen896
      have hreord1 :
          ((sp + 0x970#64) ↦ₛ bs896) ∗
          ((sp + 0x1280#64) ↦ₛ bs896) ∗
          ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x1268#64) ↦₆₄ w1) ∗
          ((sp + 0x1270#64) ↦₆₄ w2) ∗
          ((sp + 0x1278#64) ↦₆₄ w3) ∗
          relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
          ((sp + 0x930#64) ↦₆₄ w1) ∗
          ((sp + 0x938#64) ↦₆₄ w2) ∗
          ((sp + 0x940#64) ↦₆₄ w3) ∗
          ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x958#64) ↦₆₄ w1) ∗
          ((sp + 0x960#64) ↦₆₄ w2) ∗
          ((sp + 0x968#64) ↦₆₄ w3) ∗
          spqrSendStatesJumpTableAt b ∗ Frame =
          ((((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x958#64) ↦₆₄ w1) ∗
            ((sp + 0x960#64) ↦₆₄ w2) ∗
            ((sp + 0x968#64) ↦₆₄ w3) ∗
            ((sp + 0x970#64) ↦ₛ bs896) ∗
            relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs) ∗
           (((sp + 0x930#64) ↦₆₄ w1) ∗
            ((sp + 0x938#64) ↦₆₄ w2) ∗
            ((sp + 0x940#64) ↦₆₄ w3)) ∗
           (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x1268#64) ↦₆₄ w1) ∗
            ((sp + 0x1270#64) ↦₆₄ w2) ∗
            ((sp + 0x1278#64) ↦₆₄ w3) ∗
            ((sp + 0x1280#64) ↦ₛ bs896)) ∗
           spqrSendStatesJumpTableAt b) ∗ Frame := by ac_rfl
      rw [hreord1]
      exact sepConj_mono_left (sepConj_mono hst (sepConj_mono h930 (sepConj_mono_left h1260)))
    rw [spqrSendStatesJumpTableAt_eq_words b]
    dsimp only [spqrSendStatesJumpTableWordsAt, BitVec.ofNat_eq_ofNat] at hreasm ⊢
    cases st0 with
    | ct1Sampled st =>
      dsimp only [chunkedStatesWord0, statesSendArmOffset, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm hnext ⊢
      cases hs : st.sending_ct1.s <;>
        { rw [hs] at hx20_1 hreasm
          dsimp only [polyEncoderTagVal, polyEncoderPointsTag, polyEncoderPolysTag, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm ⊢
          wp_steps
          refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hreasm) ?_
          exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, polyEncoderTagVal, polyEncoderPointsTag, polyEncoderPolysTag, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩ }
    | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
    | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
    | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
      dsimp only [chunkedStatesWord0, statesSendArmOffset, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm hnext ⊢
      wp_steps
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hreasm) ?_
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

end CryptoVerification.SpqrV1.Top.Send
