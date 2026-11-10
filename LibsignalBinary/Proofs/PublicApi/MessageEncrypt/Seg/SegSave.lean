/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommon
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSaveFetch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `MessageEncrypt` `save_identity` Segment (`segSave_ok`)

Verifies `SaveStateV → ApplyStateV` (`+0xbd4..+0xc14`, `+0xd50..+0xd9c`): invokes the async
`save_identity` shim, poll, future drop, and box deallocation, transitioning to `ApplyStateV` on
`Ok c` or exiting via `tailStoreHookErr_ok` (`+0xe28`) on `Err`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
theorem cs_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x24 = s0.readReg64 .x24 := h.2.2.2.2.2.1
theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## Basic-Block Stepping Lemmas (`+0xbd4..+0xd9c`) -/

theorem step_bd4_to_be4 {b id_vt shimOff : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {remA idA : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xbd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + shimOff) s
      (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
       ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
       ((id_vt + 0x28#64) ↦₆₄ᵣ (b + shimOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
          ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
          ((id_vt + 0x28#64) ↦₆₄ᵣ (b + shimOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = idA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x350#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xbe8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xbd4 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_be8_to_bfc {b futVtOff pollOff : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xbe8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = b + futVtOff) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + pollOff) s
      (((s.sp + 0x470#64) ↦₆₄ u470) ∗
       ((s.sp + 0x478#64) ↦₆₄ u478) ∗
       ((b + futVtOff + 0x18#64) ↦₆₄ᵣ (b + pollOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
          ((b + futVtOff + 0x18#64) ↦₆₄ᵣ (b + pollOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = s.sp + 0x480#64 ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xc00#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xbe8 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_c00_to_d7c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u990 u998 u9a0 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xc00#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx22 : s.readReg64 .x22 = s.sp + 0x8b8#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hw0 : w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + futDropOff) s
      (((s.sp + 0x470#64) ↦₆₄ box) ∗
       ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
       ((s.sp + 0x580#64) ↦₆₄ w0) ∗
       ((s.sp + 0x588#64) ↦₆₄ w1) ∗
       ((s.sp + 0x590#64) ↦₆₄ w2) ∗
       ((s.sp + 0x598#64) ↦₆₄ w3) ∗
       ((s.sp + 0x5a0#64) ↦₆₄ w4) ∗
       ((s.sp + 0x5a8#64) ↦₆₄ w5) ∗
       ((s.sp + 0x990#64) ↦₆₄ u990) ∗
       ((s.sp + 0x998#64) ↦₆₄ u998) ∗
       ((s.sp + 0x9a0#64) ↦₆₄ u9a0) ∗
       ((b + futVtOff) ↦₆₄ᵣ (b + futDropOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
          ((s.sp + 0x580#64) ↦₆₄ w0) ∗
          ((s.sp + 0x588#64) ↦₆₄ w1) ∗
          ((s.sp + 0x590#64) ↦₆₄ w2) ∗
          ((s.sp + 0x598#64) ↦₆₄ w3) ∗
          ((s.sp + 0x5a0#64) ↦₆₄ w4) ∗
          ((s.sp + 0x5a8#64) ↦₆₄ w5) ∗
          ((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5) ∗
          ((b + futVtOff) ↦₆₄ᵣ (b + futDropOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = box ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x24 = b + futVtOff ∧ sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := beq_false_of_ne hdrop
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xc00 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xd50 0x30
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_d80_to_d90 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd80#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = box)
    (hx24 : s.readReg64 .x24 = b + futVtOff) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x3cbd8)) s
      (((b + futVtOff + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((b + futVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + futVtOff + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((b + futVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd94#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := beq_false_of_ne hsz
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xd80 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_d94_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd94#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe28#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xd94 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_d94_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd94#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd9c#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segSaveBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xd94 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-! ## Poll Buffer and Output Helpers -/

def savePollRest (sp : BitVec 64) : SepProp :=
  memRegion (sp + 0x46a#64) 6 ∗
  memRegion (sp + 0x480#64) 0x100 ∗
  memRegion (sp + 0x5b0#64) 0x3e0 ∗
  memRegion (sp + 0x9a8#64) 0x1d8

theorem savePoll_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x990#64) 24 ∗
      savePollRest sp := by
  unfold savePollRest
  rw [show (0x716 : Nat) = 6 + 0x710 by decide,
      memRegion_split (sp + 0x46a#64) 6 0x710 (by decide),
      show (0x710 : Nat) = 16 + 0x700 by decide,
      memRegion_split _ 16 0x700 (by decide),
      show (0x700 : Nat) = 0x100 + 0x600 by decide,
      memRegion_split _ 0x100 0x600 (by decide),
      show (0x600 : Nat) = 48 + 0x5d0 by decide,
      memRegion_split _ 48 0x5d0 (by decide),
      show (0x5d0 : Nat) = 0x3e0 + 0x1f0 by decide,
      memRegion_split _ 0x3e0 0x1f0 (by decide),
      show (0x1f0 : Nat) = 24 + 0x1d8 by decide,
      memRegion_split _ 24 0x1d8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem savePoll_merge_990 (sp w3 w4 w5 : BitVec 64) :
    memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      (((sp + 0x990#64) ↦₆₄ w3) ∗ ((sp + 0x998#64) ↦₆₄ w4) ∗ ((sp + 0x9a0#64) ↦₆₄ w5)) ∗
      savePollRest sp ⊢
    pollWith sp 0x990 [w3, w4, w5] := by
  unfold pollWith savePollRest
  dsimp only [words64At, List.length]
  change _ ⊢ memRegion (sp + 0x46a#64) 0x526 ∗
    (((sp + 0x990#64) ↦₆₄ w3) ∗ ((sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
      ((sp + 0x990#64 + 8#64 + 8#64) ↦₆₄ w5) ∗ emp) ∗
    memRegion (sp + 0x9a8#64) 0x1d8
  rw [show (0x526 : Nat) = 6 + (16 + (0x100 + (48 + 0x3e0))) by decide,
      memRegion_split (sp + 0x46a#64) 6 _ (by decide),
      memRegion_split _ 16 _ (by decide),
      memRegion_split _ 0x100 _ (by decide),
      memRegion_split _ 48 0x3e0 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp]
  exact Entails.of_eq

def savePassive (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗
  cmScratchRest sp ∗
  encSpillsRest ss_vt id_vt sp x ∗
  savePollRest sp ∗
  memRegion x.ret 248 ∗
  encCommonRest A ctl x draws s0

theorem save_seam_mem_split (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64) :
    cmSlots A sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x716 ∗
      memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 =
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      memRegion (sp + 0x990#64) 24) ∗
    savePassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, savePassive]
  rw [cmSlots_eq, cmScratch_eq, encSpillsAt_eq, encCommon_eq, savePoll_split]
  ac_rfl

theorem save_seam_mem_to_tail (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage)
    (draws : Nat) (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0xbe0#64)
    (P990 poll H : SepProp)
    (hpoll :
      memRegion (sp + 0x470#64) 16 ∗
        memRegion (sp + 0x580#64) 48 ∗ P990 ∗ savePollRest sp ⊢ poll) :
    (trustBaseActive id_vt A img sp x k ∗
      memRegion (sp + 0x470#64) 16 ∗
      memRegion (sp + 0x580#64) 48 ∗
      P990 ∗ H) ∗
    savePassive ss_vt id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0 ⊢
    ∃∗ g : RecordGhost,
      (dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) (some m)
          poll ∗ H) ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 := by
  subst hsp
  dsimp only [trustBaseActive, savePassive] at hpoll ⊢
  set sp := s0.sp - 0xbe0#64
  have hreord :
      (((sp + 0x40#64) ↦₆₄ (sp + 0x350#64) ∗ (sp + 0xc0#64) ↦₆₄ x.remA ∗
        (sp + 0xe0#64) ↦₆₄ x.idA ∗ (sp + 0xe8#64) ↦₆₄ id_vt ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ stackAt sp encSubStack ∗ A.pool) ∗
      memRegion (sp + 0x470#64) 16 ∗ memRegion (sp + 0x580#64) 48 ∗ P990 ∗ H) ∗
      (cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m ∗ cmScratchRest sp ∗
      encSpillsRest ss_vt id_vt sp x ∗ savePollRest sp ∗
      memRegion x.ret 248 ∗ encCommonRest A ctl x draws s0) =
      (memRegion (sp + 0x470#64) 16 ∗
        memRegion (sp + 0x580#64) 48 ∗ P990 ∗ savePollRest sp) ∗
      (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        cmSlotsRest A sp sess taken otr' pqCap' pqPtr' m) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗ encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248) := by
    rw [cmScratch_eq, encSpillsAt_eq, encCommon_eq]
    change _ = _ ∗ (_ ∗ _ ∗ _ ∗ (protocolAddressAt A x.rem x.remA ∗ logOff img ∗
      stackAt sp encSubStack ∗ A.pool ∗ encCommonRest A ctl x draws s0) ∗ _)
    ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono_left hpoll) ?_
  unfold cmSlotsRest takenSlots
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun g => Entails.sepExists_right g ?_
  have hslots := cmSlots_to_dropRecordSlots A sp g sess taken otr' pqCap' pqPtr' k m poll
  have hreord2 :
      poll ∗ (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
      (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗
      encSpillsAtV ss_vt id_vt sp x ∗ encCommon A ctl img x draws s0 ∗
      H ∗ memRegion x.ret 248 =
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        (sp + 0x280#64) ↦₆₄ (sp + 0x128#64) ∗ (sp + 0x468#64) ↦₈ 0#8 ∗ (sp + 0x469#64) ↦₈ 1#8 ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        (sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        apiEncResultAt A (sp + 0x370#64) (Except.ok m) ∗ cmScratch sp ∗ poll) ∗
      (H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0) := by
    ac_rfl
  rw [hreord2]
  exact sepConj_mono_left hslots

abbrev savePollOutHead (base out : BitVec 64) (ans : Except Unit IdentityChange) : SepProp :=
  match ans with
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 4
  | .error () =>
    (out ↦₆₄ 0x800000000000001A#64) ∗
      ((out + 8#64) ↦₆₄ (base + bv% (ls_reloc% 0x77cc)))

/-- Normalizes `savePollOutAt` after `ikit.savePoll` into six 64-bit words at `sp + 0x580`. -/
theorem savePollOut_words (b out : BitVec 64) (ans : Except Unit IdentityChange) :
    savePollOutAt b out ans ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ H : SepProp,
      ⌜(w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) ∧
        match ans with
        | .ok c => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
            w1.setWidth 32 = (if c == .replacedExisting then 1#32 else 0#32) ∧ H = emp
        | .error () =>
          w0 = 0x800000000000001A#64 ∧ w1 = b + bv% (ls_reloc% 0x77cc) ∧
          w2 = 10#64 ∧ w3 = 1#64 ∧ w4 = b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) ∧
          H = ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)⌝ ∗
      (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₆₄ w5) ∗ H := by
  rcases ans with ⟨⟨⟩⟩ | c
  · dsimp only [savePollOutAt, errTailAt]
    rw [ProofLib.memRegion_eight (out + 0x28#64)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    refine Entails.sepExists_right 0x800000000000001A#64 ?_
    refine Entails.sepExists_right (b + bv% (ls_reloc% 0x77cc)) ?_
    refine Entails.sepExists_right 10#64 ?_
    refine Entails.sepExists_right 1#64 ?_
    refine Entails.sepExists_right (b + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right ((b + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) ?_
    refine Entails.pure_right ⟨Or.inr rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [savePollOutAt]
    rw [show (36 : Nat) = 4 + (8 + (8 + (8 + 8))) by decide,
        memRegion_split (out + 0xc#64) 4 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 _ (by decide),
        memRegion_split _ 8 8 (by decide),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64 + 8#64),
        ProofLib.memRegion_eight (out + 0xc#64 + 4#64 + 8#64 + 8#64 + 8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w4 =>
      Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w2 => ?_
    have h32 := pointsTo32_memRegion4_exists_word64 (out + 8#64)
      (if c == .replacedExisting then 1#32 else 0#32)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
    have hreord :
        (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          (memRegion (out + 0xc#64) 4 ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
            ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
            ((out + 0x28#64) ↦₆₄ w5)) =
        (((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
          memRegion (out + 0xc#64) 4) ∗
        ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
          ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
          ((out + 0x28#64) ↦₆₄ w5)) := by ac_rfl
    rw [hreord]
    refine Entails.trans (sepConj_mono_left h32) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun w1 => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hw1 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64 ?_
    refine Entails.sepExists_right w1 ?_
    refine Entails.sepExists_right w2 ?_
    refine Entails.sepExists_right w3 ?_
    refine Entails.sepExists_right w4 ?_
    refine Entails.sepExists_right w5 ?_
    refine Entails.sepExists_right emp ?_
    refine Entails.pure_right ⟨Or.inl rfl, rfl, hw1, rfl⟩ ?_
    rw [sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-! ## Shim, Poll, and Deallocation Path (`+0xbd4..+0xd94`) -/

theorem save_to_d94 {Scope Q img C A}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 ist1 : ikit.IdState}
    {ctl S encRecord abs}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {x : WithStoresEncGhost} {k : IdentityKey} {F R R0 : SepProp} {s0 s : State}
    {next : State → Prop}
    (haddr : ikit.addrOk x.rem.val)
    (henv : ∀ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' → s'.trace = s.trace →
      ikit.envOk s'.fs.files)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0xbd4#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = s.sp + 0x8b8#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hm : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActive img ikit ist1 s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (ans : Except Unit IdentityChange) (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      Steps (tripleRatchetProgAt img.base C ctl abs) s sm →
      sm.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0xd94#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.spAligned = true →
      ikit.saveRel ist1 x.rem.val k ans →
      sm.trace = s.trace ++ ikit.saveEvs x.rem.val k ans →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 →
      sm.readReg64 .x21 = w1 →
      sm.readReg64 .x23 = w2 →
      (match ans with
       | .ok c => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
           w1.setWidth 32 = (if c == .replacedExisting then 1#32 else 0#32) ∧ H = emp
       | .error () =>
         w0 = 0x800000000000001A#64 ∧ w1 = img.base + bv% (ls_reloc% 0x77cc) ∧
         w2 = 10#64 ∧ w3 = 1#64 ∧ w4 = img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16) ∧
         H = ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) →
      (sm.mem ⊨ (trustActive img ikit (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R)) →
      SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hR : R ⊢ anyHeap ∗ R0 := by exact sepConj_mono_left (entails_anyHeap _)) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hb_align : img.base &&& 0xfff#64 = 0#64 :=
    ProofLib.ObjectLoad.base_aligned_of_loads env.loads
  have hm1 : s.mem ⊨ (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
      ((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((s.sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((s.sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗
      ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff))) ∗
      (((((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ ikit.identityAt x.idA ist1 ∗ stackAt s.sp (encSubStackV kit ikit) ∗ A.pool ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [saveVtablesAt, trustActive] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExit.of_sepWP hm1 (step_bd4_to_be4 hpc hrun hsp_align) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx30_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hfl1 : img.FrozenLoaded s1 := hsteps1.frozenLoaded hfl
  have hsym1 : s1.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hm3 : s1.mem ⊨ (kitSaveShimSpec ikit).pre ⟨x.idA, x.remA, s.sp + 0x350#64⟩ s1 ∗
      ((((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ ikit.identityAt x.idA ist1 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - ikit.saveShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitSaveShimSpec]
    rw [hsp1]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.saveShimStack
          (saveShimStack_le_encSubStackV kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_alloc (R0 := R0) env.ikitOk.saveShim ⟨x.idA, x.remA, s.sp + 0x350#64⟩
    hpc1 hrun1 hsp1_al hx30_1 hpref1 (inImage_pre_intro hfl1 hsym1 hm3) ?_ (hR := hR)
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hm4
  have hfl2 : img.FrozenLoaded s2 := hsteps2.frozenLoaded hfl1
  have hsym2 : s2.symtab = img.symtab := hsteps2.symtab_eq.trans hsym1
  dsimp only [Spec.inImage, kitSaveShimSpec] at hm4
  rw [hsp1] at hsp2 hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨⟨hx1_2, _, _, htr2⟩, hm4⟩ := hm4
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 ∗
        ikit.identityAt x.idA ist1 ∗ A.pool ∗
        stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.saveShimStack
          (saveShimStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗
      ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff))) ∗
      (((A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 ∗
        ikit.identityAt x.idA ist1 ∗ A.pool ∗
        stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A x.rem x.remA ∗
        logOff img ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine SegExit.of_sepWP hm6 (step_be8_to_bfc hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  have hsp3_al : s3.spAligned = true := spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2]; exact hpref1
  have hfl3 : img.FrozenLoaded s3 := hsteps3.frozenLoaded hfl2
  have hsym3 : s3.symtab = img.symtab := hsteps3.symtab_eq.trans hsym2
  let pollCall : IdentityPollCall := ⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x350#64, k⟩⟩
  have hm8 : s3.mem ⊨ (withLogOff (kitSavePollSpecE ikit) img).pre
      (pollCall, x.idA, ist1) s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - ikit.savePollStack) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [withLogOff, kitSavePollSpecE, kitSavePollSpec, withEnvPre, pollCall]
    rw [hsp3]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.savePollStack
          (savePollStack_le_encSubStackV kit ikit)] at hm7
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨henv s3 (hsteps1.trans (hsteps2.trans hsteps3)) (by rw [htr3, htr2, htr1]),
      ⟨hx0_3, hx8_3, haddr⟩,
      Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  refine call_alloc (R0 := R0) env.ikitOk.savePoll (pollCall, x.idA, ist1)
    hpc3 hrun3 hsp3_al hx30_3 hpref3 (inImage_pre_intro hfl3 hsym3 hm8) ?_ (hR := hR)
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hm9
  dsimp only [kitSavePollSpecI, Spec.inImage, withLogOff, kitSavePollSpecE, kitSavePollSpec,
    withEnvPre, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm9
  obtain ⟨ans, ⟨hsaveRel, htr4⟩, hm9⟩ := hm9
  have hm9_poll : s4.mem ⊨
      savePollOutAt img.base (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x990#64) 24 ∗
      (((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.savePollStack
          (savePollStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left
    (savePollOut_words img.base (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans⟩, hm10⟩ := hm10
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x990#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗ H ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u990, u998, u9a0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x990#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗
      ((s4.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗ ((s4.sp + 0x588#64) ↦₆₄ w1) ∗
      ((s4.sp + 0x590#64) ↦₆₄ w2) ∗ ((s4.sp + 0x598#64) ↦₆₄ w3) ∗
      ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗ ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x990#64) ↦₆₄ u990) ∗ ((s4.sp + 0x998#64) ↦₆₄ u998) ∗
      ((s4.sp + 0x9a0#64) ↦₆₄ u9a0) ∗
      ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff))) ∗
      (((A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img ∗ H) ∗ F) ∗ R) := by
    rw [hsp4]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx22_4 : s4.readReg64 .x22 = s4.sp + 0x8b8#64 := by
    rw [hsp4, cs_x22 hcs4, hx22_3, cs_x22 hcs2, hx22_1, hx22]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  refine SegExit.of_sepWP hm12
    (step_c00_to_d7c (ikit.saveFutDrop_ne_zero hb_align) hpc4 hrun4 hsp4_align hx22_4 hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨rfl, hsp5, htr5, hx0_5, hx21_5, hx22_5, hx23_5, hx24_5, hx27_5, hx30_5,
      hx19_5, hx20_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  have hsp5_al : s5.spAligned = true := spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗
        (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff))) ∗
      ((A.live box ikit.saveBoxSize 8 ∗
        ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img ∗ H) ∗ F)) ∗ R) := by
    dsimp only [futDropSpec]
    rw [emp_sepConj]
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine call_nopanic (R0 := R0) env.ikitOk.saveFutDrop ()
    hpc5 hrun5 hsp5_al hx30_5 hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropSpec] at hm15
  rw [hsp5] at hsp6
  rw [satisfies_pure_sepConj] at hm15
  obtain ⟨htr6, hm15⟩ := hm15
  have hm15_box : s6.mem ⊨
      ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
      ((((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗
        (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        A.live box ikit.saveBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img ∗ H) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15' := Satisfies.mono (sepConj_mono_left
    (ikit.saveBoxAt_memRegion box x.idA x.remA (s.sp + 0x350#64) 1#8)) hm15_box
  have hm16 : s6.mem ⊨ (((img.base + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
      ((img.base + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗
        (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((img.base + ikit.saveFutVtOff) ↦₆₄ᵣ (img.base + ikit.saveFutDropOff)) ∗
        memRegion box ikit.saveBoxSize ∗ A.live box ikit.saveBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (img.base + ikit.saveShimOff)) ∗
        ((img.base + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + ikit.savePollOff)) ∗
        logOff img ∗ H) ∗ F) ∗ R) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15'
  have hx22_6 : s6.readReg64 .x22 = box := (cs_x22 hcs6).trans hx22_5
  have hx24_6 : s6.readReg64 .x24 = img.base + ikit.saveFutVtOff := (cs_x24 hcs6).trans hx24_5
  refine SegExit.of_sepWP hm16
    (step_d80_to_d90 ikit.saveBoxSize_ne_zero hpc6 hrun6 hx22_6 hx24_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  have hsp7_al : s7.spAligned = true := spAligned_of_sp_eq hsp_al hsp7
  have hm18 : s7.mem ⊨ (rustDeallocSpec A).pre (box, ikit.saveBoxSize, 8) s7 ∗
      (((saveVtablesAt ikit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + ikit.saveFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
          (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
          (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗ ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - allocHookStack) ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xe0#64) ↦₆₄ x.idA ∗
        (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        logOff img ∗ H) ∗ F) ∗ R) := by
    dsimp only [rustDeallocSpec, saveVtablesAt]
    rw [hsp7]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ikit.saveBoxSize_lt],
      by rw [hx2_7]; rfl⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  refine call_nopanic (R0 := R0) (dealloc_ok_at_enc env) (box, ikit.saveBoxSize, 8) hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  dsimp only [rustDeallocSpec] at hm19
  rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨htr8, hm19⟩ := hm19
  have hm20 : s8.mem ⊨ saveVtablesAt ikit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (img.base + ikit.saveFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗
        ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((trustActive img ikit (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R))) := by
    dsimp only [trustActive]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (img.base + ikit.saveFutVtOff))
    (sepConj_mono_left
      (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_all :=
    hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans
      (hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))))))
  refine hcont s8 ans w0 w1 w2 w3 w4 w5 H hsteps_all hpc8 hrun8 hsp8 hsp8_al hsaveRel
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])
    (by rw [cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5,
            cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [cs_x20 hcs8, hx20_7, cs_x20 hcs6, hx20_5,
            cs_x20 hcs4, hx20_3, cs_x20 hcs2, hx20_1])
    (by rw [cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5,
            cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1])
    (by rw [cs_x26 hcs8, hx26_7, cs_x26 hcs6, hx26_5,
            cs_x26 hcs4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5,
            cs_x28 hcs4, hx28_3, cs_x28 hcs2, hx28_1])
    (by rw [cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5,
            cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1])
    (by rw [cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5,
            cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1])
    (by rw [cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5])
    (by rw [cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5])
    (by rw [cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5])
    hans
    (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

/-! ## Main Theorem (`segSave_ok`) -/

theorem segSave_okV {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegSaveSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s haddr hfs hsave
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨⟨h15, htrustRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx22, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hsave
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set ist1 := ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)
  set F := savePassive kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActive ikit.id_vt A img s.sp x k ∗ encStoreExtra kit st0 ikit ist1 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommon A ctl img x draws s0) ∗
        (encStoreExtra kit st0 ikit ist1 x s0 ∗ R0) := by
      rw [hsp]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [save_seam_mem_split kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra kit st0 ikit ist1 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  have hm_split : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActive img ikit ist1 s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R) := by
    have hm' := saveVtablesAt_intro env.idVtables hfl hm_join
    dsimp only [R]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx22' : s.readReg64 .x22 = s.sp + 0x8b8#64 := by rw [hsp]; exact hx22
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hpc_bd4 : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0xbd4#64 := by
    rw [hpc, savePC, encEntry_eq_fnAddr env]
  refine save_to_d94 (R0 := R0) env haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
        simp only [NoFsEv.append_iff, hl, ht, and_self]).2)
    hbound hpc_bd4 hrun hsp_al hx22' hx25' hpref0 hfl hsym hm_split ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H hsteps_d94 hpcm hrunm hspm hspm_al hsaveRel htrm
    hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  let R' : SepProp := encStoreExtra kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActive ikit.id_vt A img s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x990#64) ↦₆₄ w3) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActive img ikit (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
          kit.storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ F ∗ R0) := by
      dsimp only [R] at hmm_act
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x k s0 s.sp hsp hbound)) hmm1
    dsimp only [R']
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have ⟨hflm, hsymm⟩ := callInv_steps hfl hsym hsteps_d94
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k ans)) := by
    rw [htrm, htr, List.append_assoc, List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | c
  ·
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP hmm_emp (step_d94_err hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have ⟨hfl_err, hsym_err⟩ := callInv_steps hflm hsymm hsteps_err
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent := save_seam_mem_to_tail kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
        ((s.sp + 0x998#64) ↦₆₄ (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16))) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5))
      (pollWith s.sp 0x990 [1#64, img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16), w5])
      ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr)
      (savePoll_merge_990 s.sp 1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm :=
      StepsThroughEncrypt.tailModel_save_err (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrustRel hsaveRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfSaveErr r) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfSaveErr r) rfl
    refine SegExit.of_false
      (tailStoreHookErr_ok env x R0 s0 s_err (answersOfSaveErr r) (.store ())
        0x800000000000001A#64 (img.base + bv% (ls_reloc% 0x77cc)) 10#64
        1#64 (img.base + bv% (ls_xref% 0xc9ec 0xc9f0 + 16)) w5
        ((img.base + bv% (ls_reloc% 0x77cc)) ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xe28 0x990 (Or.inr (Or.inl rfl))
        htm (speStaged_storeErr A img.base x.ret w5) ?_)
    refine ⟨by rw [hpc_err, encEntry_eq_fnAddr env],
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hfl_err, hsym_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_save_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, ist1, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfSaveErr, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, _, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5))) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP hmm_emp (step_d94_ok hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have ⟨hfl_ok, hsym_ok⟩ := callInv_steps hflm hsymm hsteps_ok
    have hm_ok_990 : s_ok.mem ⊨
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x990#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x990#64) w3 w4 w5)) hm_ok_990
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x990#64) 24) ∗
          savePassive kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← save_seam_mem_split kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    intro _
    refine ⟨s_ok, Steps.refl s_ok, Or.inl ⟨c, ⟨h15, htrustRel, hsaveRel⟩, by rw [hpc_ok, applyPC, encEntry_eq_fnAddr env],
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hfl_ok, hsym_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc],
      ⟨by rw [hx20_ok, hx20m, hx20],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩⟩
    dsimp only [sp, draws, ist1, R'] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

theorem segSave_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegSaveSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  segSave_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
