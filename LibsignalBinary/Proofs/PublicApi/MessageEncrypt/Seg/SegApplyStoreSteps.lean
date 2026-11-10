/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.Prog
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreFetch
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Basic-Block Stepping Lemmas for `segApplyStore_ok`

Instruction-level `SepWP` stepping lemmas across `+0xd9c..+0xe88` of
`session_message_encrypt_with_stores`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

def otrWords25 (o : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64) : SepProp :=
  (o ↦₆₄ w0) ∗ ((o + 0x08#64) ↦₆₄ w1) ∗ ((o + 0x10#64) ↦₆₄ w2) ∗
  ((o + 0x18#64) ↦₆₄ w3) ∗ ((o + 0x20#64) ↦₆₄ w4) ∗ ((o + 0x28#64) ↦₆₄ w5) ∗ ((o + 0x30#64) ↦₆₄ w6) ∗
  ((o + 0x38#64) ↦₆₄ w7) ∗ ((o + 0x40#64) ↦₆₄ w8) ∗ ((o + 0x48#64) ↦₆₄ w9) ∗ ((o + 0x50#64) ↦₆₄ w10) ∗
  ((o + 0x58#64) ↦₆₄ w11) ∗ ((o + 0x60#64) ↦₆₄ w12) ∗ ((o + 0x68#64) ↦₆₄ w13) ∗ ((o + 0x70#64) ↦₆₄ w14) ∗
  ((o + 0x78#64) ↦₆₄ w15) ∗ ((o + 0x80#64) ↦₆₄ w16) ∗ ((o + 0x88#64) ↦₆₄ w17) ∗ ((o + 0x90#64) ↦₆₄ w18) ∗
  ((o + 0x98#64) ↦₆₄ w19) ∗ ((o + 0xa0#64) ↦₆₄ w20) ∗ ((o + 0xa8#64) ↦₆₄ w21) ∗ ((o + 0xb0#64) ↦₆₄ w22) ∗
  ((o + 0xb8#64) ↦₆₄ w23) ∗ ((o + 0xc0#64) ↦₆₄ w24)

theorem otrApply_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 18446744073709351128#64 =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrApplyName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x3cbd8]
  have hfn : libsignalSessionCode.fnOff otrApplyName = 0xbcb0 := by
    simp only [otrApplyName, arm64_norm]
  rw [hfn]
  bv_omega

set_option maxHeartbeats 1600000 in
theorem step_d9c_to_de4 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xd9c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 18446744073709351128#64) s
      (((s.sp + 0x38#64) ↦₆₄ (s.sp + 0x288#64)) ∗
       ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
       ((s.sp + 0x469#64) ↦₈ u469) ∗
       otrWords25 (s.sp + 0x288#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
         w18 w19 w20 w21 w22 w23 w24 ∗
       otrWords25 (s.sp + 0x580#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
         d18 d19 d20 d21 d22 d23 d24)
      (fun sf P_f =>
        P_f = (((s.sp + 0x38#64) ↦₆₄ (s.sp + 0x288#64)) ∗
          ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
          ((s.sp + 0x469#64) ↦₈ 0#8) ∗
          otrWords25 (s.sp + 0x288#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
            w18 w19 w20 w21 w22 w23 w24 ∗
          otrWords25 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
            w18 w19 w20 w21 w22 w23 w24) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = s.sp + 0x580#64 ∧ sf.readReg64 .x1 = s.sp + 0x128#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xde8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xd9c 0x4c
  dsimp only [tripleRatchetProgAt, otrWords25] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_de8_to_df8 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {remA ssA ss_vt shimOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + shimOff) s
      (((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xd0#64) ↦₆₄ ssA) ∗
       ((s.sp + 0xd8#64) ↦₆₄ ss_vt) ∗
       ((ss_vt + 0x20#64) ↦₆₄ᵣ (b + shimOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xd0#64) ↦₆₄ ssA) ∗
          ((s.sp + 0xd8#64) ↦₆₄ ss_vt) ∗
          ((ss_vt + 0x20#64) ↦₆₄ᵣ (b + shimOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = ssA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x110#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xdfc#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xde8 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_dfc_to_e10 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 futVtOff pollOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xdfc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = b + futVtOff) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + pollOff) s
      (((s.sp + 0x470#64) ↦₆₄ u470) ∗
       ((s.sp + 0x478#64) ↦₆₄ u478) ∗
       ((b + (futVtOff + 0x18#64)) ↦₆₄ᵣ (b + pollOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
          ((b + (futVtOff + 0x18#64)) ↦₆₄ᵣ (b + pollOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = s.sp + 0x480#64 ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe14#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xdfc 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_e14_to_e68 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u9b0 u9b8 u9c0 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe14#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
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
       ((s.sp + 0x9b0#64) ↦₆₄ u9b0) ∗
       ((s.sp + 0x9b8#64) ↦₆₄ u9b8) ∗
       ((s.sp + 0x9c0#64) ↦₆₄ u9c0) ∗
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
          ((s.sp + 0x9b0#64) ↦₆₄ w3) ∗
          ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9c0#64) ↦₆₄ w5) ∗
          ((b + futVtOff) ↦₆₄ᵣ (b + futDropOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x20 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = b + futVtOff ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe6c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := by simp [hdrop]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xe14 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xe38 0x34
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_e6c_to_e7c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe6c#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = box)
    (hx22 : s.readReg64 .x22 = b + futVtOff) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + bv% (ls_off% "__rustc::__rust_dealloc" - 0x3cbd8)) s
      (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xe6c 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_e80_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xf2c#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xe80 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem step_e80_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe88#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBin b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    libsignalSessionCode_fnOff_0x3cbd8 0x3cbd8 0xe80 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
