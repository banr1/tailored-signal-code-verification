/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustSteps
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Basic-Block Step Lemmas for `segTrust` (`+0xa70..+0xd40`)

Proves `SepWP` basic-block stepping lemmas (in normal and trap modes) for the `is_trusted_identity`
shim/poll/cleanup blocks and the `UntrustedIdentity` branch.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust

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

/-- E7 part 1 (`+0xa70..+0xa84`): load arguments from frame spills and call `isTrustedShim` (`b + shimOff`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_a70_to_a84_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {remA idA id_vt shimOff : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa70#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (trTrapProgAt b C abs) (b + shimOff) s
      (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
       ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
       ((id_vt + 0x30#64) ↦₆₄ᵣ (b + shimOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
          ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
          ((id_vt + 0x30#64) ↦₆₄ᵣ (b + shimOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = idA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x350#64 ∧ sf.readReg64 .x3 = 0#64 ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa88#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xa70 0x18
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_a70_to_a84 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {remA idA id_vt shimOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa70#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAt b C ctl abs) (b + shimOff) s
      (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
       ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
       ((id_vt + 0x30#64) ↦₆₄ᵣ (b + shimOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
          ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
          ((id_vt + 0x30#64) ↦₆₄ᵣ (b + shimOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = idA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x350#64 ∧ sf.readReg64 .x3 = 0#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa88#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xa70 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E7 part 2 (`+0xa88..+0xa9c`): store future box/vtable and call `isTrustedPoll` (`b + pollOff`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_a88_to_a9c_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 futVtOff pollOff : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa88#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = b + futVtOff) :
    SepWP (trTrapProgAt b C abs) (b + pollOff) s
      (((s.sp + 0x470#64) ↦₆₄ u470) ∗
       ((s.sp + 0x478#64) ↦₆₄ u478) ∗
       ((b + (futVtOff + 0x18#64)) ↦₆₄ᵣ (b + pollOff)))
      (fun sf P_f =>
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
          ((b + (futVtOff + 0x18#64)) ↦₆₄ᵣ (b + pollOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = s.sp + 0x480#64 ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xaa0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xa88 0x18
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_a88_to_a9c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 futVtOff pollOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xa88#64)
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
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xaa0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xa88 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E7 + E7r part 1 (`+0xaa0..+0xaa8`, `+0xb7c..+0xbac`): check `Ready`, copy SPE tail to `sp + 0x970`,
and call `futDrop` (`b + futDropOff`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_aa0_to_bac_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u970 u978 u980 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xaa0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hw0 : w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) :
    SepWP (trTrapProgAt b C abs) (b + futDropOff) s
      (((s.sp + 0x470#64) ↦₆₄ box) ∗
       ((s.sp + 0x478#64) ↦₆₄ (b + futVtOff)) ∗
       ((s.sp + 0x580#64) ↦₆₄ w0) ∗
       ((s.sp + 0x588#64) ↦₆₄ w1) ∗
       ((s.sp + 0x590#64) ↦₆₄ w2) ∗
       ((s.sp + 0x598#64) ↦₆₄ w3) ∗
       ((s.sp + 0x5a0#64) ↦₆₄ w4) ∗
       ((s.sp + 0x5a8#64) ↦₆₄ w5) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗
       ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗
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
          ((s.sp + 0x970#64) ↦₆₄ w3) ∗
          ((s.sp + 0x978#64) ↦₆₄ w4) ∗
          ((s.sp + 0x980#64) ↦₆₄ w5) ∗
          ((b + futVtOff) ↦₆₄ᵣ (b + futDropOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = b + futVtOff ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x24 = box ∧ sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbb0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := by simp [hdrop]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xaa0 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xb7c 0x34
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_aa0_to_bac {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u970 u978 u980 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xaa0#64)
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
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗
       ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗
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
          ((s.sp + 0x970#64) ↦₆₄ w3) ∗
          ((s.sp + 0x978#64) ↦₆₄ w4) ∗
          ((s.sp + 0x980#64) ↦₆₄ w5) ∗
          ((b + futVtOff) ↦₆₄ᵣ (b + futDropOff))) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = b + futVtOff ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x24 = box ∧ sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbb0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := by simp [hdrop]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xaa0 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xb7c 0x34
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E7r part 2 (`+0xbb0..+0xbc0`): read size/align from vtable and call `__rust_dealloc` (`entry + 46140`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bb0_to_bc0_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbb0#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = b + futVtOff)
    (hx24 : s.readReg64 .x24 = box) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbb0 0x14
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bb0_to_bc0 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbb0#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = b + futVtOff)
    (hx24 : s.readReg64 .x24 = box) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbb0 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E7r `Err` branch (`+0xbc4..+0xbc8` when `x27 = 0x800000000000001A`): jump to T5 store `+0xc20`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_err_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xc20#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x8
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xc20#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E7r `Ok(true)` branch (`+0xbc4..+0xbd0`): fall through to `+0xbd4` (`SaveState`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_ok_true_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {w1 : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 1#8) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbd4#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.sp + 0x8b8#64 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8 hw1
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x10
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_ok_true {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {w1 : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 1#8) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbd4#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.sp + 0x8b8#64 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8 hw1
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x10
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.adrp_3192_eq_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    ((((libsignalSessionCode.rebase b
          (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 3192#64 &&&
        18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 3192)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"),
    BitVec.add_assoc b, adrp_page_of_aligned hb, BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.adrp_3192_eq {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    ((((libsignalSessionCode.rebase b
          (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 3192#64 &&&
        18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - (page% (ls_off% "libsignal_cli_ratchet::encrypt" + 3192)))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt"),
    BitVec.add_assoc b, adrp_page_of_aligned hb, BitVec.add_assoc, BitVec.add_assoc]
  rfl

/-- E7r `Ok(false)` + E9 part 1 (`+0xbc4..+0xbd0`, `+0xc78..+0xc84`, `+0xd0c..+0xd18`):
branch on `tbz`, skip log block via `logOff`, and call `String::clone` (`entry + 46248`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_ok_false_to_d18_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {w1 remA : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 0#8) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
      (fun sf P_f =>
        P_f = (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x21 = remA ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd1c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8 hw1
  have hadrp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.adrp_3192_eq_trap (C := C) (abs := abs) hb
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xc78 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd0c 0x10
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_bc4_ok_false_to_d18 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {w1 remA : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xbc4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 0#8) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<alloc::string::String as core::clone::Clone>::clone" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
      (fun sf P_f =>
        P_f = (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x21 = remA ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd1c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8 hw1
  have hadrp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.adrp_3192_eq (C := C) (ctl := ctl) (abs := abs) hb
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xbc4 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xc78 0x10
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd0c 0x10
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E9 part 2a (`+0xd1c..+0xd28`): read `device` byte from `remA + 0x18`, `cap`/`ptr` from `sp + 0x580`,
and store `device` byte at `sp + 0x598`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_d1c_to_d2c_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {remA cap ptr : BitVec 64} {dev b598 : BitVec 8}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = remA) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd2c#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
       ((s.sp + 0x580#64) ↦₆₄ cap) ∗
       ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x598#64) ↦₈ b598))
      (fun sf P_f =>
        P_f = (((remA + 0x18#64) ↦₈ dev) ∗
          ((s.sp + 0x580#64) ↦₆₄ cap) ∗
          ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x598#64) ↦₈ dev)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x21 = cap ∧ sf.readReg64 .x23 = ptr ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd1c 0x10
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_d1c_to_d2c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {remA cap ptr : BitVec 64} {dev b598 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = remA) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd2c#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
       ((s.sp + 0x580#64) ↦₆₄ cap) ∗
       ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x598#64) ↦₈ b598))
      (fun sf P_f =>
        P_f = (((remA + 0x18#64) ↦₈ dev) ∗
          ((s.sp + 0x580#64) ↦₆₄ cap) ∗
          ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x598#64) ↦₈ dev)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x21 = cap ∧ sf.readReg64 .x23 = ptr ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd1c 0x10
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- E9 part 2b (`+0xd2c..+0xd3c`): set `x27 = speWord 12` and copy `[len, devWord]` from `sp + 0x590`
to `sp + 0x9d0`, reaching `+0xd40` (`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailCmDrop_ok`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_d2c_to_d40_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {len devWord u9d0 u9d8 : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd2c#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x9d0#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd40#64) s
      (((s.sp + 0x590#64) ↦₆₄ len) ∗
       ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
       ((s.sp + 0x9d0#64) ↦₆₄ u9d0) ∗
       ((s.sp + 0x9d8#64) ↦₆₄ u9d8))
      (fun sf P_f =>
        P_f = (((s.sp + 0x590#64) ↦₆₄ len) ∗
          ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9d0#64) ↦₆₄ len) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x27 = speWord 12 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd2c 0x14
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt, speWord] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.step_d2c_to_d40 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {len devWord u9d0 u9d8 : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd2c#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x9d0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd40#64) s
      (((s.sp + 0x590#64) ↦₆₄ len) ∗
       ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
       ((s.sp + 0x9d0#64) ↦₆₄ u9d0) ∗
       ((s.sp + 0x9d8#64) ↦₆₄ u9d8))
      (fun sf P_f =>
        P_f = (((s.sp + 0x590#64) ↦₆₄ len) ∗
          ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9d0#64) ↦₆₄ len) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x27 = speWord 12 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segTrustBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd2c 0x14
  dsimp only [tripleRatchetProgAt, speWord] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
