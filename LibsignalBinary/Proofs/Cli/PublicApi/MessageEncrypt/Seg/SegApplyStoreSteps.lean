/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreSteps
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreFetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# CLI `SegApplyStore` Basic-Block Steppers

`SepWP` basic-block stepping lemmas (`+0xd9c..+0xe88`) for `SegApplyStore` on `trTrapProgAt`.
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.otrApply_addr_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      (trTrapProgAt b C abs).fnAddr otrApplyName := by
  simp only [trTrapProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  have hfn : libsignalSessionCode.fnOff otrApplyName = 0xbcb0 := by
    simp only [otrApplyName, arm64_norm]
  rw [hfn]
  bv_omega


theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.otrApply_addr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr otrApplyName := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
  have hfn : libsignalSessionCode.fnOff otrApplyName = 0xbcb0 := by
    simp only [otrApplyName, arm64_norm]
  rw [hfn]
  bv_omega

set_option maxHeartbeats 1600000 in
/-- Apply step (`+0xd9c..+0xde4`): clear drop flag `[sp+0x469]`, copy the 200-byte OTR from
`sp+0x288` to `sp+0x580`, and call `OTR::apply_to_session_state`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_d9c_to_de4_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u469 : BitVec 8}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd9c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) s
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
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xde8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd9c 0x4c
  dsimp only [trTrapProgAt, otrWords25] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_d9c_to_de4 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd9c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::apply_to_session_state" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64)) s
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
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xde8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xd9c 0x4c
  dsimp only [tripleRatchetProgAt, otrWords25] at hpc ⊢
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store step 1 (`+0xd9c`/`+0xde8..+0xdf8`): load arguments from frame spills and call `storeSessionShim`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_de8_to_df8_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {remA ssA ss_vt shimOff : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64) :
    SepWP (trTrapProgAt b C abs) (b + shimOff) s
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
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xdfc#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xde8 0x14
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_de8_to_df8 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {remA ssA ss_vt shimOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xde8#64)
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
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xdfc#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xde8 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store step 2 (`+0xdfc..+0xe10`): store future box/vtable and call `storeSessionPoll`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_dfc_to_e10_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 futVtOff pollOff : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xdfc#64)
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
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe14#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xdfc 0x18
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_dfc_to_e10 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box u470 u478 futVtOff pollOff : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xdfc#64)
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
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe14#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xdfc 0x18
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store step 3 (`+0xe14..+0xe1c`, `+0xe38..+0xe68`): check `Ready`, copy SPE tail to `sp + 0x9b0`,
and call `futDrop`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e14_to_e68_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u9b0 u9b8 u9c0 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe14#64)
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
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe6c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := by simp [hdrop]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe14 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe38 0x34
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e14_to_e68 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box w0 w1 w2 w3 w4 w5 u9b0 u9b8 u9c0 futVtOff futDropOff : BitVec 64}
    (hdrop : b + futDropOff ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe14#64)
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
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe6c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (b + futDropOff == 0#64) = false := by simp [hdrop]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe14 0xc
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe38 0x34
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store step 4 (`+0xe6c..+0xe7c`): read size/alignment from the vtable and call `__rust_dealloc`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e6c_to_e7c_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe6c#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = box)
    (hx22 : s.readReg64 .x22 = b + futVtOff) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe6c 0x14
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e6c_to_e7c {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {box futVtOff boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe6c#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = box)
    (hx22 : s.readReg64 .x22 = b + futVtOff) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64)) s
      (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        P_f = (((b + (futVtOff + 8#64)) ↦₆₄ᵣ boxSizeBv) ∗ ((b + (futVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe6c 0x14
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  simp only [← BitVec.add_assoc]
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store `Err` branch (`+0xe80..+0xe84` when `x27 = 0x800000000000001A`): jump to `+0xf2c`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e80_err_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xf2c#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe80 0x8
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e80_err {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xf2c#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe80 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

/-- Store `Ok(())` branch (`+0xe80..+0xe84` when `x27 = 0xFFFFFFFFFFFFFFFE`): fall through to `+0xe88`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e80_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe88#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (trTrapExterns C abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe80 0x8
  dsimp only [trTrapProgAt, tripleRatchetProgAtExt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.step_e80_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe88#64) s emp
      (fun sf P_f =>
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  code_fetches_range CryptoVerification.libsignalSessionCode segApplyStoreBinCli b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") (ls_off% "libsignal_cli_ratchet::encrypt") 0xe80 0x8
  dsimp only [tripleRatchetProgAt] at hpc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry at *
  examples_hide_fetches
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨rfl, ?_⟩; simp_all)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
