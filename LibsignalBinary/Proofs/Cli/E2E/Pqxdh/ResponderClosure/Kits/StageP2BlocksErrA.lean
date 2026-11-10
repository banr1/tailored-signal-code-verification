/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P2 Basic Blocks — Shared Error Funnel and Arm 1

`SepWP` basic-block lemmas on `tripleRatchetProgAtExt b ext` for the shared 6-word
`SignalProtocolError` unwind funnel (`+0x1648 → +0x1698 → +0x1898 → +0x359c → retAddr`) and
Arm 1 (`get_signed_pre_key` error at `+0x0f38 → spkDropAddr → +0x1648`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local wp_norm, local arm64_norm]
  bfi_mask_lsr8_id evalBitfield_bfi_lsr8
attribute [local simp] extractLsb_hi_lo_append

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_dealloc")

theorem bfi_mask_lsr8_of_lo32 {r23 w1 : BitVec 64}
    (hlo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32) :
    (r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1 := by
  have hmask : ∀ x : BitVec 64, (x.extractLsb' 0 32).zeroExtend 64 &&& 255#64 = x &&& 255#64 := by
    intro x; clear * -; bv_bits
  have hrw : r23 &&& 255#64 = w1 &&& 255#64 := by rw [← hmask r23, hlo, hmask w1]
  rw [hrw]
  exact bfi_mask_lsr8_id w1

theorem evalBitfield_bfi_lsr8_of_lo32 {r23 w1 : BitVec 64}
    (hlo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32) :
    evalBitfield .W64 .BFM r23 (w1 >>> 8) 56 55 = w1 := by
  change (if (BitfieldOp.BFM == BitfieldOp.UBFM) = true then r23 >>> 8 <<< 8
      else r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1
  have h : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := rfl
  simp only [h]
  exact bfi_mask_lsr8_of_lo32 hlo

/-- Ext-generic lift of `drop_process_prekey_impl_state1_ok` (`[ptr + 0x15a] = 1#8` no-op drop). -/
theorem drop_process_prekey_impl_state1_ext_ok {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName)
      dropProcessPrekeyImplState1Spec := by
  unfold dropProcessPrekeyImplState1Spec
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hfn :
      libsignalSessionCode.fnOff
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName =
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") 0 368
  wp_init ptr s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

set_option maxHeartbeats 400000 in
/-- Segment P2.ErrTailA (`+0x1648 -> drop_process_prekey_impl_state1`) on `tripleRatchetProgAtExt`,
tracking all 6 `SignalProtocolError` words `(w0..w5)`. -/
theorem p2_err_tail_a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 : BitVec 64)
    (b_4f2 : BitVec 8)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w2 ∧
        s1.readReg64 .x23 = r23 ∧
        s1.readReg64 .x24 = w1 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond := p2_cond_ne_adds64_of_ne_neg3 herr_ne_neg3
  have htarget :
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) := by
    simp [tripleRatchetProgAtExt, Program.fnAddr,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName,
      ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>",
      ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]
  rw [htarget]
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1678 0x1694
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx10' : s.readReg64 (Reg.gpr 10#5) = w2 := hx10
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w4 >>> 8 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w1 >>> 32 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = r23 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = w2 >>> 32 := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * - hr23_lo; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- Segment P2.ErrTailB1 (`+0x1698 -> +0x1898`) on `tripleRatchetProgAtExt`, reconstructing the
exact 6-word `SignalProtocolError` `(w0, w1, w2, w3, w4, w5)` at `coroPtr + 0x250..0x280` and
`sp + 0xa90..0xac0`. -/
theorem p2_err_tail_b1_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 : BitVec 64)
    (b_390 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w2)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1898#64) s
      (((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x250#64) ↦₆₄ w0) ∗
          ((coroPtr + 0x258#64) ↦₆₄ w1) ∗
          ((coroPtr + 0x260#64) ↦₆₄ w2) ∗
          ((coroPtr + 0x268#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x270#64) ↦₆₄ w4) ∗
          ((coroPtr + 0x278#64) ↦₆₄ w5) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ w0) ∗
          ((s.sp + 0xa98#64) ↦₃₂ w1.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ w5.extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond := p2_cond_ne_adds64_of_ne_neg2 herr_ne_neg2
  have hcond' : ConditionHolds CondCode.NE (addsPState64 w0 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 herr_ne_neg2
  have hbfi_mask_r23 : (r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1 :=
    bfi_mask_lsr8_of_lo32 hr23_lo
  have hbfi_r23 : evalBitfield .W64 .BFM r23 (w1 >>> 8) 56 55 = w1 :=
    evalBitfield_bfi_lsr8_of_lo32 hr23_lo
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) w1 w2 w3 w4 w5
  try simp only [BitVec.add_assoc] at hrealign_a98; try simp only [BitVec.reduceAdd] at hrealign_a98
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1698 0x169c
  closure_fetches_range_cli b (Rust.withPanics ext) 0x16b4 0x16f4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x17b8 0x17d8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_logLevel_0x17bc_std3 hb hentry).1
  have hadrp := (adrp_logLevel_0x17bc_std3 hb hentry).2
  have h5b810 :
      (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    bv_arith
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w4 >>> 8 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w2 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = r23 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = w1 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  have hw3_hi : (w3 >>> 32).setWidth 32 = w3.extractLsb' 32 32 := by
    clear * -; bv_bits
  have hw3_lo : w3.setWidth 32 = w3.extractLsb' 0 32 := by
    clear * -; bv_bits
  wp_simp_pre [hbfi_r23, hbfi_mask_r23, hw3_hi, hw3_lo]
  apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr w3).symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  wp_simp_pre [hbfi_r23, hbfi_mask_r23]
  apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
/-- Segment P2.ErrTailB2 (`+0x1898 -> +0x359c`) on `tripleRatchetProgAtExt`. -/
theorem p2_err_tail_b2_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr
    v_a9c v_aa4 v_aac v_ab4
    u_370 u_378 u_380 u_388 : BitVec 64)
    (v_a98 v_abc u_390 : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1898#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
       ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
       ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗
       ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
       ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗
       ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
       ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗
          ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_a9c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0x380#64) ↦₆₄ v_aac) ∗
          ((s.sp + 0x388#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0x390#64) ↦₃₂ v_abc)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_a98.zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = errTag ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1898 0x18b4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3588 0x3594
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Folds the 48-byte epilogue stores at `outPtr + 0x0..0x30` into
`speWordsAt outPtr w0 w1 w2 w3 w4 w5`. -/
theorem speWordsAt_realign_outPtr (outPtr w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((outPtr + 0x0#64) ↦₆₄ w0) ∗
      ((outPtr + 0x8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
      ((outPtr + 0xc#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((outPtr + 0x14#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
      ((outPtr + 0x1c#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
      ((outPtr + 0x24#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
      ((outPtr + 0x2c#64) ↦₃₂ w5.extractLsb' 32 32) =
    speWordsAt outPtr w0 w1 w2 w3 w4 w5 := by
  have h40 := (realign_40 (outPtr + 8#64) w1 w2 w3 w4 w5).symm
  repeat (simp only [BitVec.add_assoc] at h40); repeat (simp only [BitVec.reduceAdd] at h40)
  dsimp only [speWordsAt]
  rw [BitVec.add_zero]
  rw [h40]

set_option maxHeartbeats 400000 in
/-- Segment P3.ErrTailB (`+0x359c -> retAddr`) on `tripleRatchetProgAtExt`. -/
theorem p3_err_tail_b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x359c 0x35a0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35d0 0x35d4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x35ec 0x362c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
/-- Segment P2.Err1a (`+0x0f38 -> spkDropAddr`) on `tripleRatchetProgAtExt`:
Reads `[sp + 0x3e0] = -1` and `[sp + 0x3e8..0x418]`, branches to `+0x0f54`, saves registers
and error payload words into `sp + 0x90..0xd0` and `x22, x23, x26`, loads `spkDropAddr` from
`[spkFutVt + 0x0]`, and calls `blr x8` at `+0x0f94`. -/
theorem p2_err1a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr errTag
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 u_410 u_418 : BitVec 64)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAtExt b ext) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 errTag u_3f0
         u_3f8 u_400 u_408 u_410 u_418 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 errTag u_3f0
            u_3f8 u_400 u_408 u_410 u_418 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ u_410) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_400)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = u_418 ∧
        s1.readReg64 .x21 = spkFutPtr ∧
        s1.readReg64 .x22 = errTag ∧
        s1.readReg64 .x23 = u_3f0 ∧
        s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = u_408 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdrop_beq : (spkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf38 0xf40
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf54 0xf94
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
/-- Segment P2.Err1b (`+0x0f98 -> +0x1648`, generic `spkBoxSize`) on `tripleRatchetProgAtExt`:
Deallocates `spkFutPtr` (`spkBoxSize` B), checks `x28 = -1`, branches at `+0x0fb0` to `+0x1344`,
loads and shifts all 6 `SignalProtocolError` words `(w0..w5)` into the common `+0x1648` register/stack
funnel, and jumps to `+0x1648`. -/
theorem p2_err1b_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr spkFutPtr spkFutVt outPtr
    w0 w1 w2 w4 w5 v_c0 u_a8 u_c0 : BitVec 64)
    (spkBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = w0)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = w4)
    (hx27 : s.readReg64 .x27 = v_c0)
    (hx28 : s.readReg64 .x28 = 0xffffffffffffffff#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x90#64) ↦₆₄ w5) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x90#64) ↦₆₄ w5) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ v_c0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x10 = w2 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = w2 >>> 32 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hbs_beq : (BitVec.ofNat 64 spkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 spkBoxSize).toNat = spkBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf98 0xfb0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1344 0x1370
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = spkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w0 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = w4 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = v_c0 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xffffffffffffffff#64 := hx28
  wp_steps
  wp_call hdealloc (spkFutPtr, spkBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p2_err1b_gen_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s : State) (coroPtr spkFutPtr spkFutVt outPtr
    w0 w1 w2 w4 w5 v_c0 u_a8 u_c0 : BitVec 64)
    (spkBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = w0)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = w4)
    (hx27 : s.readReg64 .x27 = v_c0)
    (hx28 : s.readReg64 .x28 = 0xffffffffffffffff#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x90#64) ↦₆₄ w5) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x90#64) ↦₆₄ w5) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ v_c0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x10 = w2 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = w2 >>> 32 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_err1b_hooks_wp b ext (.of_allocContracts hA) s coroPtr spkFutPtr spkFutVt outPtr
    w0 w1 w2 w4 w5 v_c0 u_a8 u_c0 spkBoxSize hbs_nz hbs_lt hpc hrun hsp_align
    hx19 hx21 hx22 hx23 hx24 hx26 hx27 hx28

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

