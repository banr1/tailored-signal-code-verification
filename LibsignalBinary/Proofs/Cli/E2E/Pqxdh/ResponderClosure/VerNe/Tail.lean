/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.PrevBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ErrK2
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch Error Tail (`+0x2cfc → s0.readReg64 .x30`)

Proves `over_ver_ne_tail_2cfc_cli_4k_ok` and `over_ver_ne_tail_2cfc_cli_ok` on
`tripleRatchetProgAtExt` when `errs` holds two `UnrecognizedMessageVersion` entries
(`errs.len = 2#64`, `errs.cap = 4#64`) and `previous_sessions` holds one archived session: allocates
the 17-byte `"decryption failed"` message, drops both error entries and `current_session`, and runs
the K2 `previous_sessions` epilogue to return.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")

private gen_decodes libsignalSessionCode_tree verNeTailCliDec [
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x2cfc) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x2d14),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x307c) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3098),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x32bc) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x32c0),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x33a4) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3420),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3500) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3534),
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3570) →
  (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 0x3598)]

local macro "verNeTail_fetches_range " b:term:max H:term:max lo:num hi:num : tactic => do
  let s := lo.getNat
  let l := Lean.Syntax.mkNumLit (toString (hi.getNat - s + 4))
  `(tactic| code_fetches_range libsignalSessionCode verNeTailCliDec $b $H
    (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") $lo $l)

/-! ## Basic blocks (`+0x2cfc → +0x33b0`, `+0x33b4 → dropSpe2`, `+0x3410` loop and exit) -/

private theorem cond_eq_adds64_of_ne_neg1_tail {w : BitVec 64} (h : w ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 w 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; revert h; bv_omega

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_2cfc_33b0_cli_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr retPtr savedX27 ssCap : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x33b0#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := closure_shim_ok_of_mem4k hA
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail hcap_ne
  verNeTail_fetches_range b (Rust.withPanics ext) 0x2cfc 0x2d14
  verNeTail_fetches_range b (Rust.withPanics ext) 0x307c 0x3098
  verNeTail_fetches_range b (Rust.withPanics ext) 0x32bc 0x32c0
  verNeTail_fetches_range b (Rust.withPanics ext) 0x33a4 0x33ac
  dsimp only [tripleRatchetProgAtExt] at hshim hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_logLevel_verD hb hentry).1
  have hadrp := (adrp_closure_logLevel_verD hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hlog : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_33b4_dropspe_cli_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr errsPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x33b4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
       ((dfPtr + 0x0#64) ↦₆₄ u_df0) ∗
       ((dfPtr + 0x8#64) ↦₆₄ u_df8) ∗
       ((dfPtr + 0x10#64) ↦₈ u_df10) ∗
       ((s.sp + 0x270#64) ↦₆₄ u_270) ∗
       ((s.sp + 0x278#64) ↦₆₄ u_278) ∗
       ((s.sp + 0x280#64) ↦₆₄ u_280) ∗
       ((s.sp + 0x288#64) ↦₆₄ u_288) ∗
       ((s.sp + 0x290#64) ↦₈ u_290))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ ro0) ∗
          ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ ro1) ∗
          ((dfPtr + 0x0#64) ↦₆₄ ro0) ∗
          ((dfPtr + 0x8#64) ↦₆₄ ro1) ∗
          ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
          ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
          ((s.sp + 0x290#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 2#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  verNeTail_fetches_range b (Rust.withPanics ext) 0x33b4 0x340c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_rodata_verE hb hentry).1
  have hadrp := (adrp_closure_rodata_verE hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x340c#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13324)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = dfPtr := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hro0 : (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) % 4096) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) := by bv_arith
  have hro1 : (b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) + 8#64 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8) := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 600000 in
private theorem p3_ver_ne_3410_loop_cli_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x3410#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr)
    (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 2#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr + 0x30#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr + 0x30#64 ∧
        s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x3410#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  verNeTail_fetches_range b (Rust.withPanics ext) 0x3408 0x3420
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x340c#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13324)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 2#64 := hx23
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
private theorem p3_ver_ne_3410_exit_cli_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x3410#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = errsPtr)
    (hx23 : s.readReg64 .x23 = 1#64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       A.live errsPtr 192 8 ∗
       memRegion errsPtr 192 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
       ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗
       ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
          ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := closure_dealloc_ok_of_mem4k hA
  have hcond_cap := cond_eq_adds64_of_ne_neg1_tail hcap_ne
  verNeTail_fetches_range b (Rust.withPanics ext) 0x3410 0x341c
  verNeTail_fetches_range b (Rust.withPanics ext) 0x3500 0x3534
  verNeTail_fetches_range b (Rust.withPanics ext) 0x3570 0x3598
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x3598#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13720)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = errsPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000018#64 := hx28
  wp_steps
  wp_call hdealloc (errsPtr, 192, 8)
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## Framing helpers and Part A (`+0x2cfc → +0x3410`) -/

private theorem call_frame_inImage_nopanic_tail {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine P3P4.SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]; rw [hspec, pure_sepConj_pure_assoc]

private theorem errs48_48_96_join_tail (errsPtr : BitVec 64) :
    memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
      memRegion errsPtr 192 := by
  have h1 :
      memRegion (errsPtr + 0x30#64) 48 ∗ memRegion (errsPtr + 0x60#64) 96 =
        memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr + 0x30#64) (n := 48) (k := 96)
          (b' := errsPtr + 0x60#64) rfl (by bv_omega) (by decide)]
  rw [h1, ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
        (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]

set_option maxHeartbeats 1000000 in
private theorem over_ver_ne_tail_partA_cli_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF7 : img.FrozenLoaded s7) (hsym7 : s7.symtab = img.symtab)
    (hpc7 : s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64)
    (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace)
    (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3410#64) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗
       ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
       memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       logOff img ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun s11 P_f =>
        (∃ dfPtr w3' w4 : BitVec 64,
          dfPtr ≠ 0#64 ∧
          w3'.extractLsb' 0 8 = 3#8 ∧
          (P_f ⊢
            ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
            memRegion errsPtr 192 ∗
            A.live dfPtr 17 1 ∗
            ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
            ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
            ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
            ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
            ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
            ((s.sp + 0x290#64) ↦₆₄ w3') ∗
            ((s.sp + 0x298#64) ↦₆₄ w4) ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
            logOff img ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack)) ∧
        s11.sp = s.sp ∧
        s11.trace = s0.trace ∧
        s11.readReg64 .x19 = coroPtr ∧
        s11.readReg64 .x22 = errsPtr ∧
        s11.readReg64 .x23 = 1#64 ∧
        s11.readReg64 .x24 = s.sp + 0x370#64 ∧
        s11.readReg64 .x25 = s.sp + 0x210#64 ∧
        s11.readReg64 .x26 = outPtr ∧
        s11.readReg64 .x27 = ctxPtr ∧
        s11.readReg64 .x28 = 0x8000000000000018#64 ∧
        calleeSavedVRegs s11 = calleeSavedVRegs s7 ∧
        img.FrozenLoaded s11 ∧
        s11.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hs7_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hlog_eq : logOff img =
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  rw [hlog_eq]
  have hstep7b := p3_ver_ne_2cfc_33b0_cli_wp img.base ext hA s7 coroPtr outPtr ctxPtr recG.localIk.cap
    hb_align (cap_ne_noneCap_of_lt hcap_lt) hpc7 hrun7 hsp7_align hx19_7
  rw [hs7_sp] at hstep7b
  refine P3P4.SepWPp.bind_sepWP_frame hF7 hsym7 hstep7b (by sep_focus)
    fun s7b hpc7b hrun7b hF7b hsym7b hregs7b => ?_
  rcases hregs7b with ⟨hsp7b, htr7b, hx0_7b, hx1_7b, hx19_7b, hx24_7b, hx25_7b,
    hx26_7b, hx27_7b, _, hvregs_7b⟩
  have hpack_ss7b :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss7b (by sep_focus) ?_
  rw [← hlog_eq]
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp7b_align : (s7b.sp &&& 15#64 == 0#64) = true := by rw [hsp7b]; exact hsp_align
  have htr7b_0 : s7b.trace = s0.trace := htr7b.trans htr7
  have halloc17 := p3_alloc_33b0_mem4k_ok (A := A) img img.base ext hA s0 s7b
    emp hF7b hsym7b hpc7b hrun7b hsp7b_align htr7b_0 hx0_7b hx1_7b
  rw [sepConj_emp, hsp7b] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw
    halloc17 (by sep_focus)
    fun s8 P_m8 hpc8 hrun8 ⟨hP8, hdf_ne, hsp8_7b, htr8_7b, hcs8, hF8, hsym8⟩ => ?_
  rw [sepConj_emp] at hP8
  refine P3P4.SepWPp.weaken_frame hP8 (by sep_focus) ?_
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion_17_split_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_df10 => SepWPp.exists_elim fun u_df8 =>
    SepWPp.exists_elim fun u_df0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x270#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_270 => SepWPp.exists_elim fun u_278 =>
    SepWPp.exists_elim fun u_280 => SepWPp.exists_elim fun u_288 =>
    SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7b
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, hx27_cs8, _, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7b
  have hx24_8 : s8.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs8.trans hx24_7b
  have hx25_8 : s8.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs8.trans hx25_7b
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans hx26_7b
  have hx27_8 : s8.readReg64 .x27 = ctxPtr := hx27_cs8.trans hx27_7b
  refine P3P4.SepWPp.intro_rodata_decryptionFailed himg hF8 ?_
  have hstep9 := p3_ver_ne_33b4_dropspe_cli_wp img.base ext s8 coroPtr (s8.readReg64 .x0) errsPtr
    0x6974707972636564#64 0x656c696166206e6f#64
    u_df0 u_df8 u_270 u_278 u_280 u_288 u_df10 (w3.extractLsb' 0 8)
    hb_align hdf_ne hpc8 hrun8 hsp8_align rfl hx19_8
  rw [hsp8_s] at hstep9
  refine P3P4.SepWPp.bind_sepWP_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx24_9, hx25_9, hx26_9, hx27_9, hx28_9, _, hx30_9, hvregs_9⟩
  refine SepWPp.drop_frame
    (P_drop := ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hsp9_s : s9.sp = s.sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9_s] using hsp_align
  have hstack_spe :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 480 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_spe) (by sep_focus) ?_
  refine call_frame_inImage_nopanic_tail
    (spec := dropSpeVerSpec A)
    (x := (errsPtr, msgVer0))
    (φ := s9.readReg64 .x0 = errsPtr)
    (T := (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
          memRegion (errsPtr + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF9 hsym9 (drop_spe2_ver_ok_ext (A := A) (img := img) (ext := ext) himg)
    hpc9 hrun9 hsp9_al hx30_9
    (by dsimp only [dropSpeVerSpec]; rw [hsp9_s])
    hx0_9
    (by sep_focus)
    (hnext := fun s10 hpc10 hrun10 hsp10_9 _ hcs10 hF10 hsym10 => ?_)
  dsimp only [dropSpeVerSpec]
  rw [hsp9_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr10_9 => ?_
  have hsp10_s : s10.sp = s.sp := hsp10_9.trans hsp9_s
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10_s]; exact hsp_align
  rcases hcs10 with ⟨hx19_cs10, _, hx21_cs10, hx22_cs10, hx23_cs10, hx24_cs10, hx25_cs10,
    hx26_cs10, hx27_cs10, hx28_cs10, _, hvregs_cs10⟩
  have hx19_10 : s10.readReg64 .x19 = coroPtr := hx19_cs10.trans hx19_9
  have hx21_10 : s10.readReg64 .x21 = errsPtr := hx21_cs10.trans hx21_9
  have hx22_10 : s10.readReg64 .x22 = errsPtr := hx22_cs10.trans hx22_9
  have hx23_10 : s10.readReg64 .x23 = 2#64 := hx23_cs10.trans hx23_9
  have hloop := p3_ver_ne_3410_loop_cli_wp img.base ext s10 coroPtr errsPtr
    hpc10 hrun10 hsp10_align hx19_10 hx21_10 hx22_10 hx23_10
  refine P3P4.SepWPp.bind_sepWP_frame hF10 hsym10 hloop (emp_sepConj _).symm
    fun s10b hpc10b hrun10b hF10b hsym10b hregs10b => ?_
  rw [emp_sepConj]
  rcases hregs10b with ⟨hsp10b_10, htr10b_10, hx0_10b, hx19_10b, _, hx22_10b, hx23_10b,
    hx24_10b, hx25_10b, hx26_10b, hx27_10b, hx28_10b, _, hx30_10b, hvregs_10b⟩
  have hsp10b_s : s10b.sp = s.sp := hsp10b_10.trans hsp10_s
  have hsp10b_al : s10b.spAligned = true := by simpa only [State.spAligned, hsp10b_s] using hsp_align
  have herrs_off :
      ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
      ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
      memRegion (errsPtr + 60#64) 36 =
      ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
      (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
      memRegion ((errsPtr + 0x30#64) + 12#64) 36 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq herrs_off) (by sep_focus) ?_
  refine call_frame_inImage_nopanic_tail
    (spec := dropSpeVerSpec A)
    (x := (errsPtr + 0x30#64, msgVer1))
    (φ := s10b.readReg64 .x0 = errsPtr + 0x30#64)
    (T := ((errsPtr + 0x30#64) ↦₆₄ 0x8000000000000006#64) ∗
          (((errsPtr + 0x30#64) + 8#64) ↦₃₂ msgVer1) ∗
          memRegion ((errsPtr + 0x30#64) + 12#64) 36 ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF10b hsym10b (drop_spe2_ver_ok_ext (A := A) (img := img) (ext := ext) himg)
    hpc10b hrun10b hsp10b_al hx30_10b
    (by dsimp only [dropSpeVerSpec]; rw [hsp10b_s])
    hx0_10b
    (by sep_focus)
    (hnext := fun s11 hpc11 hrun11 hsp11_10b _ hcs11 hF11 hsym11 => ?_)
  dsimp only [dropSpeVerSpec]
  rw [hsp10b_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr11_10b => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs48_48_96_join_tail errsPtr)) (by sep_focus) ?_
  have hstack_restore11 :
      memRegion (s.sp - 4608#64) 480 ∗ stackAt s.sp dropSpeStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_spe]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore11 (by sep_focus) ?_
  rcases hcs11 with ⟨hx19_cs11, _, _, hx22_cs11, hx23_cs11, hx24_cs11, hx25_cs11,
    hx26_cs11, hx27_cs11, hx28_cs11, _, hvregs_cs11⟩
  have hsp11_s : s11.sp = s.sp := hsp11_10b.trans hsp10b_s
  have htr11_0 : s11.trace = s0.trace :=
    htr11_10b.trans (htr10b_10.trans (htr10_9.trans (htr9_8.trans (htr8_7b.trans htr7b_0))))
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10b
  have hx22_11 : s11.readReg64 .x22 = errsPtr := hx22_cs11.trans hx22_10b
  have hx23_11 : s11.readReg64 .x23 = 1#64 := hx23_cs11.trans hx23_10b
  have hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64 :=
    hx24_cs11.trans (hx24_10b.trans (hx24_cs10.trans (hx24_9.trans hx24_8)))
  have hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64 :=
    hx25_cs11.trans (hx25_10b.trans (hx25_cs10.trans (hx25_9.trans hx25_8)))
  have hx26_11 : s11.readReg64 .x26 = outPtr :=
    hx26_cs11.trans (hx26_10b.trans (hx26_cs10.trans (hx26_9.trans hx26_8)))
  have hx27_11 : s11.readReg64 .x27 = ctxPtr :=
    hx27_cs11.trans (hx27_10b.trans (hx27_cs10.trans (hx27_9.trans hx27_8)))
  have hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64 :=
    hx28_cs11.trans (hx28_10b.trans (hx28_cs10.trans hx28_9))
  have hvregs_11_7 : calleeSavedVRegs s11 = calleeSavedVRegs s7 := by
    rw [hvregs_cs11, hvregs_10b, hvregs_cs10, hvregs_9, hvregs_cs8, hvregs_7b]
  refine SepWPp.done hpc11 hrun11 ?_
  refine ⟨⟨s8.readReg64 .x0, w3', w4, hdf_ne, hw3'_head, Entails.of_eq (by ac_rfl)⟩,
    hsp11_s, htr11_0, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, hx27_11, hx28_11,
    hvregs_11_7, hF11, hsym11⟩

/-! ## Part B (`+0x3410 → s0.readReg64 .x30`) and combined tail theorems -/

set_option maxHeartbeats 1000000 in
private theorem over_ver_ne_tail_partB_cli_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s11 : State) (coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hdf_ne : dfPtr ≠ 0#64)
    (hw3'_head : w3'.extractLsb' 0 8 = 3#8)
    (hF11 : img.FrozenLoaded s11) (hsym11 : s11.symtab = img.symtab)
    (hpc11 : s11.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3410#64)
    (hrun11 : s11.status = .Running)
    (hs11_sp : s11.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr11 : s11.trace = s0.trace)
    (hx19_11 : s11.readReg64 .x19 = coroPtr)
    (hx22_11 : s11.readReg64 .x22 = errsPtr)
    (hx23_11 : s11.readReg64 .x23 = 1#64)
    (hx24_11 : s11.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_11 : s11.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_11 : s11.readReg64 .x26 = outPtr)
    (hx28_11 : s11.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s11
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       A.live errsPtr 192 8 ∗
       memRegion errsPtr 192 ∗
       A.live dfPtr 17 1 ∗
       ((dfPtr + 0x0#64) ↦₆₄ 0x6974707972636564#64) ∗
       ((dfPtr + 0x8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
       ((dfPtr + 0x10#64) ↦₈ 0x64#8) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x280#64) ↦₆₄ dfPtr) ∗
       ((s.sp + 0x288#64) ↦₆₄ 17#64) ∗
       ((s.sp + 0x290#64) ↦₆₄ w3') ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s11)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr dfPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG st) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG st (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) 17#64 dfPtr 17#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hs11_sp]; exact hsp_align
  have hx24_11' : s11.readReg64 .x24 = s11.sp + 0x370#64 := by rw [hx24_11, hs11_sp]
  have hx25_11' : s11.readReg64 .x25 = s11.sp + 0x210#64 := by rw [hx25_11, hs11_sp]
  have hstep12 := p3_ver_ne_3410_exit_cli_wp img.base ext hA s11 coroPtr errsPtr recG.localIk.cap
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    w3' w4 u_250 u_258 u_370 u_378 u_384 u_38c
    ((17#64 : BitVec 64).extractLsb' 0 32) ((17#64 : BitVec 64).extractLsb' 32 32)
    u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc11 hrun11 hsp11_align
    hx19_11 hx22_11 hx23_11 hx24_11' hx25_11' hx28_11
  rw [hs11_sp] at hstep12
  refine P3P4.SepWPp.bind_sepWP_frame hF11 hsym11 hstep12 (by sep_focus)
    fun s12 hpc12 hrun12 hF12 hsym12 hregs12 => ?_
  rcases hregs12 with ⟨hsp12_11, htr12_11, hx0_12, hx19_12, hx22_12, _, hx25_12,
    hx26_12, _, hx28_12, _, hx30_12, hvregs_12⟩
  have hstack_restore8 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore8 (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG st ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG st := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG st hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64)
      0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ (17#64 : BitVec 64).extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
        ((17#64 : BitVec 64).extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  have hsp12_s : s12.sp = s.sp := hsp12_11
  have hsp12_al : s12.spAligned = true := by simpa only [State.spAligned, hsp12_s] using hsp_align
  have hdropSs3 := drop_session_structure3_ok_of_mem4k (b := img.base) (ext := ext) hA
  have hpc12_drop : s12.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc12, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, recG, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF12 hsym12 hdropSs3 hpc12_drop hrun12 hsp12_al hx30_12
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp12_s])
    hx0_12 (by sep_focus)
    (hnext := fun s13 hpc13 hrun13 hsp13_12 _ hcs13 hF13 hsym13 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp12_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr13_12 => ?_
  have hstack_k2 :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_k2) (by sep_focus) ?_
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hsp13_s : s13.sp = s.sp := hsp13_12.trans hsp12_s
  have hsp13_align : (s13.sp &&& 15#64 == 0#64) = true := by rw [hsp13_s]; exact hsp_align
  rcases hcs13 with ⟨hx19_cs13, _, _, hx22_cs13, _, _, hx25_cs13, hx26_cs13, _, hx28_cs13, _, hvregs_cs13⟩
  have hx19_13 : s13.readReg64 .x19 = coroPtr := hx19_cs13.trans hx19_12
  have hx22_13 : s13.readReg64 .x22 = ((17#64 : BitVec 64).extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs13.trans hx22_12
  have hx25_13 : s13.readReg64 .x25 = s13.sp + 0x210#64 := by rw [hx25_cs13, hx25_12, hsp13_s]
  have hx26_13 : s13.readReg64 .x26 = outPtr := hx26_cs13.trans (hx26_12.trans hx26_11)
  have hx28_13 : s13.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs13.trans hx28_12
  have hk2 := overK2Seg_cli_4k_ok img ext hA s13 coroPtr outPtr 0x8000000000000018#64
    prevCap prevPtr
    (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
    (w3'.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3'.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    ((17#64 : BitVec 64).extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0 enc
    hpc13 hrun13 hsp13_align hx19_13 hx22_13 hx25_13 hx26_13 hx28_13
  rw [hsp13_s] at hk2
  refine P3P4.SepWPp.bind_sepWP_frame hF13 hsym13 hk2 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_13, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregs_f⟩
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_36_err_fold s.sp
      (dfPtr.extractLsb' 0 32 ++ (17#64 : BitVec 64).extractLsb' 32 32)
      ((17#64 : BitVec 64).extractLsb' 0 32 ++ dfPtr.extractLsb' 32 32)
      w3' w4 ((17#64 : BitVec 64).extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    ((17#64 : BitVec 64).extractLsb' 32 32) w3' w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) 17#64 dfPtr 17#64).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗ ((outPtr + 0x8#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x10#64) ↦₆₄ dfPtr) ∗ ((outPtr + 0x18#64) ↦₆₄ 17#64) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3') ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr 0x8000000000000018#64 17#64 dfPtr 17#64 w3' w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr dfPtr w3' w4 hdf_ne hw3'_head
  refine P3P4.SepWPp.weaken_frame hrec (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_k2.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2.symm) (by sep_focus) ?_
  have htrf_0 : sf.trace = s0.trace :=
    htrf_13.trans (htr13_12.trans (htr12_11.trans htr11))
  have hvregsf_11 : calleeSavedVRegs sf = calleeSavedVRegs s11 := by
    rw [hvregs_f, hvregs_cs13, hvregs_12]
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨Entails.of_eq (by ac_rfl), hspf_s, htrf_0,
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
    hFf, hsymf, hvregsf_11⟩

set_option maxHeartbeats 600000 in
/-- Version-mismatch error tail (`+0x2cfc → s0.readReg64 .x30` with `errs.len = 2`) under `AllocContractsMem4K`. -/
theorem over_ver_ne_tail_2cfc_cli_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF7 : img.FrozenLoaded s7) (hsym7 : s7.symtab = img.symtab)
    (hpc7 : s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64)
    (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace)
    (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗
       ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
       memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗
       A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       logOff img ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          logOff img ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0) := by
  have hpartA := over_ver_ne_tail_partA_cli_ok img ext himg hA
    s0 s s7 coroPtr ctxPtr outPtr errsPtr msgVer0 msgVer1 recG st
    hF7 hsym7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7
  refine SepWPp.bind_sepWPp_frame_raw hpartA (by sep_focus)
    fun s11 P_m11 hpc11 hrun11
      ⟨⟨dfPtr, w3', w4, hdf_ne, hw3'_head, hP11⟩,
       hs11_sp, htr11, hx19_11, hx22_11, hx23_11, hx24_11, hx25_11, hx26_11, _, hx28_11,
       hvregs_11, hF11, hsym11⟩ => ?_
  refine SepWPp.weaken_pre (sepConj_mono_left hP11) ?_
  have hpartB := over_ver_ne_tail_partB_cli_ok img ext hA
    s0 s s11 coroPtr outPtr errsPtr prevCap prevPtr dfPtr w3' w4 b_2c0 enc recG st
    hdf_ne hw3'_head hF11 hsym11 hpc11 hrun11 hs11_sp hsp_align htr11
    hx19_11 hx22_11 hx23_11 hx24_11 hx25_11 hx26_11 hx28_11
  refine P3P4.SepWPp.ret_sepWPp_frame hpartB (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (by ac_rfl), hspf, htrf, hcc, hFf, hsymf, hvregs_f.trans hvregs_11⟩

theorem over_ver_ne_tail_2cfc_cli_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (s0 s s7 : State) (coroPtr ctxPtr outPtr errsPtr prevCap prevPtr : BitVec 64)
    (msgVer0 msgVer1 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF7 : img.FrozenLoaded s7) (hsym7 : s7.symtab = img.symtab)
    (hpc7 : s7.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x2cfc#64)
    (hrun7 : s7.status = .Running)
    (hs7_sp : s7.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr7 : s7.trace = s0.trace)
    (hx19_7 : s7.readReg64 .x19 = coroPtr) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s7
      (((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 8#64) ↦₃₂ msgVer0) ∗
       memRegion (errsPtr + 12#64) 36 ∗
       ((errsPtr + 48#64) ↦₆₄ 0x8000000000000006#64) ∗
       ((errsPtr + 56#64) ↦₃₂ msgVer1) ∗
       memRegion (errsPtr + 60#64) 36 ∗
       memRegion (errsPtr + 96#64) 96 ∗
       A.live errsPtr 192 8 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       logOff img ∗
       memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗
       memRegion (s.sp + 0x270#64) 48 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 2#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          logOff img ∗
          recordResultAt A outPtr (.error (.invalidMessage .preKey .decryptionFailed)) ∗
          memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp growOneSpeStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧
        ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s7)
      (P3P4.PanicOomProp s0) :=
  over_ver_ne_tail_2cfc_cli_4k_ok img ext himg (.of_AllocContracts hA)
    s0 s s7 coroPtr ctxPtr outPtr errsPtr prevCap prevPtr msgVer0 msgVer1 b_2c0 enc recG st
    hF7 hsym7 hpc7 hrun7 hs7_sp hsp_align htr7 hx19_7

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
