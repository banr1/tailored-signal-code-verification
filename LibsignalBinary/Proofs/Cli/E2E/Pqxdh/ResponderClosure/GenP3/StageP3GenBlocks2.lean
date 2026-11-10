/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClosureStubs4K
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
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
# Stage P3 Error-Tail and Version-Mismatch Basic Blocks

Basic-block steps on `tripleRatchetProgAtExt b ext` for the non-duplicate error tail
(`+0x2db4 → +0x2eac`, `+0x2eb0 → dropSessionStructure3`), the shared error-exit tail
(`+0x34dc → dropSpe2 → dropSessionStructure3 → retAddr`), and the version-mismatch path
(`+0x1e04 → +0x3410 → dropSessionStructure3`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Layout-Independent `adrp` Helpers -/

theorem adrp_closure_logLevel_nondupC {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0x2dec#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11756))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x2dec#64)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11756))) =
      b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

theorem adrp_closure_rodata_nondupD {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0x2eb8#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x2eb8#64)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

/-! ## 2. Non-Duplicate Error Segments C & D (`+0x2db4 → +0x2eac`, `+0x2eb0 → dropSessionStructure3`) -/

theorem p3_err_nondup_c_ext_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2db4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eac#64) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗
       ((s.sp + 0x288#64) ↦₆₄ e3) ∗
       ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗
          ((s.sp + 0x288#64) ↦₆₄ e3) ∗
          ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗
          ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗
          ((errsPtr + 0x18#64) ↦₆₄ e3) ∗
          ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := decryptPrekeyClosure_shim_ok_ext_4k hA
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2db4 0x2df4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2ea0 0x2ea8
  dsimp only [tripleRatchetProgAtExt] at hshim hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_logLevel_nondupC hb hentry).1
  have hadrp := (adrp_closure_logLevel_nondupC hb hentry).2
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hlog : (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by bv_arith
  have herr0 : 0#64 * 0x30#64 + errsPtr = errsPtr := by bv_arith
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p3_err_nondup_c_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2db4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eac#64) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗
       ((s.sp + 0x288#64) ↦₆₄ e3) ∗
       ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗
       ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗
       ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗
       ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗
       ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗
          ((s.sp + 0x288#64) ↦₆₄ e3) ∗
          ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗
          ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗
          ((errsPtr + 0x18#64) ↦₆₄ e3) ∗
          ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = 17#64 ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p3_err_nondup_c_ext_4k_wp b ext (AllocContractsMem4K.of_AllocContracts hA)
    s coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hb hpc hrun hsp_align hx19 hx21 hx25

theorem p3_err_nondup_d_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr dfPtr ro0 ro1
    u_df0 u_df8 u_270 u_278 u_280 u_288 : BitVec 64)
    (u_df10 u_290 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hdf_nz : dfPtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eb0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = dfPtr)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
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
        s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdf_beq : (dfPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hdf_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2eb0 0x2ef4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34d4 0x34d8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_rodata_nondupD hb hentry).1
  have hadrp := (adrp_closure_rodata_nondupD hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x34d8#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13528)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
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
    by simp_all [arm64_norm]⟩

/-! ## 3. Shared Error-Exit Tail (`+0x34dc → dropSpe2 → dropSessionStructure3 → retAddr`) -/

theorem p3_err_tail_dup_a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
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
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
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
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34dc 0x34e4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3500 0x3504
  closure_fetches_range_cli b (Rust.withPanics ext) 0x351c 0x3534
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3570 0x3598
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
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
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000017#64 := hx28
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_tail_nondup_a1_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) s
      (((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = errsPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = errsPtr ∧
        s1.readReg64 .x22 = errsPtr ∧
        s1.readReg64 .x23 = 1#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34f4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34dc 0x34f0
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x34f0#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13552)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_tail_nondup_a2_ext_4k_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34f4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr)
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
  have hdealloc := decryptPrekeyClosure_dealloc_ok_ext_4k hA
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34f4 0x3534
  closure_fetches_range_cli b (Rust.withPanics ext) 0x3570 0x3598
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
  have hx21' : s.readReg64 (Reg.gpr 21#5) = errsPtr := hx21
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

theorem p3_err_tail_nondup_a2_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34f4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = errsPtr)
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
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p3_err_tail_nondup_a2_ext_4k_wp b ext (AllocContractsMem4K.of_AllocContracts hA)
    s coroPtr errsPtr ssCap v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c v_278 v_28c u_260 u_380
    hcap_ne hpc hrun hsp_align hx19 hx21 hx22 hx23 hx24 hx25 hx28

theorem p3_err_tail_b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64)
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
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
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

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
