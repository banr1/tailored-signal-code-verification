/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P2 Over-Path Outer `v3` Reject Basic Blocks

Defines the 24-byte `.rodata` slice `x3dhUnsupportedStr` (`"X3DH no longer supported"`) and proves
basic-block specifications for the outer `v3` (`(msgPtr + 0xf0) ↦₈ 3#8`) reject path from `+0x0868`
to `dropProcessPrekeyImplName`.
-/

@[expose] public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## `.rodata` String Helper (`"X3DH no longer supported"`) -/

abbrev x3dhUnsupportedOff : Nat :=
  num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))

/-- The 24-byte `.rodata` `"X3DH no longer supported"` slice referenced at
`decryptPrekeyClosure + 2608..2612`. -/
noncomputable def x3dhUnsupportedStr : List (BitVec 8) :=
  (libsignalSessionImage.data.drop
    (x3dhUnsupportedOff - libsignalSessionImage.dataOff)).take 24

set_option maxRecDepth 2000000 in
private theorem x3dhUnsupported_dataOff_le :
    libsignalSessionImage.dataOff ≤ x3dhUnsupportedOff :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

set_option maxRecDepth 2000000 in
private theorem x3dhUnsupported_bound :
    (x3dhUnsupportedOff - libsignalSessionImage.dataOff) + 24 ≤
      libsignalSessionImage.data.length :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

theorem x3dhUnsupportedStr_length : x3dhUnsupportedStr.length = 24 := by
  unfold x3dhUnsupportedStr
  have h := x3dhUnsupported_bound
  rw [List.length_take, List.length_drop]
  omega

set_option maxRecDepth 2000000 in
theorem rodata_x3dhUnsupported_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))) ↦ᵣ x3dhUnsupportedStr) ∗ P := by
  have hh := ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
    (off := x3dhUnsupportedOff) (n := 24) (bs := x3dhUnsupportedStr)
    x3dhUnsupported_dataOff_le x3dhUnsupported_bound
    (by rfl_kernel) (by rfl_kernel) x3dhUnsupportedStr_length rfl
  obtain ⟨hRO, hread⟩ := ProofLib.ObjectLoad.holdsBytes_ro hh
  exact Satisfies.rodata_intro hRO hread (by rw [x3dhUnsupportedStr_length]; decide) hP

theorem p2_intro_rodata_x3dhUnsupported {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))) ↦ᵣ x3dhUnsupportedStr) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))) ↦ᵣ x3dhUnsupportedStr) ∗ P) ∗ R := by
    rw [sepConj_assoc]
    exact rodata_x3dhUnsupported_intro himg hF hm
  exact h R hm' hL

theorem p2_over_v3_adrp_rodata {b cAddr : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : cAddr = b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) :
    (((cAddr + 0xa30#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0xa30#64)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

/-! ## Outer `v3` Basic Blocks (`+0x0868 → dropProcessPrekeyImplName`) -/

set_option maxHeartbeats 800000 in
theorem p2_over_seg1a_v3_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 3#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8a0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x868 0x89c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyActive10At]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p2_over_seg1b_v3_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 3#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 3#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 3#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8a0 0x8bc
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 3#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
/-- Steps `+0x08c0 → strToOwnedLocal2Name`: checks `Ok(false)` at `sp + 0x3e0..0x3e8`, deallocates
`(serPtr, 33, 1)`, observes `(msgPtr + 0xf0) ↦₈ 3#8`, and calls `<str as ToOwned>::to_owned [local#2]`
on the 24-byte `"X3DH no longer supported"` slice into `sp + 0x3e0`. -/
theorem p2_over_seg1c_v3_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s : State) (coroPtr msgPtr serPtr : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Matched.strToOwnedLocal2Name) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 =
          b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) ∧
        s1.readReg64 .x2 = 24#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xa44#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := p2_dealloc_at_closure_ext hA
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x910 0x914
  closure_fetches_range_cli b (Rust.withPanics ext) 0xa08 0xa40
  dsimp only [tripleRatchetProgAtExt, Matched.strToOwnedLocal2Name] at hdealloc hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (p2_over_v3_adrp_rodata hb hentry).1
  have hadrp := (p2_over_v3_adrp_rodata hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0xa40#64 +
      bv% ((2 ^ 64 + ls_off% "<str as alloc::borrow::ToOwned>::to_owned" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2624)) % 2 ^ 64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<str as alloc::borrow::ToOwned>::to_owned" := by
    rw [hentry, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")]
    simp only [BitVec.add_assoc]; rfl
  have hro :
      (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)))) +
        bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) := by
    bv_arith
  rw [← htarget]
  clear hentry htarget
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  wp_call hdealloc (serPtr, 33, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
theorem p2_over_seg1c_v3_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr serPtr : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Matched.strToOwnedLocal2Name) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 =
          b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) ∧
        s1.readReg64 .x2 = 24#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xa44#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x910 0x914
  closure_fetches_range_cli b (Rust.withPanics ext) 0xa08 0xa40
  dsimp only [tripleRatchetProgAtExt, Matched.strToOwnedLocal2Name] at hdealloc hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (p2_over_v3_adrp_rodata hb hentry).1
  have hadrp := (p2_over_v3_adrp_rodata hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0xa40#64 +
      bv% ((2 ^ 64 + ls_off% "<str as alloc::borrow::ToOwned>::to_owned" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2624)) % 2 ^ 64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        "<str as alloc::borrow::ToOwned>::to_owned" := by
    rw [hentry, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")]
    simp only [BitVec.add_assoc]; rfl
  have hro :
      (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)))) +
        bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) % 4096) =
      b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612)) := by
    bv_arith
  rw [← htarget]
  clear hentry htarget
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  wp_call hdealloc (serPtr, 33, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Steps `+0x0a44 → dropProcessPrekeyImplName` via `+0x1324` and `+0x1648`, loading `outPtr` from
`[sp + 0xc8]` and setting `errTag = 0x8000000000000018#64`. -/
theorem p2_over_seg1d_v3_to_drop_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr cap ptr len u_a8 u_d0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xa44#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ len))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ len)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = ptr ∧
        s1.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = cap ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1698#64) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 3#64) = true :=
    p2_cond_ne_adds64_of_ne_neg3 (by decide)
  have hsplit_cap :
      ((s.sp + 0x3e0#64) ↦₆₄ cap) =
        ((s.sp + 0x3e0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((s.sp + 0x3e4#64) ↦₃₂ cap.extractLsb' 32 32) := by
    rw [pointsTo64_split32 (s.sp + 0x3e0#64) cap]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xa44 0xa5c
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1324 0x1340
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1678 0x1694
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x1694#64 + bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 5780)) % 2 ^ 64) =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") := by
    rw [hentry]; simp only [BitVec.add_assoc]; rfl
  rw [← htarget]
  clear hentry htarget
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  apply SepWP.fold (Entails.of_eq hsplit_cap) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hsplit_cap.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
