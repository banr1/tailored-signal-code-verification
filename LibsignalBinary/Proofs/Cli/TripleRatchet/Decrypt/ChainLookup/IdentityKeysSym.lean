/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSym
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.TryDecryptStateRatchetCoins
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` Segment S0 (`IdentityKeys`) Symbolic Execution

Basic-block `SepWP` lemmas for the prologue and identity-key checks (`+0x000 .. +0x1d8`) of
`try_decrypt_with_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_prologue_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hlocal : LocalIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (s0 : State)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64)
    (h_pc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret)
    (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA)
    (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    SepWP (tripleRatchetProgAtExt img.base ext) (entry + bv% (84)) s0
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗
       words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗
       ((sp + 48#64) ↦₆₄ w_sp48) ∗
       vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗
       logOff img ∗
       stackAt sp localIdentityKeyStack)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = x.ret ∧
        sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧
        sf.readReg64 .x22 = x.msgA ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧
        (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        (P_f ⊢
          tryDecryptSavedRegs s0.sp s0 ∗
          (sp ↦₆₄ 0#64) ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          vecGhostAt A x.G.localIk x.ss ∗
          localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          logOff img ∗
          stackAt sp localIdentityKeyStack)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hloc_addr : (tripleRatchetProgAtExt img.base ext).fnAddr localIdentityKeyName =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::local_identity_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::local_identity_key") (by decide)
  unfold LocalIdentityKeyOkExt at hlocal
  rw [hloc_addr] at hlocal
  dec_fetches_cli img.base ext hfn 0x0 84
  clear hfn hloc_addr
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold tryDecryptSavedRegs words8At words4At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_apply
  wp_finish
  refine ⟨by bv_omega, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  · rw [← hx5]; simp_all [arm64_norm]
  · have hsp_loc : s0.sp - 1104#64 = s0.sp - 1504#64 + 400#64 := by bv_omega
    have hsp_48 : s0.sp - 1456#64 = s0.sp - 1504#64 + 48#64 := by bv_omega
    rw [hsp_loc, hsp_48]
    exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_copy_local_ik_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (x : TryDecryptGhost) (s0 s : State)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
    (u1104 : BitVec 64) (u1112 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 84#64)
    (h_run : s.status = .Running)
    (h_sp : s.sp = s0.sp - 1504#64)
    (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx29 : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    let sp := s0.sp - 1504#64
    SepWP (tripleRatchetProgAtExt b ext) (entry + bv% (156)) s
      (((sp + 400#64) ↦₈ 0#8) ∗
       localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗
       ((sp + 1112#64) ↦₈ u1112))
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x0 = x.ss ∧
        sf.readReg64 .x8 = sp + 400#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 ∧
        (P_f ⊢
          ((sp + 400#64) ↦₈ 0#8) ∗
          localGroupB (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          localGroupB (sp + 1280#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          ((sp + 1104#64) ↦₆₄ w2) ∗
          ((sp + 1112#64) ↦₈ b31))) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  dec_fetches_cli b ext hfn 0x54 72
  clear hfn
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold localGroupA localGroupB
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  rw [localGroupA_401_to_B (s0.sp - 1504#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31]
  wp_steps
  rw [localGroupA_1280_to_B (s0.sp - 1504#64) b0 b1 b2 b3 d4 d5 d6 dw0 dw1 dw2 db31]
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_call_remote_ik_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hrem : RemoteIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (s : State)
    (h_pc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 156#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.ss)
    (hx8 : s.readReg64 .x8 = s.sp + 400#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt img.base ext) (entry + bv% (160)) s
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
       memRegion (s.sp + 400#64) 34 ∗
       logOff img ∗
       stackAt s.sp remoteIdentityKeyStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢
          vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (s.sp + 400#64) x.st.remoteIdentity ∗
          logOff img ∗
          stackAt s.sp remoteIdentityKeyStack)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hrem_addr : (tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::remote_identity_key") (by decide)
  unfold RemoteIdentityKeyOkExt at hrem
  rw [hrem_addr] at hrem
  dec_fetches_cli img.base ext hfn 0x9c 4
  clear hfn hrem_addr
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_remote_ik_common_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State)
    (tag : BitVec 8)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 160#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt b ext) (entry + bv% (384)) s
      (((s.sp + 400#64) ↦₈ 0#8) ∗
       ((s.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s.sp + 352#64) ↦₆₄ u352) ∗
       ((s.sp + 360#64) ↦₈ u360) ∗
       ((s.sp + 976#64) ↦₃₂ u976) ∗
       ((s.sp + 980#64) ↦₈ u980) ∗
       ((s.sp + 981#64) ↦₈ u981))
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        sf.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        sf.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧
        sf.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢
          ((s.sp + 400#64) ↦₈ 0#8) ∗
          ((s.sp + 401#64) ↦₈ tag) ∗
          remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5))) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  dec_fetches_cli b ext hfn 0xa0 12
  dec_fetches_cli b ext hfn 0x154 44
  clear hfn
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold remoteGroupC
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  rw [hb4, hb5]
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.adrp_0xc0_tryDecrypt_eq_logFilterAddr {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) :
    ((entry + bv% (192) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" + 500))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry, BitVec.add_assoc img.base, adrp_page_of_aligned hbal,
      CryptoVerification.LibsignalSession.logFilterAddr]
  have hmask : (((bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) + 192#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = (bv% (page% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>" + 192))) := rfl
  rw [hmask]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_remote_none_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (s : State)
    (u1024 u1032 u1280 : BitVec 64)
    (h_pc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx11 : s.readReg64 .x11 = 0#64)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt img.base ext) (entry + bv% (472)) s
      (((s.sp + 1024#64) ↦₆₄ u1024) ∗
       ((s.sp + 1032#64) ↦₆₄ u1032) ∗
       ((s.sp + 1280#64) ↦₆₄ u1280) ∗
       logOff img)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          memRegion (s.sp + 1024#64) 16 ∗
          memRegion (s.sp + 1280#64) 8 ∗
          logOff img)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hentry_val : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") := by
    rw [Program.fnAddr_rebase, hfn]
  dec_fetches_cli img.base ext hfn 0x180 4
  dec_fetches_cli img.base ext hfn 0x564 16
  dec_fetches_cli img.base ext hfn 0xb0 32
  dec_fetches_cli img.base ext hfn 0x14c 8
  clear hfn
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  have hlog := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.adrp_0xc0_tryDecrypt_eq_logFilterAddr himg hentry_val
  clear hentry_val himg
  unfold logOff
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))) ?_
  rw [show (s.sp + 1032#64) = (s.sp + 1024#64) + 8#64 by bv_omega,
      ← sepConj_assoc, ← memRegion_split (s.sp + 1024#64) 8 8 (by decide)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.identityKeys_remote_some_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hsame : IsSameAccountOkExt b ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64,
      (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName
    SepWP (tripleRatchetProgAtExt b ext) (entry + bv% (472)) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗
       ((s.sp + 400#64) ↦₆₄ u400) ∗
       ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗
       ((s.sp + 360#64) ↦₈ b31) ∗
       ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗
       ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       stackAt s.sp isSameAccountStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧
        sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢
          ((s.sp + 48#64) ↦₆₄ x.remA) ∗
          ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗
          ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗
          ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          stackAt s.sp isSameAccountStack)) := by
  dsimp only
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
  have hsame_addr : (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (by decide)
  unfold IsSameAccountOkExt at hsame
  rw [hsame_addr] at hsame
  dec_fetches_cli b ext hfn 0x180 92
  clear hfn hsame_addr
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = entry
  examples_hide_fetches
  unfold remoteGroupD
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by
    unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗
       (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗
       (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  wp_steps
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by
    unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by
    unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗
       (s.sp + 60#64) ↦₈ b4 ∗
       (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗
       (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗
       (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb4, hb5, hb6, hb15_22, hrem56]
  wp_apply
  wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
