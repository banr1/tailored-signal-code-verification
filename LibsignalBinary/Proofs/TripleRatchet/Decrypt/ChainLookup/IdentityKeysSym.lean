/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

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

/-!
# Symbolic Execution Step Lemmas for Segment S0 (`IdentityKeys`)

Fixed-image and relocatable `[LibsignalPlacement]` basic-block symbolic execution lemmas for
Segment S0 (`+0x000 → +0x1d8`) of `try_decrypt_with_state`.
-/


theorem identityKeys_prologue_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hlocal : LocalIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (s0 : State)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64)
    (h_pc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName)
    (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret)
    (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA)
    (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hloc_addr : (tripleRatchetProgAtExt img.base ext).fnAddr localIdentityKeyName =
      (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::local_identity_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) :=
    fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::local_identity_key") (by decide)
  unfold LocalIdentityKeyOkExt at hlocal
  rw [hloc_addr] at hlocal
  dec_fetches img.base ext hfn 0x0 84
  clear hfn hloc_addr
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
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

theorem bytes4_expand (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦₃₂ pack32 b0 b1 b2 b3) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3)) := by
  unfold pack32
  rw [← pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes8_expand (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ pack64 b0 b1 b2 b3 b4 b5 b6 b7) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
     ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) := by
  unfold pack64
  rw [← pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem bytes7_groupA_eq_groupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ pack32 b0 b1 b2 b3) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ pack32 b3 b4 b5 b6)) := by
  rw [bytes4_expand a b0 b1 b2 b3, bytes4_expand (a + 3#64) b3 b4 b5 b6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes9_64_8_eq_8_64 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    ((a ↦₆₄ pack64 b0 b1 b2 b3 b4 b5 b6 b7) ∗ ((a + 8#64) ↦₈ b8)) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ pack64 b1 b2 b3 b4 b5 b6 b7 b8)) := by
  rw [bytes8_expand a b0 b1 b2 b3 b4 b5 b6 b7, bytes8_expand (a + 1#64) b1 b2 b3 b4 b5 b6 b7 b8]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes17_shift_eq (a : BitVec 64)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8) :
    ((a ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13) ∗
     ((a + 8#64) ↦₆₄ pack64 b14 b15 b16 b17 b18 b19 b20 b21) ∗
     ((a + 16#64) ↦₈ b22)) =
    ((a ↦₈ b6) ∗
     ((a + 1#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
     ((a + 9#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22)) := by
  have h1 := bytes9_64_8_eq_8_64 (a + 8#64) b14 b15 b16 b17 b18 b19 b20 b21 b22
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1
  rw [h1, ← sepConj_assoc, bytes9_64_8_eq_8_64 a b6 b7 b8 b9 b10 b11 b12 b13 b14, sepConj_assoc]

def localGroupA (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ pack32 b0 b1 b2 b3) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₆₄ w0) ∗
  ((a + 15#64) ↦₆₄ w1) ∗
  ((a + 23#64) ↦₆₄ w2) ∗
  ((a + 31#64) ↦₈ b31)

def localGroupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗
  ((a + 1#64) ↦₈ b1) ∗
  ((a + 2#64) ↦₈ b2) ∗
  ((a + 3#64) ↦₃₂ pack32 b3 b4 b5 b6) ∗
  ((a + 7#64) ↦₆₄ w0) ∗
  ((a + 15#64) ↦₆₄ w1) ∗
  ((a + 23#64) ↦₆₄ w2) ∗
  ((a + 31#64) ↦₈ b31)

theorem localGroupA_eq_localGroupB (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 =
    localGroupB a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 := by
  unfold localGroupA localGroupB
  rw [bytes4_expand a b0 b1 b2 b3, bytes4_expand (a + 3#64) b3 b4 b5 b6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_localGroupA_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 := by
  obtain ⟨u0, u1, u2, u3, rfl, _⟩ := exists_unpack64_of_length_32 h
  refine ⟨u0.extractLsb' 0 8, u0.extractLsb' 8 8, u0.extractLsb' 16 8, u0.extractLsb' 24 8,
          u0.extractLsb' 32 8, u0.extractLsb' 40 8, u0.extractLsb' 48 8,
          pack64 (u0.extractLsb' 56 8) (u1.extractLsb' 0 8) (u1.extractLsb' 8 8) (u1.extractLsb' 16 8)
                 (u1.extractLsb' 24 8) (u1.extractLsb' 32 8) (u1.extractLsb' 40 8) (u1.extractLsb' 48 8),
          pack64 (u1.extractLsb' 56 8) (u2.extractLsb' 0 8) (u2.extractLsb' 8 8) (u2.extractLsb' 16 8)
                 (u2.extractLsb' 24 8) (u2.extractLsb' 32 8) (u2.extractLsb' 40 8) (u2.extractLsb' 48 8),
          pack64 (u2.extractLsb' 56 8) (u3.extractLsb' 0 8) (u3.extractLsb' 8 8) (u3.extractLsb' 16 8)
                 (u3.extractLsb' 24 8) (u3.extractLsb' 32 8) (u3.extractLsb' 40 8) (u3.extractLsb' 48 8),
          u3.extractLsb' 56 8, fun a => ?_⟩
  unfold localGroupA unpack64
  rw [bytes4_expand, bytes8_expand, bytes8_expand, bytes8_expand]
  simp only [List.cons_append, List.nil_append, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

def remoteGroupC (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13) ∗
  ((a + 14#64) ↦₆₄ pack64 b14 b15 b16 b17 b18 b19 b20 b21) ∗
  ((a + 22#64) ↦₈ b22) ∗
  ((a + 23#64) ↦₆₄ w3) ∗
  ((a + 31#64) ↦₈ b31)

def remoteGroupD (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗
  ((a + 4#64) ↦₈ b4) ∗
  ((a + 5#64) ↦₈ b5) ∗
  ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
  ((a + 15#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22) ∗
  ((a + 23#64) ↦₆₄ w3) ∗
  ((a + 31#64) ↦₈ b31)

theorem remoteGroupC_eq_remoteGroupD (a : BitVec 64) (w0 : BitVec 32) (b4 b5 : BitVec 8)
    (b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) :
    remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 =
    remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 := by
  unfold remoteGroupC remoteGroupD
  rw [bytes8_expand (a + 6#64), bytes8_expand (a + 14#64),
      bytes8_expand (a + 7#64), bytes8_expand (a + 15#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_remoteGroupC_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
      (w3 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 := by
  obtain ⟨u0, u1, u2, u3, rfl, _⟩ := exists_unpack64_of_length_32 h
  refine ⟨pack32 (u0.extractLsb' 0 8) (u0.extractLsb' 8 8) (u0.extractLsb' 16 8) (u0.extractLsb' 24 8),
          u0.extractLsb' 32 8, u0.extractLsb' 40 8,
          u0.extractLsb' 48 8, u0.extractLsb' 56 8,
          u1.extractLsb' 0 8, u1.extractLsb' 8 8, u1.extractLsb' 16 8, u1.extractLsb' 24 8,
          u1.extractLsb' 32 8, u1.extractLsb' 40 8, u1.extractLsb' 48 8, u1.extractLsb' 56 8,
          u2.extractLsb' 0 8, u2.extractLsb' 8 8, u2.extractLsb' 16 8, u2.extractLsb' 24 8,
          u2.extractLsb' 32 8, u2.extractLsb' 40 8, u2.extractLsb' 48 8,
          pack64 (u2.extractLsb' 56 8) (u3.extractLsb' 0 8) (u3.extractLsb' 8 8) (u3.extractLsb' 16 8)
                 (u3.extractLsb' 24 8) (u3.extractLsb' 32 8) (u3.extractLsb' 40 8) (u3.extractLsb' 48 8),
          u3.extractLsb' 56 8, fun a => ?_⟩
  unfold remoteGroupC unpack64
  rw [bytes4_expand, bytes8_expand, bytes8_expand, bytes8_expand]
  simp only [List.cons_append, List.nil_append, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem localGroupA_401_to_B (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    ((sp + 401#64) ↦₃₂ pack32 b0 b1 b2 b3 ∗
     (sp + 405#64) ↦₈ b4 ∗
     (sp + 406#64) ↦₈ b5 ∗
     (sp + 407#64) ↦₈ b6 ∗
     (sp + 408#64) ↦₆₄ w0 ∗
     (sp + 416#64) ↦₆₄ w1 ∗
     (sp + 424#64) ↦₆₄ w2 ∗
     (sp + 432#64) ↦₈ b31) =
    ((sp + 401#64) ↦₈ b0 ∗
     (sp + 402#64) ↦₈ b1 ∗
     (sp + 403#64) ↦₈ b2 ∗
     (sp + 404#64) ↦₃₂ pack32 b3 b4 b5 b6 ∗
     (sp + 408#64) ↦₆₄ w0 ∗
     (sp + 416#64) ↦₆₄ w1 ∗
     (sp + 424#64) ↦₆₄ w2 ∗
     (sp + 432#64) ↦₈ b31) := by
  simpa only [localGroupA, localGroupB, BitVec.add_assoc, BitVec.reduceAdd] using
    localGroupA_eq_localGroupB (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31

theorem localGroupA_1280_to_B (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 : BitVec 64) (b31 : BitVec 8) :
    ((sp + 1280#64) ↦₃₂ pack32 b0 b1 b2 b3 ∗
     (sp + 1284#64) ↦₈ b4 ∗
     (sp + 1285#64) ↦₈ b5 ∗
     (sp + 1286#64) ↦₈ b6 ∗
     (sp + 1287#64) ↦₆₄ w0 ∗
     (sp + 1295#64) ↦₆₄ w1 ∗
     (sp + 1303#64) ↦₆₄ w2 ∗
     (sp + 1311#64) ↦₈ b31) =
    ((sp + 1280#64) ↦₈ b0 ∗
     (sp + 1281#64) ↦₈ b1 ∗
     (sp + 1282#64) ↦₈ b2 ∗
     (sp + 1283#64) ↦₃₂ pack32 b3 b4 b5 b6 ∗
     (sp + 1287#64) ↦₆₄ w0 ∗
     (sp + 1295#64) ↦₆₄ w1 ∗
     (sp + 1303#64) ↦₆₄ w2 ∗
     (sp + 1311#64) ↦₈ b31) := by
  simpa only [localGroupA, localGroupB, BitVec.add_assoc, BitVec.reduceAdd] using
    localGroupA_eq_localGroupB (sp + 1280#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31

theorem identityKeys_copy_local_ik_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (x : TryDecryptGhost) (s0 s : State)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
    (u1104 : BitVec 64) (u1112 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 84#64)
    (h_run : s.status = .Running)
    (h_sp : s.sp = s0.sp - 1504#64)
    (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx29 : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches b ext hfn 0x54 72
  clear hfn
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = entry
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

theorem identityKeys_call_remote_ik_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hrem : RemoteIdentityKeyOkExt img A ext)
    (x : TryDecryptGhost) (s : State)
    (h_pc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 156#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.ss)
    (hx8 : s.readReg64 .x8 = s.sp + 400#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hrem_addr : (tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName =
      (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) :=
    fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::remote_identity_key") (by decide)
  unfold RemoteIdentityKeyOkExt at hrem
  rw [hrem_addr] at hrem
  dec_fetches img.base ext hfn 0x9c 4
  clear hfn hrem_addr
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches
  wp_steps
  wp_apply
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_remote_ik_common_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State)
    (tag : BitVec 8)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 160#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = s.sp + 320#64) :
    let entry := (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  dec_fetches b ext hfn 0xa0 12
  dec_fetches b ext hfn 0x154 44
  clear hfn
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = entry
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

theorem adrp_0xc0_tryDecrypt_eq_logFilterAddr {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) :
    ((entry + bv% (192) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_session::HookRng>" + 500))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry, BitVec.add_assoc img.base, adrp_page_of_aligned hbal,
      CryptoVerification.LibsignalSession.logFilterAddr]
  have hmask : ((214564#64 + 192#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = 212992#64 := rfl
  rw [hmask]
  bv_omega

theorem identityKeys_remote_none_wp {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (s : State)
    (u1024 u1032 u1280 : BitVec 64)
    (h_pc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 384#64)
    (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx11 : s.readReg64 .x11 = 0#64)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64) :
    let entry := (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hentry_val : (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>") := by
    rw [Program.fnAddr_rebase, hfn]
  dec_fetches img.base ext hfn 0x180 4
  dec_fetches img.base ext hfn 0x564 16
  dec_fetches img.base ext hfn 0xb0 32
  dec_fetches img.base ext hfn 0x14c 8
  clear hfn
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName = entry
  examples_hide_fetches
  have hlog := adrp_0xc0_tryDecrypt_eq_logFilterAddr himg hentry_val
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

theorem identityKeys_remote_some_wp {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hsame : IsSameAccountOkExt b ext)
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + 384#64)
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
    let entry := (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName
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
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")
  have hsame_addr : (tripleRatchetProgAtExt b ext).fnAddr isSameAccountName =
      (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_session::HookRng>")) :=
    fnAddr_tryDecrypt_rel64 (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") (by decide)
  unfold IsSameAccountOkExt at hsame
  rw [hsame_addr] at hsame
  dec_fetches b ext hfn 0x180 92
  clear hfn hsame_addr
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr tryDecryptName = entry
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

/-! ## Relocatable `[LibsignalPlacement]` Step Lemmas (Block `130`) -/

theorem identityKeys_prologue_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hlocal : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 28)
      (withLsCodeLoaded lsmpl (localIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64)
    (h_pc : s0.pc = (blkPl_131).base) (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss) (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA) (hx4 : s0.readReg64 .x4 = x.msgA)
    (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 84#64) s0
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = x.ret ∧ sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧ sf.readReg64 .x22 = x.msgA ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧ (sf.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        sf.readReg64 .x25 = x.locA ∧ sf.readReg64 .x29 = s0.sp - 96#64 ∧
        (P_f ⊢ tryDecryptSavedRegs s0.sp s0 ∗ (sp ↦₆₄ 0#64) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
          vecGhostAt A x.G.localIk x.ss ∗ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack)) := by
  dsimp only
  simp only [withLsCodeLoaded, localIdentityKeyPlacedSpec] at hlocal
  unfold tryDecryptSavedRegs words8At words4At
  simp only [logOff_tryDecryptDummyImg, BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 28); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_apply; wp_finish
  refine ⟨by bv_omega, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  · rw [← hx5]; simp_all [arm64_norm]
  · have hsp_loc : s0.sp - 1104#64 = s0.sp - 1504#64 + 400#64 := by bv_omega
    have hsp_48 : s0.sp - 1456#64 = s0.sp - 1504#64 + 48#64 := by bv_omega
    rw [hsp_loc, hsp_48]; exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_copy_local_ik_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (s0 s : State)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
    (u1104 : BitVec 64) (u1112 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 84#64) (h_run : s.status = .Running)
    (h_sp : s.sp = s0.sp - 1504#64) (h_sp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s.readReg64 .x21 = x.ss)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx29 : s.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 156#64) s
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x0 = x.ss ∧ sf.readReg64 .x8 = sp + 400#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = sp + 320#64 ∧
        sf.readReg64 .x21 = x.ss ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 1280#64 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = (s0.sp - 1504#64) + 1408#64 ∧
        (P_f ⊢ ((sp + 400#64) ↦₈ 0#8) ∗
          localGroupB (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          localGroupB (sp + 1280#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
          ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31))) := by
  dsimp only; unfold localGroupA localGroupB
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps
  rw [localGroupA_401_to_B (s0.sp - 1504#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31]; wp_steps
  rw [localGroupA_1280_to_B (s0.sp - 1504#64) b0 b1 b2 b3 d4 d5 d6 dw0 dw1 dw2 db31]; wp_steps
  wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl)⟩

theorem identityKeys_call_remote_ik_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrem : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 29)
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h_pc : s.pc = (blkPl_131).base + 156#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx0 : s.readReg64 .x0 = x.ss)
    (hx8 : s.readReg64 .x8 = s.sp + 400#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 160#64) s
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s.sp + 400#64) 34 ∗
       logOff tryDecryptDummyImg ∗ stackAt s.sp remoteIdentityKeyStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (s.sp + 400#64) x.st.remoteIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt s.sp remoteIdentityKeyStack)) := by
  simp only [withLsCodeLoaded, remoteIdentityKeyPlacedSpec, logOff_tryDecryptDummyImg] at hrem ⊢
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 29); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  wp_apply; wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], Entails.of_eq (by sep_ac_rfl)⟩

theorem identityKeys_remote_ik_common_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (s : State) (tag : BitVec 8)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (u352 : BitVec 64) (u360 : BitVec 8) (u976 : BitVec 32) (u980 u981 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 160#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx20 : s.readReg64 .x20 = s.sp + 320#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 384#64) s
      (((s.sp + 400#64) ↦₈ 0#8) ∗ ((s.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s.sp + 352#64) ↦₆₄ u352) ∗ ((s.sp + 360#64) ↦₈ u360) ∗
       ((s.sp + 976#64) ↦₃₂ u976) ∗ ((s.sp + 980#64) ↦₈ u980) ∗ ((s.sp + 981#64) ↦₈ u981))
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        sf.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        sf.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧
        sf.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.sp + 320#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        (P_f ⊢ ((s.sp + 400#64) ↦₈ 0#8) ∗ ((s.sp + 401#64) ↦₈ tag) ∗
          remoteGroupC (s.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗
          ((s.sp + 976#64) ↦₃₂ w0) ∗ ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5))) := by
  unfold remoteGroupC; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps; wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  rw [hb4, hb5]; exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_remote_none_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (s : State) (u1024 u1032 u1280 : BitVec 64)
    (h_pc : s.pc = (blkPl_131).base + 384#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true) (hx11 : s.readReg64 .x11 = 0#64)
    (hx29 : s.readReg64 .x29 = s.sp + 1408#64) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s
      (((s.sp + 1024#64) ↦₆₄ u1024) ∗ ((s.sp + 1032#64) ↦₆₄ u1032) ∗
       ((s.sp + 1280#64) ↦₆₄ u1280) ∗ logOff tryDecryptDummyImg)
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢ memRegion (s.sp + 1024#64) 16 ∗ memRegion (s.sp + 1280#64) 8 ∗ logOff tryDecryptDummyImg)) := by
  simp only [logOff_tryDecryptDummyImg]
  wp_steps; wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], ?_⟩
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))) ?_
  rw [show (s.sp + 1032#64) = (s.sp + 1024#64) + 8#64 by bv_omega,
      ← sepConj_assoc, ← memRegion_split (s.sp + 1024#64) 8 8 (by decide)]
  exact Entails.of_eq (by sep_ac_rfl)

theorem identityKeys_remote_some_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hsame : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl isSameAccountSpec))
    (x : TryDecryptGhost) (remIk : IdentityKey) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8) (u400 : BitVec 64) (u408 : BitVec 8)
    (dw0 : BitVec 32) (db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 : BitVec 8)
    (dw3 : BitVec 64) (db31 : BitVec 8)
    (h_pc : s.pc = (blkPl_131).base + 384#64) (h_run : s.status = .Running)
    (h_sp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s.readReg64 .x10 = BitVec.zeroExtend 64 b22)
    (hx11 : s.readReg64 .x11 = 1#64) (hx20 : s.readReg64 .x20 = s.sp + 320#64)
    (hx25 : s.readReg64 .x25 = x.locA) (hx29 : s.readReg64 .x29 = s.sp + 1408#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s
      (((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₆₄ u400) ∗ ((s.sp + 408#64) ↦₈ u408) ∗
       ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
       ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ stackAt s.sp isSameAccountStack)
      (fun sf P_f =>
        sf.sp = s.sp ∧ sf.spAligned = true ∧
        (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        (sf.readReg64 .x1).setWidth 32 = 0#32 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.sp + 320#64 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = x.locA ∧
        sf.readReg64 .x29 = s.sp + 1408#64 ∧
        (P_f ⊢ ((s.sp + 48#64) ↦₆₄ x.remA) ∗ ((s.sp + 400#64) ↦₈ b6) ∗
          ((s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
          ((s.sp + 352#64) ↦₆₄ w3) ∗ ((s.sp + 360#64) ↦₈ b31) ∗ ((s.sp + 976#64) ↦₃₂ w0) ∗
          ((s.sp + 980#64) ↦₈ b4) ∗ ((s.sp + 981#64) ↦₈ b5) ∗
          ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗
          ((s.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          stackAt s.sp isSameAccountStack)) := by
  simp only [withLsCodeLoaded, isSameAccountSpec] at hsame
  unfold remoteGroupD; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_seq_lscl hcl (mid := (blkPl_131).base + 404#64); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl1
  have hb14 : BitVec.zeroExtend 8 (pack64 b14 b15 b16 b17 b18 b19 b20 b21) = b14 := by unfold pack64; bv_kernel
  have h400 :
      ((s.sp + 400#64) ↦₆₄ pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∗ (s.sp + 408#64) ↦₈ b14) =
      ((s.sp + 400#64) ↦₈ b6 ∗ (s.sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      bytes9_64_8_eq_8_64 (s.sp + 400#64) b6 b7 b8 b9 b10 b11 b12 b13 b14
  rw [hb14, ← sepConj_assoc ((s.sp + 400#64) ↦₆₄ _), h400, sepConj_assoc]
  apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 17); wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
  have hb4 : BitVec.zeroExtend 8 (b5 ++ b4) = b4 := by bv_kernel
  have hb5 : BitVec.extractLsb' 8 8 (BitVec.zeroExtend 32 (b5 ++ b4)) = b5 := by bv_kernel
  have hb6 : BitVec.zeroExtend 8 (pack64 b6 b7 b8 b9 b10 b11 b12 b13) = b6 := by unfold pack64; bv_kernel
  have hb15_22 :
      BitVec.truncate 64 ((BitVec.zeroExtend 64 b22 ++ pack64 b14 b15 b16 b17 b18 b19 b20 b21) >>> 8) =
        pack64 b15 b16 b17 b18 b19 b20 b21 b22 := by unfold pack64; bv_kernel
  have hrem56 :
      ((s.sp + 56#64) ↦₃₂ w0 ∗ (s.sp + 60#64) ↦₈ b4 ∗ (s.sp + 61#64) ↦₈ b5 ∗
       (s.sp + 62#64) ↦₈ b6 ∗ (s.sp + 63#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14 ∗
       (s.sp + 71#64) ↦₆₄ pack64 b15 b16 b17 b18 b19 b20 b21 b22 ∗
       (s.sp + 79#64) ↦₆₄ w3 ∗ (s.sp + 87#64) ↦₈ b31) =
      ((s.sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) := by
    simpa only [remoteGroupD, BitVec.add_assoc, BitVec.reduceAdd] using (hrem_eq (s.sp + 56#64)).symm
  rw [hb4, hb5, hb6, hb15_22, hrem56]
  wp_apply; wp_steps; wp_finish
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    Entails.of_eq (by sep_ac_rfl)⟩

theorem exists_localGroupA_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w0 w1 w2 : BitVec 64) (b31 : BitVec 8),
      m ⊨ localGroupA a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hlen, hm⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, heq⟩ := exists_localGroupA_of_length_32 hlen
  exact ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, heq a ▸ hm⟩

theorem exists_remoteGroupC_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
      (w3 : BitVec 64) (b31 : BitVec 8),
      (∀ q : BitVec 64, remoteGroupC q w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion q 32) ∧
      m ⊨ remoteGroupC a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hlen, hm⟩
  obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, heq⟩ :=
    exists_remoteGroupC_of_length_32 hlen
  refine ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31,
    fun q => ?_, heq a ▸ hm⟩
  rw [← heq q, ← hlen]; exact pointsToBytes_entails_memRegion q bs

def sessionStateRestAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧ G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧ G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗ vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗ optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗ ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_eq_ik_rest (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st = vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ sessionStateRestAt A ss G st := by
  unfold sessionStateAt sessionStateRestAt; ac_rfl

theorem sessionStateAt_ik_facts {A : RustAlloc} {ss : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {R : SepProp} {m : Memory} (hm : m ⊨ sessionStateAt A ss G st ∗ R) :
    PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with | none => G.remoteIk.bytes = [] | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) := by
  unfold sessionStateAt at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact ⟨hm.1.1, hm.1.2.1⟩

theorem exists_words4_of_memRegion_32 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ r0 r1 r2 r3 : BitVec 64, m ⊨ words4At a r0 r1 r2 r3 ∗ R := by
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hlen, hm⟩
  obtain ⟨r0, r1, r2, r3, heq⟩ := exists_words4_of_length_32 hlen
  exact ⟨r0, r1, r2, r3, heq a ▸ hm⟩

theorem exists_words8_of_memRegion_64 {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion a 64 ∗ R) :
    ∃ r4 r5 r6 r7 r8 r9 r10 r11 : BitVec 64, m ⊨ words8At a r4 r5 r6 r7 r8 r9 r10 r11 ∗ R := by
  rw [memRegion_eq_exists_bytes a 64 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨hlen, hm⟩
  obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, heq⟩ := exists_words8_of_length_64 hlen
  exact ⟨r4, r5, r6, r7, r8, r9, r10, r11, heq a ▸ hm⟩

theorem tryDecryptStack_split_prologue (sp0 : BitVec 64) :
    let sp := sp0 - 1504#64
    stackAt sp0 rootStack =
      memRegion (sp0 - 96#64) 32 ∗ memRegion (sp0 - 64#64) 64 ∗ memRegion sp 8 ∗
      memRegion (sp + 8#64) 40 ∗ memRegion (sp + 48#64) 8 ∗ memRegion (sp + 56#64) 344 ∗
      memRegion (sp + 400#64) 33 ∗ memRegion (sp + 433#64) 975 ∗
      stackAt sp localIdentityKeyStack ∗
      memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) := by
  dsimp only; rw [stackAt_sub sp0 1504 rootStack (by decide) (by decide)]
  have hsub : memRegion (sp0 - BitVec.ofNat 64 rootStack) (rootStack - 1504) =
      stackAt (sp0 - 1504#64) tryDecryptSubStack := by
    unfold stackAt tryDecryptSubStack tryDecryptFrameSize rootStack
    exact congrArg (fun a => memRegion a (262144 - 1504)) (by bv_omega)
  rw [hsub, stackAt_tryDecryptSubStack_sub sp0 localIdentityKeyStack (by decide)]; unfold stackAt
  change memRegion (sp0 - 1504#64) 1504 ∗
      (memRegion (sp0 - 1504#64 - BitVec.ofNat 64 localIdentityKeyStack) localIdentityKeyStack ∗
       memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) = _
  rw [memRegion_split (sp0 - 1504#64) 1408 96 (by decide),
      show sp0 - 1504#64 + 1408#64 = sp0 - 96#64 by bv_omega,
      memRegion_split (sp0 - 96#64) 32 64 (by decide),
      show sp0 - 96#64 + 32#64 = sp0 - 64#64 by bv_omega,
      memRegion_split (sp0 - 1504#64) 8 1400 (by decide),
      memRegion_split (sp0 - 1504#64 + 8#64) 40 1360 (by decide),
      show sp0 - 1504#64 + 8#64 + 40#64 = sp0 - 1504#64 + 48#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 48#64) 8 1352 (by decide),
      show sp0 - 1504#64 + 48#64 + 8#64 = sp0 - 1504#64 + 56#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 56#64) 344 1008 (by decide),
      show sp0 - 1504#64 + 56#64 + 344#64 = sp0 - 1504#64 + 400#64 by bv_omega,
      memRegion_split (sp0 - 1504#64 + 400#64) 33 975 (by decide),
      show sp0 - 1504#64 + 400#64 + 33#64 = sp0 - 1504#64 + 433#64 by bv_omega]
  sep_ac_rfl

theorem identityKeys_prologue_extract {sp0 : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ stackAt sp0 rootStack ∗ R) :
    let sp := sp0 - 1504#64
    ∃ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48 : BitVec 64,
      m ⊨ (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
           (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ memRegion (sp + 400#64) 33 ∗
           stackAt sp localIdentityKeyStack) ∗
          (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
           memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R) := by
  dsimp only; let sp := sp0 - 1504#64; rw [tryDecryptStack_split_prologue sp0] at hm
  have hm1 : m ⊨ memRegion (sp0 - 96#64) 32 ∗
      (memRegion (sp0 - 64#64) 64 ∗ memRegion sp 8 ∗ memRegion (sp + 48#64) 8 ∗
       memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, hm1⟩ := exists_words4_of_memRegion_32 hm1
  have hm2 : m ⊨ memRegion (sp0 - 64#64) 64 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ memRegion sp 8 ∗ memRegion (sp + 48#64) 8 ∗
       memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, hm2⟩ := exists_words8_of_memRegion_64 hm2
  have hm3 : m ⊨ memRegion sp 8 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       memRegion (sp + 48#64) 8 ∗ memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨w_sp0, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm4 : m ⊨ memRegion (sp + 48#64) 8 ∗
      (words4At (sp0 - 96#64) r0 r1 r2 r3 ∗ words8At (sp0 - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ memRegion (sp + 400#64) 33 ∗ stackAt sp localIdentityKeyStack ∗
       (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
        memRegion (sp0 - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ R)) := by
    convert hm3 using 1; sep_ac_rfl
  obtain ⟨w_sp48, hm4⟩ := exists_word64_of_memRegion_8 hm4
  refine ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, ?_⟩
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step2_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion (sp + 433#64) 975 ∗ R) :
    ∃ (d0 d1 d2 d3 d4 d5 d6 : BitVec 8) (dw0 dw1 dw2 : BitVec 64) (db31 : BitVec 8)
      (u1104 : BitVec 64) (u1112 : BitVec 8),
      m ⊨ (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
           ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112)) ∗
          (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
           memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R) := by
  rw [memRegion_split (sp + 433#64) 1 974 (by decide),
      show sp + 433#64 + 1#64 = sp + 434#64 by bv_omega,
      memRegion_split (sp + 434#64) 670 304 (by decide),
      show sp + 434#64 + 670#64 = sp + 1104#64 by bv_omega,
      memRegion_split (sp + 1104#64) 8 296 (by decide),
      show sp + 1104#64 + 8#64 = sp + 1112#64 by bv_omega,
      memRegion_split (sp + 1112#64) 1 295 (by decide),
      show sp + 1112#64 + 1#64 = sp + 1113#64 by bv_omega,
      memRegion_split (sp + 1113#64) 167 128 (by decide),
      show sp + 1113#64 + 167#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 32 96 (by decide),
      show sp + 1280#64 + 32#64 = sp + 1312#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 1280#64) 32 ∗
      (memRegion (sp + 1104#64) 8 ∗ memRegion (sp + 1112#64) 1 ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, hm1⟩ := exists_localGroupA_of_memRegion_32 hm1
  have hm2 : m ⊨ memRegion (sp + 1104#64) 8 ∗
      (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗ memRegion (sp + 1112#64) 1 ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1104, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : m ⊨ memRegion (sp + 1112#64) 1 ∗
      (localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗ ((sp + 1104#64) ↦₆₄ u1104) ∗
       (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
        memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ R)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1112, hm3⟩ := exists_word8_of_memRegion_1 hm3
  refine ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, ?_⟩
  convert hm3 using 1; sep_ac_rfl

theorem identityKeys_step2_recombine (sp : BitVec 64) (ik : IdentityKey) (w2 : BitVec 64) (b31 : BitVec 8) :
    (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ ik.publicKey.bytes.toList) ∗
     memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
     ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ⊢
    memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 846 := by
  have hlen : ik.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
  refine Entails.trans
    (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
    (sepConj_mono (hlen ▸ pointsToBytes_entails_memRegion (sp + 401#64) _)
    (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 1104#64) w2)
    (sepConj_mono_left (pointsTo8_entails_memRegion (sp + 1112#64) b31))))))) ?_
  rw [show sp + 1113#64 = (sp + 1112#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 1112#64) 1 167 (by decide),
      show sp + 1112#64 = (sp + 1104#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 1104#64) 8 168 (by decide),
      show sp + 1104#64 = (sp + 434#64) + 670#64 by bv_omega,
      ← memRegion_split (sp + 434#64) 670 176 (by decide),
      show sp + 433#64 = (sp + 401#64) + 32#64 by bv_omega,
      ← sepConj_assoc (memRegion (sp + 401#64) 32),
      ← memRegion_split (sp + 401#64) 32 1 (by decide),
      show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
      ← sepConj_assoc (memRegion (sp + 400#64) 1),
      ← memRegion_split (sp + 400#64) 1 33 (by decide)]
  exact Entails.refl _

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
