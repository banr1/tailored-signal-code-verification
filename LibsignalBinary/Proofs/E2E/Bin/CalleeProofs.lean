/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.StoreNew.Proof
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.RunAssembly.TryFromAssembly
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Wrapper Callee Proofs

Proves the `libsignal_e2e` wrapper-layer direct callee contracts:
`<IdentityKey>::decode` (`0x0ae58`), `session_signal_message_parse` (`0x3dab8`),
`<InMemSignedPreKeyStore>::new` (`0x127d8`), and `<InMemIdentityKeyStore>::new` (`0x0c238`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## `session_signal_message_parse` (`0x3dab8`) -/

gen_decodes libsignalSessionCode_tree parseSignalMessage [raw (ls_off% "session_signal_message_parse")]

theorem session_signal_message_parse_tryFrom_ok (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + parseSignalMessageOff)
      (tryFromSpec A img) := by
  have hfetch :=
    libsignalSessionCode_fetch_fnAddr_entry (b := img.base)
      (H := Rust.withPanics (tripleRatchetExterns C ctl abs))
      parseSignalMessage_fnOff (by decide) (ls_decode% parseSignalMessage (ls_off% "session_signal_message_parse"))
  have hfn :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr parseSignalMessageName =
        img.base + parseSignalMessageOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, parseSignalMessage_fnOff]
  rw [hfn] at hfetch
  have htarget :
      img.base + parseSignalMessageOff + 0xfffffffffffe7d80#64 =
        (tripleRatchetProgAt img.base C ctl abs).fnAddr tryFromName := by
    dsimp only [tripleRatchetProgAt, parseSignalMessageOff]
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")]
    bv_lin
  have htry := TryFromAssembly.tryFrom_run_closed C A ctl S abs img hH himg
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg,
      entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg tryFromName]
    at htry
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg]
  exact subroutine_ok_of_b hfetch htarget rfl
    (by intro x s pc; cases s; simp only [tryFromSpec, Spec.inImage, Obj.Image.FrozenLoaded, State.setPC]; rfl)
    htry

theorem session_signal_message_parse_ok (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hH : TripleRatchetHooks C A S abs) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + parseSignalMessageOff)
      (parseSignalMessageSpec A img) := by
  have htry := session_signal_message_parse_tryFrom_ok C A S img ctl abs hH himg
  refine subroutine_ok_outcome_intro ?_
  intro ⟨ret, ctPtr, ctext⟩ R s0 hpc hrun hpre hal
  have hpre' : s0.mem ⊨ (tryFromSpec A img).pre ⟨ctPtr, ctext, ret⟩ s0 ∗ R := by
    dsimp only [parseSignalMessageSpec, tryFromSpec, Spec.inImage, tryFromStack] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hF, ⟨hx8, hx0, hx1, hlen⟩, hmem⟩
    refine ⟨hF, ⟨hx0, hx1, hlen, hx8⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine htry.mono_outcome ⟨ctPtr, ctext, ret⟩ R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [tryFromSpec, parseSignalMessageSpec, Spec.inImage, tryFromStack] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    convert hpost using 1; ac_rfl
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-! ## `PublicKey::try_from` on 33-Byte `Role.idPubWire` -/

def pkTryFromLen33Spec : Spec (BitVec 64 × BitVec 64 × Role) where
  pre := fun (out, keyPtr, r) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ₛ r.idPubWire) ∗ memRegion out 40
  post := fun (out, keyPtr, r) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (keyPtr ↦ₛ r.idPubWire) ∗
      (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗
      memRegion (out + 33#64) 7

theorem role_idPubWire_eq (r : Role) :
    r.idPubWire = 5#8 :: r.idKey.publicKey.bytes.toList := by
  cases r <;> rfl

theorem role_idKey_bytes_length (r : Role) :
    r.idKey.publicKey.bytes.toList.length = 32 := by
  cases r <;> decide

theorem pkTryFrom_len33_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr pkTryFromName) pkTryFromLen33Spec := by
  simp only [pkTryFromLen33Spec]
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 0 48
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 196 76
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, keyPtr, r⟩ := g
  dsimp only at *
  subst out keyPtr
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := r.idKey.publicKey.bytes.toList)
      (role_idKey_bytes_length r)
  rw [role_idPubWire_eq r, pointsToBytes_cons,
      hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
      PublicKeyTryFrom.memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
  wp_pull_exists
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_done

/-! ## `<IdentityKey>::decode` (`0x0ae58`) -/

theorem pk_try_from_len33_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pkTryFromName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) pkTryFromLen33Spec :=
  inImage_ok_at hk (pkTryFrom_len33_ok b C ctl abs)

gen_decodes libsignalSessionCode_tree identityKeyDecode [(ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode") → (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" + 36), (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" + 64) → (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" + 168)]

private def remoteKeyChunks (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

private theorem sevenLo_eq_sevenHi (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenLo_eq_sevenHi a b0 b1 b2 b3 b4 b5 b6)

private theorem truncate16_zeroExtend32 (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by omega
  simp [hi]

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

private theorem exists_remoteKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = remoteKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8),
    pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (hle 4 (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (hle 5 (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (hle 6 (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (hle 7 (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (hle 9 (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (hle 13 (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (hle 15 (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (hle 23 (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (hle 31 (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (hle 32 (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (hle 4 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (hle 5 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (hle 6 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (hle 7 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (hle 9 (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (hle 13 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (hle 15 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (hle 23 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (hle 31 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (hle 32 (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [remoteKeyChunks, pack32, BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunks_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (ret + 8#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗
      ((ret + 15#64) ↦₁₆ v7) ∗ ((ret + 17#64) ↦₃₂ v9) ∗ ((ret + 21#64) ↦₁₆ v13) ∗
      ((ret + 23#64) ↦₆₄ v15) ∗ ((ret + 31#64) ↦₆₄ v23) ∗ ((ret + 39#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunks_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (sp - 87#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗
      ((sp - 80#64) ↦₁₆ v7) ∗ ((sp - 78#64) ↦₃₂ v9) ∗ ((sp - 74#64) ↦₁₆ v13) ∗
      ((sp - 72#64) ↦₆₄ v15) ∗ ((sp - 64#64) ↦₆₄ v23) ∗ ((sp - 56#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  have h83 : sp - 87#64 + 4#64 = sp - 83#64 := by bv_omega
  have h82 : sp - 87#64 + 5#64 = sp - 82#64 := by bv_omega
  have h81 : sp - 87#64 + 6#64 = sp - 81#64 := by bv_omega
  have h80 : sp - 87#64 + 7#64 = sp - 80#64 := by bv_omega
  have h78 : sp - 87#64 + 9#64 = sp - 78#64 := by bv_omega
  have h74 : sp - 87#64 + 13#64 = sp - 74#64 := by bv_omega
  have h72 : sp - 87#64 + 15#64 = sp - 72#64 := by bv_omega
  have h64 : sp - 87#64 + 23#64 = sp - 64#64 := by bv_omega
  have h56 : sp - 87#64 + 31#64 = sp - 56#64 := by bv_omega
  rw [h83, h82, h81, h80, h78, h74, h72, h64, h56]

private theorem sevenLo_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗ rest) =
      (((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
       ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 87#64) (sp - 86#64) (sp - 85#64) (sp - 84#64)
    (sp - 83#64) (sp - 82#64) (sp - 81#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗ rest) =
      (((ret + 8#64) ↦₈ b0) ∗ ((ret + 9#64) ↦₈ b1) ∗ ((ret + 10#64) ↦₈ b2) ∗
       ((ret + 11#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 8#64) (ret + 9#64) (ret + 10#64) (ret + 11#64)
    (ret + 12#64) (ret + 13#64) (ret + 14#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sp_88_four_bytes (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗ rest) =
      (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗ rest) := by
  have h87 : sp - 87#64 = sp - 88#64 + 1#64 := by bv_omega
  have h86 : sp - 86#64 = sp - 88#64 + 2#64 := by bv_omega
  have h85 : sp - 85#64 = sp - 88#64 + 3#64 := by bv_omega
  rw [h87, h86, h85, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sp_84_split_16 (sp : BitVec 64) (b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) =
      (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5)) ∗ rest) := by
  have h82 : sp - 82#64 = sp - 84#64 + 2#64 := by bv_omega
  rw [h82, ← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16, ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_40_identityKeyDecode_split (ret : BitVec 64) :
    memRegion ret 40 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 32, (ret + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (ret + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (ret + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (ret + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 16, (ret + 15#64) ↦₁₆ r15) ∗
      (∃∗ r17 : BitVec 32, (ret + 17#64) ↦₃₂ r17) ∗
      (∃∗ r21 : BitVec 16, (ret + 21#64) ↦₁₆ r21) ∗
      (∃∗ r23 : BitVec 64, (ret + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 64, (ret + 31#64) ↦₆₄ r31) ∗
      (∃∗ r39 : BitVec 8, (ret + 39#64) ↦₈ r39) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 32)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 28)
        (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 27)
        (b' := ret + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 26)
        (b' := ret + 14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 25)
        (b' := ret + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 2) (k := 23)
        (b' := ret + 17#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 4) (k := 19)
        (b' := ret + 21#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 21#64) (n := 2) (k := 17)
        (b' := ret + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 23#64) (n := 8) (k := 9)
        (b' := ret + 31#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 31#64) (n := 8) (k := 1)
        (b' := ret + 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret, memRegion_four (ret + 8#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_two (ret + 15#64), memRegion_four (ret + 17#64), memRegion_two (ret + 21#64),
      ProofLib.memRegion_eight (ret + 23#64), ProofLib.memRegion_eight (ret + 31#64), memRegion_one (ret + 39#64)]

private theorem stackAt_identityKeyDecode_split (sp : BitVec 64) :
    stackAt sp 0x60 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s56 : BitVec 8, (sp - 40#64) ↦₈ s56) ∗
      memRegion (sp - 39#64) 7 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ s88 : BitVec 32, (sp - 8#64) ↦₃₂ s88) ∗
      (∃∗ s92 : BitVec 16, (sp - 4#64) ↦₁₆ s92) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x60 = 96#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 40) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 1) (k := 39)
        (b' := sp - 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 48#64), memRegion_one (sp - 40#64),
      (ProofLib.memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem memRegion_sp_88_40_split (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ k0 : BitVec 32, (sp - 88#64) ↦₃₂ k0) ∗
      (∃∗ k4 : BitVec 16, (sp - 84#64) ↦₁₆ k4) ∗
      (∃∗ k6 : BitVec 16, (sp - 82#64) ↦₁₆ k6) ∗
      (∃∗ k8 : BitVec 16, (sp - 80#64) ↦₁₆ k8) ∗
      (∃∗ k10 : BitVec 32, (sp - 78#64) ↦₃₂ k10) ∗
      (∃∗ k14 : BitVec 16, (sp - 74#64) ↦₁₆ k14) ∗
      (∃∗ k16 : BitVec 64, (sp - 72#64) ↦₆₄ k16) ∗
      (∃∗ k24 : BitVec 64, (sp - 64#64) ↦₆₄ k24) ∗
      (∃∗ k32 : BitVec 8, (sp - 56#64) ↦₈ k32) ∗
      memRegion (sp - 55#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 36)
        (b' := sp - 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 2) (k := 34)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 2) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 2) (k := 30)
        (b' := sp - 78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 4) (k := 26)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 7)
        (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 88#64), memRegion_two (sp - 84#64), memRegion_two (sp - 82#64),
      memRegion_two (sp - 80#64), memRegion_four (sp - 78#64), memRegion_two (sp - 74#64),
      ProofLib.memRegion_eight (sp - 72#64), ProofLib.memRegion_eight (sp - 64#64), memRegion_one (sp - 56#64)]

set_option maxHeartbeats 800000 in
theorem identityKey_decode_tripleRatchetProgAt_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr identityKeyDecodeName)
      identityKeyDecodeSpec := by
  simp only [identityKeyDecodeSpec]
  have htry := pk_try_from_len33_ok_at b C ctl abs
    identityKeyDecodeName (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" - ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode"))
    (by rw [identityKeyDecode_fnOff, (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")])
  simp only [pkTryFromLen33Spec] at htry
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode") (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")) 0 40
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode") (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")) 64 108
  dsimp only [tripleRatchetProgAt, identityKeyDecodeName, BitVec.ofNat_eq_ofNat] at htry ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::identity_key::IdentityKey>::decode" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ret, keyPtr, r⟩ := x
  dsimp only at *
  subst ret keyPtr
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
    exists_remoteKeyChunks_of_length_32 (role_idKey_bytes_length r)
  rw [memRegion_40_identityKeyDecode_split (s0.readReg64 (Reg.gpr 8#5)),
      hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
      remoteKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5)),
      stackAt_identityKeyDecode_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_steps
  wp_apply
  rw [hchunks (s0.sp - 87#64), remoteKeyChunks_sp_87 s0.sp]
  wp_steps
  rw [sevenLo_sp_87 s0.sp]
  wp_steps
  simp only [sepConj_assoc]
  rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5)),
      sp_88_four_bytes s0.sp,
      sp_84_split_16 s0.sp]
  wp_steps
  try rw [truncate16_zeroExtend32]
  try rw [truncate16_zeroExtend32]
  try rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
  try rw [memRegion_sp_88_40_split s0.sp]
  wp_done

theorem identityKey_decode_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + identityKeyDecodeOff)
      (identityKeyDecodeSpec.inImage img) := by
  have hfn : (tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyDecodeName =
      img.base + identityKeyDecodeOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, identityKeyDecode_fnOff]
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg, ← hfn]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (identityKey_decode_tripleRatchetProgAt_ok img.base C ctl abs)

/-! ## `<InMemSignedPreKeyStore>::new` (`0x127d8`) and `<InMemIdentityKeyStore>::new` (`0x0c238`) -/

private theorem storeNew_tlsKeysInitAt_eq (t k0 k1 : BitVec 64) :
    StoreNew.tlsKeysInitAt t k0 k1 = tlsKeysInitAt t k0 k1 := rfl

private theorem storeNew_tlsKeysAt_eq (t : BitVec 64) (st : Option (BitVec 64 × BitVec 64)) :
    StoreNew.tlsKeysAt t st = tlsKeysAt t st := by
  cases st <;> rfl

private theorem storeNew_emptyHashMapAt_eq (ctrlPtr out k0 k1 : BitVec 64) :
    StoreNew.emptyHashMapAt ctrlPtr out k0 k1 = emptyHashMapAt ctrlPtr out k0 k1 := rfl

private theorem storeNew_emptyIdentityKeyStoreAt_eq (ctrlPtr out k0 k1 : BitVec 64)
    (kpBytes : List (BitVec 8)) (regId : BitVec 32) :
    StoreNew.emptyIdentityKeyStoreAt ctrlPtr out k0 k1 kpBytes regId =
      emptyIdentityKeyStoreAt ctrlPtr out k0 k1 kpBytes regId := rfl

private theorem role_keyPairBytes_length (r : Role) :
    r.keyPairBytes.length = 64 := by
  cases r <;> decide

theorem inMemSessionStore_new_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + inMemSessionStoreNewOff)
      (sessionStoreNewSpec img) := by
  have hrs := StoreNew.sessionStore_new_ok (C := C) (ctl := ctl) himg hRk
  rw [StoreNew.inMemSignedPreKeyStoreNew_addr_eq himg] at hrs
  refine subroutine_ok_refine hrs fun ⟨out, st⟩ R s0 hpre => ?_
  refine ⟨⟨out, st⟩, ?_, fun sf hpost => ?_⟩
  · simpa only [sessionStoreNewSpec, StoreNew.sessionStoreNewSpec, Spec.inImage,
      storeNew_tlsKeysAt_eq, StoreNew.tlsKeysTpoff, StoreNew.inMemSessionStoreNewStack,
      StoreNew.inMemSessionStoreNewFrame] using hpre
  · simp only [StoreNew.sessionStoreNewSpec, sessionStoreNewSpec, Spec.inImage,
      storeNew_tlsKeysInitAt_eq, StoreNew.tlsKeysTpoff, StoreNew.emptyCtrlOff,
      StoreNew.inMemSessionStoreNewStack, StoreNew.inMemSessionStoreNewFrame,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    cases st with
    | none =>
      simp only [storeNew_emptyHashMapAt_eq] at hpost
      exact hpost
    | some ks =>
      rcases ks with ⟨k0, k1⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨k0, k1, ?_⟩
      simpa only [storeNew_emptyHashMapAt_eq, sepConj_assoc] using hpost

theorem inMemIdentityKeyStore_new_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + inMemIdentityStoreNewOff)
      (identityStoreNewSpec img) := by
  have hrs := StoreNew.identityStore_new_ok (C := C) (ctl := ctl) himg hRk
  rw [StoreNew.inMemIdentityKeyStoreNew_addr_eq himg] at hrs
  refine subroutine_ok_refine hrs fun ⟨out, kpPtr, me, st⟩ R s0 hpre => ?_
  refine ⟨⟨out, kpPtr, me.keyPairBytes, 0#32, st⟩, ?_, fun sf hpost => ?_⟩
  · simp only [identityStoreNewSpec, StoreNew.identityStoreNewSpec, Spec.inImage,
      storeNew_tlsKeysAt_eq, StoreNew.tlsKeysTpoff, StoreNew.inMemIdentityStoreNewStack,
      StoreNew.inMemIdentityStoreNewFrame, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hF, ⟨hx8, hx0, hx1⟩, hmem⟩
    exact ⟨hF, ⟨hx8, hx0, hx1, role_keyPairBytes_length me⟩, hmem⟩
  · simp only [StoreNew.identityStoreNewSpec, identityStoreNewSpec, Spec.inImage,
      storeNew_tlsKeysInitAt_eq, StoreNew.tlsKeysTpoff, StoreNew.emptyCtrlOff,
      StoreNew.inMemIdentityStoreNewStack, StoreNew.inMemIdentityStoreNewFrame,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    refine ⟨htr, ?_⟩
    cases st with
    | none =>
      simp only [storeNew_emptyIdentityKeyStoreAt_eq] at hpost
      exact hpost
    | some ks =>
      rcases ks with ⟨k0, k1⟩
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨k0, k1, ?_⟩
      simpa only [storeNew_emptyIdentityKeyStoreAt_eq, sepConj_assoc] using hpost

end CryptoVerification.E2E.Bin



