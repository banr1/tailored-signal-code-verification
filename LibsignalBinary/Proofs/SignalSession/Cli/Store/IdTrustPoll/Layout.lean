/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
public import LibsignalBinary.Specifications.RecordCodecsBinary
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit -- shake: keep

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## 1. Symbolic relative callee offsets (layout-independent) -/

theorem identityKeyDecode_fnOff :
    libsignalSessionCode.fnOff RecordCodecsBinary.identityKeyDecodeName =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode")

theorem publicKeyEq_fnOff :
    libsignalSessionCode.fnOff Getters.publicKeyEqName =
      num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dirGetName =
      (tripleRatchetProgAtExt b ext).fnAddr idTrustPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
          "<libsignal_cli::stores::Dir>::get") := by
  have h1 := idTrustPoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustPollName, dirGetName, h1, h2]
  bv_omega

theorem identityKeyDecode_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr RecordCodecsBinary.identityKeyDecodeName =
      (tripleRatchetProgAtExt b ext).fnAddr idTrustPollName -
        bv% (ls_rel%
          "<libsignal_protocol::identity_key::IdentityKey>::decode"
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") := by
  have h1 := idTrustPoll_fnOff
  have h2 := identityKeyDecode_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustPollName,
    RecordCodecsBinary.identityKeyDecodeName, h1, h2]
  bv_omega

theorem publicKeyEq_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr Getters.publicKeyEqName =
      (tripleRatchetProgAtExt b ext).fnAddr idTrustPollName -
        bv% (ls_rel%
          "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") := by
  have h1 := idTrustPoll_fnOff
  have h2 := publicKeyEq_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idTrustPollName,
    Getters.publicKeyEqName, h1, h2]
  bv_omega

theorem dealloc_fnOff_rel :
    libsignalSessionCode.fnOff idTrustPollName +
      num% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
        "__rustc::__rust_dealloc") =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by
  rw [idTrustPoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")]

/-! ## 2. Pure BitVec & model helpers -/

theorem publicKey_beq_eq_decide (ik1 ik2 : IdentityKey) :
    (ik1.publicKey == ik2.publicKey) = decide (ik1 = ik2) := by
  cases ik1 with | mk pk1 =>
  cases ik2 with | mk pk2 =>
  by_cases h : pk1 = pk2
  · subst h; simp
  · have hne : (⟨pk1⟩ : IdentityKey) ≠ ⟨pk2⟩ := fun heq => h (IdentityKey.mk.inj heq)
    have hbeq : (pk1 == pk2) = false := beq_false_of_ne h
    rw [hbeq, decide_eq_false hne]

theorem cons_len_bv_ne_zero {b : BitVec 8} {bs : List (BitVec 8)}
    (hlt : (b :: bs).length < 2 ^ 63) :
    BitVec.ofNat 64 (b :: bs).length ≠ 0#64 := by
  intro heq
  have h0 : (BitVec.ofNat 64 (b :: bs).length).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h0
  simp at h0

theorem cap_ne_zero_of_cons {b : BitVec 8} {bs : List (BitVec 8)} {cap : BitVec 64}
    (hle : (b :: bs).length ≤ cap.toNat) :
    cap ≠ 0#64 := by
  intro h0
  subst h0
  simp at hle

/-! ## 3. Stack & region splits -/

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_idTrustPoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 192 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 192) =
      stackAt (sp - 192#64) calleeStk ∗ cells (sp - 192#64) 24 :=
  ProofLib.stackAt_split_cells sp calleeStk 24 hhi

private theorem memRegion_16_eq_stackFrameFor_eq (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor,
    (ls_lemma% frameBytes "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq"),
    reduceStackFrameAt]

private theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor,
    (ls_lemma% frameBytes "<[u8] as subtle::ConstantTimeEq>::ct_eq"),
    reduceStackFrameAt]

theorem stackAt_64_eq_pkEq_frames (sp : BitVec 64) :
    stackAt sp 64 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) := by
  simp only [stackAt]
  rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  have e48 : sp - 64#64 = sp - 16#64 - 48#64 := by bv_omega
  rw [e48, sepConj_comm, memRegion_16_eq_stackFrameFor_eq, memRegion_48_eq_stackFrameFor_ct_eq]

/-! ## 4. `vecU8At` & `protocolAddressAt` exposure (works uniformly for `cap = 0` and `cap ≠ 0`) -/

def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (n : Nat) : SepProp :=
  if cap = 0#64 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 n) (cap.toNat - n)

theorem vecU8At_eq_expose (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs.length := by
  unfold vecU8At vecHeader vecU8BufRest
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  simp only [h0]
  by_cases hc : cap = 0#64
  · subst hc
    by_cases hbs : bs = []
    · subst hbs
      simp only [ite_true, pointsToBytes_nil, emp_sepConj, sepConj_emp]
      ac_rfl
    · have hf :
        (bs.length ≤ (0#64 : BitVec 64).toNat ∧
          (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = False := by
        simp [hbs]
      rw [hf]
      simp only [pure_false_sepConj, sepConj_pure_false]
  · simp only [hc, ite_false]
    ac_rfl

theorem protocolAddressAt_eq_expose (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
        (a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗ vecU8BufRest A g.name.cap g.name.ptr g.name.bytes.length ∗
        ((a + 24#64) ↦₈ g.device) ∗ memRegion (a + 25#64) 7 := by
  dsimp only [protocolAddressAt, vecGhostAt]
  rw [vecU8At_eq_expose]
  ac_rfl

/-! ## 5. Unaligned 7-byte swap (`sevenLo ↔ sevenHi`), 64-bit word byte splits, and 32-byte key chunks -/

theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  have hbase :
      ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗
        ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗
        ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
    rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
    simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  simpa only [sepConj_assoc] using congrArg (· ∗ rest) hbase

theorem sevenLo_any (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (w : BitVec 32) (b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ w) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ w.extractLsb' 0 8) ∗ (a1 ↦₈ w.extractLsb' 8 8) ∗ (a2 ↦₈ w.extractLsb' 16 8) ∗
        (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8)) ∗ rest) := by
  have hw : w = w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by bv_bits
  conv_lhs => rw [hw]
  exact sevenLo_eq_sevenHi' a a1 a2 a3 a4 a5 a6 h1 h2 h3 h4 h5 h6 _ _ _ _ b4 b5 b6 rest

theorem sevenHi_any (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 : BitVec 8) (w' : BitVec 32) (rest : SepProp) :
    ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ w') ∗ rest) =
      ((a ↦₃₂ (w'.extractLsb' 0 8 ++ b2 ++ b1 ++ b0)) ∗
        (a4 ↦₈ w'.extractLsb' 8 8) ∗ (a5 ↦₈ w'.extractLsb' 16 8) ∗
        (a6 ↦₈ w'.extractLsb' 24 8) ∗ rest) := by
  have hw : w' = w'.extractLsb' 24 8 ++ w'.extractLsb' 16 8 ++
      w'.extractLsb' 8 8 ++ w'.extractLsb' 0 8 := by bv_bits
  conv_lhs => rw [hw]
  exact (sevenLo_eq_sevenHi' a a1 a2 a3 a4 a5 a6 h1 h2 h3 h4 h5 h6 b0 b1 b2 _ _ _ _ rest).symm

theorem sevenLo_sp_72 (sp : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 72#64) ↦₃₂ w) ∗
      ((sp - 68#64) ↦₈ b4) ∗ ((sp - 67#64) ↦₈ b5) ∗ ((sp - 66#64) ↦₈ b6) ∗ rest) =
    (((sp - 72#64) ↦₈ w.extractLsb' 0 8) ∗ ((sp - 71#64) ↦₈ w.extractLsb' 8 8) ∗
      ((sp - 70#64) ↦₈ w.extractLsb' 16 8) ∗
      ((sp - 69#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8)) ∗ rest) :=
  sevenLo_any (sp - 72#64) (sp - 71#64) (sp - 70#64) (sp - 69#64)
    (sp - 68#64) (sp - 67#64) (sp - 66#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    w b4 b5 b6 rest

theorem sevenHi_sp_72 (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (w' : BitVec 32) (rest : SepProp) :
    (((sp - 72#64) ↦₈ b0) ∗ ((sp - 71#64) ↦₈ b1) ∗ ((sp - 70#64) ↦₈ b2) ∗
      ((sp - 69#64) ↦₃₂ w') ∗ rest) =
    (((sp - 72#64) ↦₃₂ (w'.extractLsb' 0 8 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 68#64) ↦₈ w'.extractLsb' 8 8) ∗ ((sp - 67#64) ↦₈ w'.extractLsb' 16 8) ∗
      ((sp - 66#64) ↦₈ w'.extractLsb' 24 8) ∗ rest) :=
  sevenHi_any (sp - 72#64) (sp - 71#64) (sp - 70#64) (sp - 69#64)
    (sp - 68#64) (sp - 67#64) (sp - 66#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 w' rest

theorem sevenLo_sp_151 (sp : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 151#64) ↦₃₂ w) ∗
      ((sp - 147#64) ↦₈ b4) ∗ ((sp - 146#64) ↦₈ b5) ∗ ((sp - 145#64) ↦₈ b6) ∗ rest) =
    (((sp - 151#64) ↦₈ w.extractLsb' 0 8) ∗ ((sp - 150#64) ↦₈ w.extractLsb' 8 8) ∗
      ((sp - 149#64) ↦₈ w.extractLsb' 16 8) ∗
      ((sp - 148#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8)) ∗ rest) :=
  sevenLo_any (sp - 151#64) (sp - 150#64) (sp - 149#64) (sp - 148#64)
    (sp - 147#64) (sp - 146#64) (sp - 145#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    w b4 b5 b6 rest

theorem sevenLo_out_41 (out : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((out + 41#64) ↦₃₂ w) ∗
      ((out + 45#64) ↦₈ b4) ∗ ((out + 46#64) ↦₈ b5) ∗ ((out + 47#64) ↦₈ b6) ∗ rest) =
    (((out + 41#64) ↦₈ w.extractLsb' 0 8) ∗ ((out + 42#64) ↦₈ w.extractLsb' 8 8) ∗
      ((out + 43#64) ↦₈ w.extractLsb' 16 8) ∗
      ((out + 44#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8)) ∗ rest) :=
  sevenLo_any (out + 41#64) (out + 42#64) (out + 43#64) (out + 44#64)
    (out + 45#64) (out + 46#64) (out + 47#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    w b4 b5 b6 rest

theorem sevenLo_sp_72' (sp : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) :
    (((sp - 72#64) ↦₃₂ w) ∗
      ((sp - 68#64) ↦₈ b4) ∗ ((sp - 67#64) ↦₈ b5) ∗ ((sp - 66#64) ↦₈ b6)) =
    (((sp - 72#64) ↦₈ w.extractLsb' 0 8) ∗ ((sp - 71#64) ↦₈ w.extractLsb' 8 8) ∗
      ((sp - 70#64) ↦₈ w.extractLsb' 16 8) ∗
      ((sp - 69#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8))) := by
  simpa only [sepConj_emp] using sevenLo_sp_72 sp w b4 b5 b6 emp

theorem sevenHi_sp_72' (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (w' : BitVec 32) :
    (((sp - 72#64) ↦₈ b0) ∗ ((sp - 71#64) ↦₈ b1) ∗ ((sp - 70#64) ↦₈ b2) ∗
      ((sp - 69#64) ↦₃₂ w')) =
    (((sp - 72#64) ↦₃₂ (w'.extractLsb' 0 8 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 68#64) ↦₈ w'.extractLsb' 8 8) ∗ ((sp - 67#64) ↦₈ w'.extractLsb' 16 8) ∗
      ((sp - 66#64) ↦₈ w'.extractLsb' 24 8)) := by
  simpa only [sepConj_emp] using sevenHi_sp_72 sp b0 b1 b2 w' emp

theorem sevenLo_sp_151' (sp : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) :
    (((sp - 151#64) ↦₃₂ w) ∗
      ((sp - 147#64) ↦₈ b4) ∗ ((sp - 146#64) ↦₈ b5) ∗ ((sp - 145#64) ↦₈ b6)) =
    (((sp - 151#64) ↦₈ w.extractLsb' 0 8) ∗ ((sp - 150#64) ↦₈ w.extractLsb' 8 8) ∗
      ((sp - 149#64) ↦₈ w.extractLsb' 16 8) ∗
      ((sp - 148#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8))) := by
  simpa only [sepConj_emp] using sevenLo_sp_151 sp w b4 b5 b6 emp

theorem sevenLo_out_41' (out : BitVec 64) (w : BitVec 32) (b4 b5 b6 : BitVec 8) :
    (((out + 41#64) ↦₃₂ w) ∗
      ((out + 45#64) ↦₈ b4) ∗ ((out + 46#64) ↦₈ b5) ∗ ((out + 47#64) ↦₈ b6)) =
    (((out + 41#64) ↦₈ w.extractLsb' 0 8) ∗ ((out + 42#64) ↦₈ w.extractLsb' 8 8) ∗
      ((out + 43#64) ↦₈ w.extractLsb' 16 8) ∗
      ((out + 44#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ w.extractLsb' 24 8))) := by
  simpa only [sepConj_emp] using sevenLo_out_41 out w b4 b5 b6 emp

theorem pointsTo64_sp_152_split (sp : BitVec 64) (v : BitVec 64) :
    ((sp - 152#64) ↦₆₄ v) =
      ((sp - 152#64) ↦₈ v.extractLsb' 0 8) ∗
      ((sp - 151#64) ↦₃₂
        (v.extractLsb' 32 8 ++ v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8)) ∗
      ((sp - 147#64) ↦₈ v.extractLsb' 40 8) ∗
      ((sp - 146#64) ↦₈ v.extractLsb' 48 8) ∗
      ((sp - 145#64) ↦₈ v.extractLsb' 56 8) := by
  rw [pointsTo64_eq_pointsToBytes, ← pointsToBytes4_eq_pointsTo32]
  dsimp only [unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
  have h1 : sp - 152#64 + 1#64 = sp - 151#64 := by bv_omega
  have h2 : sp - 151#64 + 1#64 = sp - 150#64 := by bv_omega
  have h3 : sp - 150#64 + 1#64 = sp - 149#64 := by bv_omega
  have h4 : sp - 149#64 + 1#64 = sp - 148#64 := by bv_omega
  have h5 : sp - 148#64 + 1#64 = sp - 147#64 := by bv_omega
  have h6 : sp - 147#64 + 1#64 = sp - 146#64 := by bv_omega
  have h7 : sp - 146#64 + 1#64 = sp - 145#64 := by bv_omega
  rw [h1, h2, h3, h4, h5, h6, h7]

theorem pointsTo64_out_40_any_eq (out : BitVec 64) (v : BitVec 64)
    (b40 b41 b42 b43 : BitVec 8) (w44 : BitVec 32)
    (hv : w44 ++ b43 ++ b42 ++ b41 ++ b40 = v) :
    (((out + 40#64) ↦₈ b40) ∗ ((out + 41#64) ↦₈ b41) ∗
      ((out + 42#64) ↦₈ b42) ∗ ((out + 43#64) ↦₈ b43) ∗ ((out + 44#64) ↦₃₂ w44)) =
    ((out + 40#64) ↦₆₄ v) := by
  subst hv
  have hw44 : w44 = w44.extractLsb' 24 8 ++ w44.extractLsb' 16 8 ++
      w44.extractLsb' 8 8 ++ w44.extractLsb' 0 8 := by bv_bits
  conv_lhs => arg 2; arg 2; arg 2; arg 2; rw [hw44]
  rw [← pointsToBytes4_eq_pointsTo32, pointsTo64_eq_pointsToBytes]
  have e0 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 0 8 = b40 := by bv_bits
  have e1 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 8 8 = b41 := by bv_bits
  have e2 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 16 8 = b42 := by bv_bits
  have e3 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 24 8 = b43 := by bv_bits
  have e4 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 32 8 = w44.extractLsb' 0 8 := by bv_bits
  have e5 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 40 8 = w44.extractLsb' 8 8 := by bv_bits
  have e6 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 48 8 = w44.extractLsb' 16 8 := by bv_bits
  have e7 : (w44 ++ b43 ++ b42 ++ b41 ++ b40).extractLsb' 56 8 = w44.extractLsb' 24 8 := by bv_bits
  dsimp only [unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7]

theorem pointsTo64_out_8_any_eq (out : BitVec 64) (sCap : BitVec 64)
    (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16) (b15 : BitVec 8)
    (hsCap : b15 ++ h13 ++ w9 ++ b8 = sCap) :
    (((out + 8#64) ↦₈ b8) ∗ ((out + 9#64) ↦₃₂ w9) ∗
      ((out + 13#64) ↦₁₆ h13) ∗ ((out + 15#64) ↦₈ b15)) =
    ((out + 8#64) ↦₆₄ sCap) := by
  subst hsCap
  have hw9 : w9 = w9.extractLsb' 24 8 ++ w9.extractLsb' 16 8 ++
      w9.extractLsb' 8 8 ++ w9.extractLsb' 0 8 := by bv_bits
  have hh13 : ((out + 13#64) ↦₁₆ h13) =
      ((out + 13#64) ↦₈ h13.extractLsb' 0 8) ∗ ((out + 14#64) ↦₈ h13.extractLsb' 8 8) := by
    simp only [pointsTo16, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs => arg 2; arg 1; rw [hw9]
  rw [← pointsToBytes4_eq_pointsTo32, hh13, pointsTo64_eq_pointsToBytes]
  have e0 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 0 8 = b8 := by bv_bits
  have e1 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 8 8 = w9.extractLsb' 0 8 := by bv_bits
  have e2 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 16 8 = w9.extractLsb' 8 8 := by bv_bits
  have e3 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 24 8 = w9.extractLsb' 16 8 := by bv_bits
  have e4 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 32 8 = w9.extractLsb' 24 8 := by bv_bits
  have e5 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 40 8 = h13.extractLsb' 0 8 := by bv_bits
  have e6 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 48 8 = h13.extractLsb' 8 8 := by bv_bits
  have e7 : (b15 ++ h13 ++ w9 ++ b8).extractLsb' 56 8 = b15 := by bv_bits
  dsimp only [unpack64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7]

def pollKeyChunks (a : BitVec 64)
    (w0 : BitVec 32) (w4 : BitVec 16) (b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ w4) ∗ ((a + 6#64) ↦₈ b6) ∗
    ((a + 7#64) ↦₆₄ v7) ∗ ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗
    ((a + 31#64) ↦₈ b31)

private theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

theorem exists_pollKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 : BitVec 32) (w4 : BitVec 16) (b6 : BitVec 8)
      (v7 v15 v23 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pollKeyChunks a w0 w4 b6 v7 v15 v23 b31 := by
  refine ⟨pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8),
    pack16 (bs.getD 4 0#8) (bs.getD 5 0#8),
    bs.getD 6 0#8,
    pack64 (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8)
      (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (by omega),
      pointsToBytes_drop_split _ bs 4 2 (by omega),
      pointsToBytes_drop_split _ bs 6 1 (by omega),
      pointsToBytes_drop_split _ bs 7 8 (by omega),
      pointsToBytes_drop_split _ bs 15 8 (by omega),
      pointsToBytes_drop_split _ bs 23 8 (by omega),
      pointsToBytes_drop_split _ bs 31 1 (by omega)]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (by omega),
      pointsToBytes_take2_eq_pointsTo16 _ bs 4 (by omega),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 7 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (by omega),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (by omega)]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [pollKeyChunks, BitVec.add_assoc, BitVec.reduceAdd]

theorem pollKeyChunks_sp_136 (sp : BitVec 64)
    (w0 : BitVec 32) (w4 : BitVec 16) (b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (b31 : BitVec 8) :
    pollKeyChunks (sp - 136#64) w0 w4 b6 v7 v15 v23 b31 =
      ((sp - 136#64) ↦₃₂ w0) ∗ ((sp - 132#64) ↦₁₆ w4) ∗ ((sp - 130#64) ↦₈ b6) ∗
        ((sp - 129#64) ↦₆₄ v7) ∗ ((sp - 121#64) ↦₆₄ v15) ∗ ((sp - 113#64) ↦₆₄ v23) ∗
        ((sp - 105#64) ↦₈ b31) := by
  dsimp only [pollKeyChunks]
  have e1 : sp - 136#64 + 4#64 = sp - 132#64 := by bv_omega
  have e2 : sp - 136#64 + 6#64 = sp - 130#64 := by bv_omega
  have e3 : sp - 136#64 + 7#64 = sp - 129#64 := by bv_omega
  have e4 : sp - 136#64 + 15#64 = sp - 121#64 := by bv_omega
  have e5 : sp - 136#64 + 23#64 = sp - 113#64 := by bv_omega
  have e6 : sp - 136#64 + 31#64 = sp - 105#64 := by bv_omega
  rw [e1, e2, e3, e4, e5, e6]

theorem pollKeyChunks_sp_144 (sp : BitVec 64)
    (w0 : BitVec 32) (w4 : BitVec 16) (b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (b31 : BitVec 8) :
    pollKeyChunks (sp - 144#64) w0 w4 b6 v7 v15 v23 b31 =
      ((sp - 144#64) ↦₃₂ w0) ∗ ((sp - 140#64) ↦₁₆ w4) ∗ ((sp - 138#64) ↦₈ b6) ∗
        ((sp - 137#64) ↦₆₄ v7) ∗ ((sp - 129#64) ↦₆₄ v15) ∗ ((sp - 121#64) ↦₆₄ v23) ∗
        ((sp - 113#64) ↦₈ b31) := by
  dsimp only [pollKeyChunks]
  have e1 : sp - 144#64 + 4#64 = sp - 140#64 := by bv_omega
  have e2 : sp - 144#64 + 6#64 = sp - 138#64 := by bv_omega
  have e3 : sp - 144#64 + 7#64 = sp - 137#64 := by bv_omega
  have e4 : sp - 144#64 + 15#64 = sp - 129#64 := by bv_omega
  have e5 : sp - 144#64 + 23#64 = sp - 121#64 := by bv_omega
  have e6 : sp - 144#64 + 31#64 = sp - 113#64 := by bv_omega
  rw [e1, e2, e3, e4, e5, e6]

theorem pollKeyChunks_sp_144_of_eq (sp : BitVec 64) {bs : List (BitVec 8)}
    {w0 w0' : BitVec 32} {w4 w4' : BitVec 16} {b6 b6' : BitVec 8}
    {v7 v15 v23 : BitVec 64} {b31 : BitVec 8}
    (hchunks : ∀ a : BitVec 64, (a ↦ₛ bs) = pollKeyChunks a w0 w4 b6 v7 v15 v23 b31)
    (hw0 : w0' = w0) (hw4 : w4' = w4) (hb6 : b6' = b6) :
    (((sp - 144#64) ↦₃₂ w0') ∗ ((sp - 140#64) ↦₁₆ w4') ∗ ((sp - 138#64) ↦₈ b6') ∗
      ((sp - 137#64) ↦₆₄ v7) ∗ ((sp - 129#64) ↦₆₄ v15) ∗ ((sp - 121#64) ↦₆₄ v23) ∗
      ((sp - 113#64) ↦₈ b31)) =
    ((sp - 144#64) ↦ₛ bs) := by
  subst hw0 hw4 hb6
  rw [hchunks (sp - 144#64), pollKeyChunks_sp_144]

theorem sret_48_sp_144_rebuild_split (sp : BitVec 64) :
    memRegion (sp - 144#64) 48 =
      (∃∗ q0 : BitVec 32, (sp - 144#64) ↦₃₂ q0) ∗
      (∃∗ q4 : BitVec 16, (sp - 140#64) ↦₁₆ q4) ∗
      (∃∗ q6 : BitVec 8, (sp - 138#64) ↦₈ q6) ∗
      (∃∗ q7 : BitVec 64, (sp - 137#64) ↦₆₄ q7) ∗
      (∃∗ q15 : BitVec 64, (sp - 129#64) ↦₆₄ q15) ∗
      (∃∗ q23 : BitVec 64, (sp - 121#64) ↦₆₄ q23) ∗
      (∃∗ q31 : BitVec 8, (sp - 113#64) ↦₈ q31) ∗
      memRegion (sp - 112#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 144#64) (n := 4) (k := 44)
        (b' := sp - 140#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 140#64) (n := 2) (k := 42)
        (b' := sp - 138#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 138#64) (n := 1) (k := 41)
        (b' := sp - 137#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 137#64) (n := 8) (k := 33)
        (b' := sp - 129#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 129#64) (n := 8) (k := 25)
        (b' := sp - 121#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 121#64) (n := 8) (k := 17)
        (b' := sp - 113#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 113#64) (n := 1) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 144#64), memRegion_two (sp - 140#64), memRegion_one (sp - 138#64),
      ProofLib.memRegion_eight (sp - 137#64), ProofLib.memRegion_eight (sp - 129#64),
      ProofLib.memRegion_eight (sp - 121#64), memRegion_one (sp - 113#64)]

theorem sp_144_key_fold_48 (sp : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    ((sp - 144#64) ↦ₛ bs) ∗ memRegion (sp - 112#64) 16 ⊢ memRegion (sp - 144#64) 48 := by
  have hent : ((sp - 144#64) ↦ₛ bs) ⊢ memRegion (sp - 144#64) 32 := by
    rw [← h]
    exact IsBlock.entails_memRegion (IsBlock.pointsToBytes (sp - 144#64) bs)
  have h48 := ProofLib.memRegion_split' (b := sp - 144#64) (n := 32) (k := 16)
    (b' := sp - 112#64) rfl (by bv_omega) (by decide)
  rw [h48]
  exact sepConj_mono_left hent

theorem sp_144_ikDec_fold_48 (sp : BitVec 64)
    (tag : BitVec 64) (w0 : BitVec 32) (w4 : BitVec 16) (b6 : BitVec 8)
    (v7 v15 v23 : BitVec 64) (b31 : BitVec 8) :
    ((sp - 144#64) ↦₆₄ tag) ∗
      ((sp - 136#64) ↦₃₂ w0) ∗ ((sp - 132#64) ↦₁₆ w4) ∗ ((sp - 130#64) ↦₈ b6) ∗
      ((sp - 129#64) ↦₆₄ v7) ∗ ((sp - 121#64) ↦₆₄ v15) ∗ ((sp - 113#64) ↦₆₄ v23) ∗
      ((sp - 105#64) ↦₈ b31) ∗ memRegion (sp - 104#64) 8 ⊢
    memRegion (sp - 144#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 40)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 4) (k := 36)
        (b' := sp - 132#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 132#64) (n := 2) (k := 34)
        (b' := sp - 130#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 130#64) (n := 1) (k := 33)
        (b' := sp - 129#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 129#64) (n := 8) (k := 25)
        (b' := sp - 121#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 121#64) (n := 8) (k := 17)
        (b' := sp - 113#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 113#64) (n := 8) (k := 9)
        (b' := sp - 105#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 105#64) (n := 1) (k := 8)
        (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo16 _ _))
        (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
          (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
            (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
              (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
                (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _)))))))))

theorem sp_144_cells4_fold_48 (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((sp - 144#64) ↦₆₄ w0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗
      ((sp - 128#64) ↦₆₄ w2) ∗ ((sp - 120#64) ↦₆₄ w3) ∗
      memRegion (sp - 112#64) 16 ⊢
    memRegion (sp - 144#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 40)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 32)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 24)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
        (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _)))))

theorem sp_144_cells6_fold_48 (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 144#64) ↦₆₄ w0) ∗ ((sp - 136#64) ↦₆₄ w1) ∗
      ((sp - 128#64) ↦₆₄ w2) ∗ ((sp - 120#64) ↦₆₄ w3) ∗
      ((sp - 112#64) ↦₆₄ w4) ∗ ((sp - 104#64) ↦₆₄ w5) ⊢
    memRegion (sp - 144#64) 48 := by
  have h16 : ((sp - 112#64) ↦₆₄ w4) ∗ ((sp - 104#64) ↦₆₄ w5) ⊢ memRegion (sp - 112#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 112#64) (n := 8) (k := 8)
      (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h16))))
    (sp_144_cells4_fold_48 sp w0 w1 w2 w3)

theorem sp_152_fold_64 (sp : BitVec 64) (b5 : BitVec 8) :
    ((sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7 ⊢
      ∃∗ v5 : BitVec 64, (sp - 152#64) ↦₆₄ v5 := by
  rw [← ProofLib.memRegion_eight (sp - 152#64),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 1) (k := 7)
        (b' := sp - 151#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))

theorem sp_151_sevenHi_fold_7 (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (w : BitVec 32) :
    ((sp - 151#64) ↦₈ b0) ∗ ((sp - 150#64) ↦₈ b1) ∗ ((sp - 149#64) ↦₈ b2) ∗
      ((sp - 148#64) ↦₃₂ w) ⊢
    memRegion (sp - 151#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 151#64) (n := 1) (k := 6)
        (b' := sp - 150#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 150#64) (n := 1) (k := 5)
        (b' := sp - 149#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 149#64) (n := 1) (k := 4)
        (b' := sp - 148#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
        (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))))

/-! ## 6. Exact 24-cell stack splits & 48-byte `out` sret splits -/

theorem memRegion_8_eq_1_7_sub (sp off off1 : BitVec 64) (h : sp - off + 1#64 = sp - off1) :
    (∃∗ v : BitVec 64, (sp - off) ↦₆₄ v) =
      (∃∗ b : BitVec 8, (sp - off) ↦₈ b) ∗ memRegion (sp - off1) 7 := by
  rw [← ProofLib.memRegion_eight (sp - off),
      ProofLib.memRegion_split' (b := sp - off) (n := 1) (k := 7)
        (b' := sp - off1) rfl h.symm (by decide),
      memRegion_one (sp - off)]

theorem memRegion_8_sp_72_lo (sp : BitVec 64) :
    (∃∗ v : BitVec 64, (sp - 72#64) ↦₆₄ v) =
      (∃∗ w0 : BitVec 32, (sp - 72#64) ↦₃₂ w0) ∗
      (∃∗ b4 : BitVec 8, (sp - 68#64) ↦₈ b4) ∗
      (∃∗ b5 : BitVec 8, (sp - 67#64) ↦₈ b5) ∗
      (∃∗ b6 : BitVec 8, (sp - 66#64) ↦₈ b6) ∗
      (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7) := by
  rw [← ProofLib.memRegion_eight (sp - 72#64),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 4) (k := 4)
        (b' := sp - 68#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 68#64) (n := 1) (k := 3)
        (b' := sp - 67#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 67#64) (n := 1) (k := 2)
        (b' := sp - 66#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 66#64) (n := 1) (k := 1)
        (b' := sp - 65#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 72#64),
      memRegion_one (sp - 68#64), memRegion_one (sp - 67#64),
      memRegion_one (sp - 66#64), memRegion_one (sp - 65#64)]

theorem memRegion_8_sp_72_hi (sp : BitVec 64) :
    (∃∗ v : BitVec 64, (sp - 72#64) ↦₆₄ v) =
      (∃∗ b0 : BitVec 8, (sp - 72#64) ↦₈ b0) ∗
      (∃∗ b1 : BitVec 8, (sp - 71#64) ↦₈ b1) ∗
      (∃∗ b2 : BitVec 8, (sp - 70#64) ↦₈ b2) ∗
      (∃∗ w3 : BitVec 32, (sp - 69#64) ↦₃₂ w3) ∗
      (∃∗ b7 : BitVec 8, (sp - 65#64) ↦₈ b7) := by
  rw [← ProofLib.memRegion_eight (sp - 72#64),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 1) (k := 7)
        (b' := sp - 71#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 71#64) (n := 1) (k := 6)
        (b' := sp - 70#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 70#64) (n := 1) (k := 5)
        (b' := sp - 69#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 69#64) (n := 4) (k := 1)
        (b' := sp - 65#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 72#64), memRegion_one (sp - 71#64), memRegion_one (sp - 70#64),
      memRegion_four (sp - 69#64), memRegion_one (sp - 65#64)]

theorem cells_24_split (sp : BitVec 64) :
    cells (sp - 192#64) 24 =
      (∃∗ v0 : BitVec 64, (sp - 192#64) ↦₆₄ v0) ∗
      ((∃∗ b1 : BitVec 8, (sp - 184#64) ↦₈ b1) ∗ memRegion (sp - 183#64) 7) ∗
      (∃∗ v2 : BitVec 64, (sp - 176#64) ↦₆₄ v2) ∗
      ((∃∗ b3 : BitVec 8, (sp - 168#64) ↦₈ b3) ∗ memRegion (sp - 167#64) 7) ∗
      (∃∗ v4 : BitVec 64, (sp - 160#64) ↦₆₄ v4) ∗
      ((∃∗ b5 : BitVec 8, (sp - 152#64) ↦₈ b5) ∗ memRegion (sp - 151#64) 7) ∗
      memRegion (sp - 144#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 96#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 88#64) ↦₆₄ s30) ∗
      (∃∗ s27 : BitVec 64, (sp - 80#64) ↦₆₄ s27) ∗
      (∃∗ v72 : BitVec 64, (sp - 72#64) ↦₆₄ v72) ∗
      (∃∗ s26 : BitVec 64, (sp - 64#64) ↦₆₄ s26) ∗
      (∃∗ s25 : BitVec 64, (sp - 56#64) ↦₆₄ s25) ∗
      (∃∗ s24 : BitVec 64, (sp - 48#64) ↦₆₄ s24) ∗
      (∃∗ s23 : BitVec 64, (sp - 40#64) ↦₆₄ s23) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  conv_lhs =>
    rw [show (24 : Nat) = 1 + 23 from rfl, cells_split_sub sp 192 184 1 23,
        show (23 : Nat) = 1 + 22 from rfl, cells_split_sub sp 184 176 1 22,
        show (22 : Nat) = 1 + 21 from rfl, cells_split_sub sp 176 168 1 21,
        show (21 : Nat) = 1 + 20 from rfl, cells_split_sub sp 168 160 1 20,
        show (20 : Nat) = 1 + 19 from rfl, cells_split_sub sp 160 152 1 19,
        show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
        show (18 : Nat) = 6 + 12 from rfl, cells_split_sub sp 144 96 6 12,
        show (12 : Nat) = 1 + 11 from rfl, cells_split_sub sp 96 88 1 11,
        show (11 : Nat) = 1 + 10 from rfl, cells_split_sub sp 88 80 1 10,
        show (10 : Nat) = 1 + 9 from rfl, cells_split_sub sp 80 72 1 9,
        show (9 : Nat) = 1 + 8 from rfl, cells_split_sub sp 72 64 1 8,
        show (8 : Nat) = 1 + 7 from rfl, cells_split_sub sp 64 56 1 7,
        show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6,
        show (6 : Nat) = 1 + 5 from rfl, cells_split_sub sp 48 40 1 5,
        show (5 : Nat) = 1 + 4 from rfl, cells_split_sub sp 40 32 1 4,
        show (4 : Nat) = 1 + 3 from rfl, cells_split_sub sp 32 24 1 3,
        show (3 : Nat) = 1 + 2 from rfl, cells_split_sub sp 24 16 1 2,
        show (2 : Nat) = 1 + 1 from rfl, cells_split_sub sp 16 8 1 1,
        ← memRegion_cells (sp - 144#64) 6 (by decide)]
  cells_unfold
  rw [memRegion_8_eq_1_7_sub sp 184#64 183#64 (by bv_omega),
      memRegion_8_eq_1_7_sub sp 168#64 167#64 (by bv_omega),
      memRegion_8_eq_1_7_sub sp 152#64 151#64 (by bv_omega)]

theorem out_48_pre_split (out : BitVec 64) :
    memRegion out 48 =
      (∃∗ o0 : BitVec 64, out ↦₆₄ o0) ∗
      (∃∗ o8 : BitVec 8, (out + 8#64) ↦₈ o8) ∗
      (∃∗ o9 : BitVec 32, (out + 9#64) ↦₃₂ o9) ∗
      (∃∗ o13 : BitVec 16, (out + 13#64) ↦₁₆ o13) ∗
      (∃∗ o15 : BitVec 8, (out + 15#64) ↦₈ o15) ∗
      (∃∗ o16 : BitVec 64, (out + 16#64) ↦₆₄ o16) ∗
      (∃∗ o24 : BitVec 64, (out + 24#64) ↦₆₄ o24) ∗
      (∃∗ o32 : BitVec 64, (out + 32#64) ↦₆₄ o32) ∗
      (∃∗ o40 : BitVec 8, (out + 40#64) ↦₈ o40) ∗
      (∃∗ w41 : BitVec 32, (out + 41#64) ↦₃₂ w41) ∗
      (∃∗ c4 : BitVec 8, (out + 45#64) ↦₈ c4) ∗
      (∃∗ c5 : BitVec 8, (out + 46#64) ↦₈ c5) ∗
      (∃∗ c6 : BitVec 8, (out + 47#64) ↦₈ c6) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 40)
        (b' := out + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 39)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 9#64) (n := 4) (k := 35)
        (b' := out + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 13#64) (n := 2) (k := 33)
        (b' := out + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 15#64) (n := 1) (k := 32)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
        (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 40#64) (n := 1) (k := 7)
        (b' := out + 41#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 41#64) (n := 4) (k := 3)
        (b' := out + 45#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 45#64) (n := 1) (k := 2)
        (b' := out + 46#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 46#64) (n := 1) (k := 1)
        (b' := out + 47#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, memRegion_one (out + 8#64),
      memRegion_four (out + 9#64), memRegion_two (out + 13#64), memRegion_one (out + 15#64),
      ProofLib.memRegion_eight (out + 16#64), ProofLib.memRegion_eight (out + 24#64),
      ProofLib.memRegion_eight (out + 32#64), memRegion_one (out + 40#64),
      memRegion_four (out + 41#64), memRegion_one (out + 45#64),
      memRegion_one (out + 46#64), memRegion_one (out + 47#64)]

theorem out_ok_fold (A : RustAlloc) (out : BitVec 64) (t : Bool)
    (tag : BitVec 64) (b8 : BitVec 8)
    (o9 : BitVec 32) (o13 : BitVec 16) (o15 : BitVec 8)
    (o16 o24 o32 : BitVec 64)
    (o40 c0 c1 c2 : BitVec 8) (o44 : BitVec 32)
    (htag : tag = 0xFFFFFFFFFFFFFFFE#64)
    (hb8 : b8 = if t then 1#8 else 0#8) :
    ((out ↦₆₄ tag) ∗
      ((out + 8#64) ↦₈ b8) ∗
      ((out + 9#64) ↦₃₂ o9) ∗ ((out + 13#64) ↦₁₆ o13) ∗ ((out + 15#64) ↦₈ o15) ∗
      ((out + 16#64) ↦₆₄ o16) ∗ ((out + 24#64) ↦₆₄ o24) ∗ ((out + 32#64) ↦₆₄ o32) ∗
      ((out + 40#64) ↦₈ o40) ∗
      ((out + 41#64) ↦₈ c0) ∗ ((out + 42#64) ↦₈ c1) ∗ ((out + 43#64) ↦₈ c2) ∗
      ((out + 44#64) ↦₃₂ o44)) ⊢
    idTrustOutAt A out (.ok t) := by
  subst htag hb8
  dsimp only [idTrustOutAt]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [ProofLib.memRegion_split' (b := out + 9#64) (n := 4) (k := 35)
        (b' := out + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 13#64) (n := 2) (k := 33)
        (b' := out + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 15#64) (n := 1) (k := 32)
        (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 24)
        (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 16)
        (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 8)
        (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 40#64) (n := 1) (k := 7)
        (b' := out + 41#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 41#64) (n := 1) (k := 6)
        (b' := out + 42#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 42#64) (n := 1) (k := 5)
        (b' := out + 43#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 43#64) (n := 1) (k := 4)
        (b' := out + 44#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo16 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
        (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
          (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
            (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
              (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
                (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
                  (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
                    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo8 _ _))
                      (IsBlock.entails_memRegion (IsBlock.pointsTo32 _ _)))))))))))

theorem out_err_fold (A : RustAlloc) (out : BitVec 64)
    (sCap sPtr : BitVec 64) (sBs : List (BitVec 8)) (fnPtr : BitVec 64)
    (b8 : BitVec 8) (w9 : BitVec 32) (h13 : BitVec 16) (b15 : BitVec 8)
    (b40 b41 b42 b43 : BitVec 8) (w44 : BitVec 32)
    (hsCap : b15 ++ h13 ++ w9 ++ b8 = sCap)
    (hfnLen : w44 ++ b43 ++ b42 ++ b41 ++ b40 = BitVec.ofNat 64 (utf8 "read").length) :
    ((out ↦₆₄ speWord 1) ∗
      (((out + 8#64) ↦₈ b8) ∗ ((out + 9#64) ↦₃₂ w9) ∗
        ((out + 13#64) ↦₁₆ h13) ∗ ((out + 15#64) ↦₈ b15)) ∗
      ((out + 16#64) ↦₆₄ sPtr) ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
      ((out + 32#64) ↦₆₄ fnPtr) ∗
      (((out + 40#64) ↦₈ b40) ∗ ((out + 41#64) ↦₈ b41) ∗
        ((out + 42#64) ↦₈ b42) ∗ ((out + 43#64) ↦₈ b43) ∗ ((out + 44#64) ↦₃₂ w44)) ∗
      (fnPtr ↦ᵣ utf8 "read")) ⊢
    idTrustOutAt A out (.error ()) := by
  dsimp only [idTrustOutAt, speAt]
  rw [pointsTo64_out_8_any_eq out sCap b8 w9 h13 b15 hsCap,
      pointsTo64_out_40_any_eq out (BitVec.ofNat 64 (utf8 "read").length) b40 b41 b42 b43 w44 hfnLen]
  have hvec :
      (((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (out + 8#64) bs := by
    have heq :
        (((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
          ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs =
        vecU8At A (out + 8#64) sCap sPtr sBs := by
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
      dsimp only [vecHeader]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [heq]
    exact Entails.sepExists_right sBs
      (Entails.sepExists_right sCap (Entails.sepExists_right sPtr (Entails.refl _)))
  have hstr :
      ((out + 32#64) ↦₆₄ fnPtr) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ⊢
      strRefAt (out + 32#64) (utf8 "read") :=
    Entails.sepExists_right fnPtr (Entails.of_eq (by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]))
  have hgrp :
      (out ↦₆₄ speWord 1) ∗ ((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
        ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((out + 32#64) ↦₆₄ fnPtr) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") =
      (out ↦₆₄ speWord 1) ∗
        ((((out + 8#64) ↦₆₄ sCap) ∗ ((out + 16#64) ↦₆₄ sPtr) ∗
          ((out + 24#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs) ∗
        (((out + 32#64) ↦₆₄ fnPtr) ∗
          ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
          (fnPtr ↦ᵣ utf8 "read")) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_right (sepConj_mono hvec hstr)

/-! ## 7. `getResultAt` unpack lemmas (for `.error ()` and `.ok bs`) -/

theorem getResultAt_err_sp_144 (A : RustAlloc) (sp : BitVec 64) :
    getResultAt A (sp - 144#64) (.error ()) =
      ∃∗ fnPtr : BitVec 64, ∃∗ sBs : List (BitVec 8), ∃∗ sCap : BitVec 64, ∃∗ sPtr : BitVec 64,
        ((sp - 144#64) ↦₆₄ speWord 1) ∗
        ((sp - 136#64) ↦₆₄ sCap) ∗ ((sp - 128#64) ↦₆₄ sPtr) ∗
        ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 112#64) ↦₆₄ fnPtr) ∗
        ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") := by
  dsimp only [getResultAt, speAt, vecU8, strRefAt]
  simp_rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  have e8 : sp - 144#64 + 8#64 = sp - 136#64 := by bv_omega
  have e16 : sp - 136#64 + 8#64 = sp - 128#64 := by bv_omega
  have e24 : sp - 136#64 + 16#64 = sp - 120#64 := by bv_omega
  have e32 : sp - 144#64 + 32#64 = sp - 112#64 := by bv_omega
  have e40 : sp - 112#64 + 8#64 = sp - 104#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32, e40]

theorem getResultAt_ok_sp_144 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 144#64) (.ok bs) =
      ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
        ⌜bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bPtr ≠ 0#64⌝ ∗
        ((sp - 144#64) ↦₆₄ okTagVec) ∗
        ((sp - 136#64) ↦₆₄ bCap) ∗ ((sp - 128#64) ↦₆₄ bPtr) ∗
        ((sp - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗
        memRegion (sp - 112#64) 16 := by
  dsimp only [getResultAt, vecResultAt, vecU8]
  simp_rw [vecU8At_eq_expose]
  have e8 : sp - 144#64 + 8#64 = sp - 136#64 := by bv_omega
  have e16 : sp - 136#64 + 8#64 = sp - 128#64 := by bv_omega
  have e24 : sp - 136#64 + 16#64 = sp - 120#64 := by bv_omega
  have e32 : sp - 144#64 + 32#64 = sp - 112#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32]
  congr 1; funext bCap; congr 1; funext bPtr
  ac_rfl

theorem post_err_disj {dget : Except Unit (List (BitVec 8))} {s0 sf1 sf2 : State}
    (h1 : .error () = dget ∧ sf1.trace = s0.trace)
    (htr : sf2.trace = sf1.trace) :
    (.error () = dget ∧ sf2.trace = s0.trace) ∧
      IdPeerAns (.error ()) (.error ()) :=
  ⟨⟨h1.1, htr.trans h1.2⟩, rfl⟩

theorem post_ok_disj {bs : List (BitVec 8)} {dget : Except Unit (List (BitVec 8))} {s0 sf1 : State}
    (h1 : .ok bs = dget ∧ sf1.trace = s0.trace) :
    .ok bs = dget ∧ sf1.trace = s0.trace :=
  h1

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
