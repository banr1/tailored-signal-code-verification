/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
import ProofLib.RegChain
import ProofLib.SepLogic.WP.StateNorm

/-!
# Representation Predicates and `encoded_len` Specifications for `V1State.Unchunked.*`

Parametric and concrete separation-logic representation predicates, pure `encodedLen` models,
`LibsignalSpqrV1.Proto` equivalence bridges, and Hoare contracts for `Option<Authenticator>` and
the 10 `V1State.Unchunked.*` protobuf structs (`59`-, `71`-, `82`-, and `93`-instruction groups).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace EncodedLen

theorem zeroExtend64_beq_zero32 (x : BitVec 32) :
    (BitVec.zeroExtend 64 x == 0#64) = (x == 0#32) := by bv_bits

theorem ofNat_countLeadingZeros_64 (x : BitVec 64) :
    BitVec.ofNat 64 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 63

theorem ofNat_countLeadingZeros_32 (x : BitVec 32) :
    BitVec.ofNat 32 (countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 31

theorem truncate32_ofNat64 (n : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem hwVarintLen_eq_ofNat_varintLen_norm (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (varintLen v) :=
  hwVarintLen_eq_ofNat_varintLen v

theorem hwVarintLen_bvShift_eq_ofNat_varintLen_norm (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3#64)) + 0x49#64) >>> 6#64 =
      BitVec.ofNat 64 (varintLen v) :=
  hwVarintLen_bvShift_eq_ofNat_varintLen v

macro "epochEncLen_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    arm64_norm, *]
  done))

def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf; ac_rfl

theorem vecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact ⟨hm.1.1, hm.1.2.1⟩

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1; omega

theorem cap_add_one_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  simp [bne, cap_add_one_beq_zero_false h]

theorem ofNat_length_beq_zero_of_lt {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 64) :
    (BitVec.ofNat 64 bs.length == 0#64) = bs.isEmpty ∧
      (BitVec.ofNat 64 bs.length != 0#64) = !bs.isEmpty := by
  cases bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b rest =>
    simp only [List.isEmpty_cons, Bool.not_false]
    have hne : BitVec.ofNat 64 (b :: rest).length ≠ 0#64 := by
      intro heq; have h1 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at h1
      rw [Nat.mod_eq_of_lt hlt] at h1; simp only [List.length_cons] at h1; omega
    exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl
theorem noneCap_add_one_bne_zero : (noneCap + 1#64 != 0#64) = false := rfl
theorem zext64_truncate32 (v : BitVec 32) : (BitVec.zeroExtend 64 v).truncate 32 = v := by bv_bits

theorem bv_u32VarintField_nonzero {v : BitVec 32} (hv : v ≠ 0#32) :
    BitVec.ofNat 64 (varintLen (v.zeroExtend 64)) + 1#64 =
      BitVec.ofNat 64 (u32VarintFieldEncodedLen v) := by
  unfold u32VarintFieldEncodedLen
  simp only [hv, ↓reduceIte, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_bytesField_nonempty {bs : List (BitVec 8)} (hbs : bs.isEmpty = false) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 bs.length)) + 1#64 =
      BitVec.ofNat 64 (bytesFieldEncodedLen bs) := by
  unfold bytesFieldEncodedLen
  simp only [hbs, Bool.false_eq_true, ↓reduceIte, ← BitVec.ofNat_add]; congr 1; omega

theorem bv_add_ofNat_comm (a b : Nat) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_eq (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

theorem ule_zero_64 (x : BitVec 64) : BitVec.ule 0#64 x = true := by bv_bits
theorem ult_zero_64 (x : BitVec 64) : BitVec.ult x 0#64 = false := by bv_bits
theorem ule_self_64 (x : BitVec 64) : BitVec.ule x x = true := by bv_bits
theorem ult_self_64 (x : BitVec 64) : BitVec.ult x x = false := by bv_bits

theorem ule_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 (a + b)) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem ult_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem adds_no_overflow_of_eq {a b c : Nat} (heq : b + a = c) (hlt : c < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 c ∧
      (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 a) = false ∧
      (BitVec.ofNat 64 a).ule (BitVec.ofNat 64 c) = true ∧
      (BitVec.ofNat 64 c).ult (BitVec.ofNat 64 b) = false ∧
      (BitVec.ofNat 64 b).ule (BitVec.ofNat 64 c) = true := by
  subst heq
  exact ⟨bv_add_ofNat_comm b a, ult_ofNat_add_of_lt hlt, ule_ofNat_add_of_lt hlt,
    by rw [Nat.add_comm] at hlt ⊢; exact ult_ofNat_add_of_lt hlt,
    by rw [Nat.add_comm] at hlt ⊢; exact ule_ofNat_add_of_lt hlt⟩

theorem cmp_ls_false_of_lt {vlen tot : Nat} (hlt : vlen < tot) (htot : tot < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true ∧
    BitVec.ule (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false ∧
    BitVec.ult (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false ∧
    (BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen == 0#64) = false ∧
    (BitVec.ofNat 64 tot == BitVec.ofNat 64 vlen) = false := by
  have h1 : BitVec.ule (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true := by
    rw [BitVec.ule_eq_decide, decide_eq_true_eq]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]; omega
  have h2 : BitVec.ule (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false := by
    rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]; omega
  have h3 : BitVec.ult (BitVec.ofNat 64 tot) (BitVec.ofNat 64 vlen) = false := by
    rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]; omega
  have hne : BitVec.ofNat 64 tot ≠ BitVec.ofNat 64 vlen := by
    intro heq; have h := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot] at h; omega
  have hsub : BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen ≠ 0#64 := by
    intro heq; apply hne
    have : BitVec.ofNat 64 tot - BitVec.ofNat 64 vlen + BitVec.ofNat 64 vlen =
        0#64 + BitVec.ofNat 64 vlen := congrArg (· + BitVec.ofNat 64 vlen) heq
    simpa [BitVec.sub_add_cancel] using this
  exact ⟨h1, h2, h3, beq_eq_false_iff_ne.mpr hsub, beq_eq_false_iff_ne.mpr hne⟩

def EpochEncLenCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EpochEncLenCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EpochEncLenCalleeSaved s0 s1) (h2 : EpochEncLenCalleeSaved s1 s2) :
    EpochEncLenCalleeSaved s0 s2 := by
  reg_chain

theorem stackAt_epochEncodedLen_eq (sp : BitVec 64) :
    stackAt sp epochEncodedLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
  simp only [stackAt, epochEncodedLenStack]
  change memRegion (sp - 16#64) (8 * 2) = _
  rw [memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold

end EncodedLen

open EncodedLen

/-! ## 1. `Option<AuthenticatorPB>` (`48` bytes = `0x30`, align `8`) -/

/-- Pinned `Option<spqr::proto::pq_ratchet::Authenticator>` at `a` (`48` bytes = `0x30`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40` (`root_key.cap = 0xFFFFFFFFFFFFFFFF#64` niche)
    * `some auth`: `authenticatorPBPinnedAt A g a auth` -/
def optAuthenticatorPBPinnedAt (A : RustAlloc) (g : AuthenticatorPBGhost) (a : BitVec 64) :
    Option AuthenticatorPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBPinnedAt A g a auth

/-- Unpinned `Option<spqr::proto::pq_ratchet::Authenticator>` at `a` (`48` bytes = `0x30`, align `8`). -/
def optAuthenticatorPBAt (A : RustAlloc) (a : BitVec 64) : Option AuthenticatorPB → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBAt A a auth

private theorem sepExists_const {α : Sort _} (a₀ : α) (P : SepProp) :
    (∃∗ _ : α, P) = P := by
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun _ => Entails.refl _
  · exact Entails.sepExists_right a₀ (Entails.refl _)

theorem optAuthenticatorPBAt_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (opt : Option AuthenticatorPB) :
    optAuthenticatorPBAt A a opt =
      ∃∗ g : AuthenticatorPBGhost, optAuthenticatorPBPinnedAt A g a opt := by
  cases opt with
  | none =>
    simp only [optAuthenticatorPBAt, optAuthenticatorPBPinnedAt]
    exact (sepExists_const ⟨⟨0, 0⟩, ⟨0, 0⟩⟩ _).symm
  | some auth =>
    exact authenticatorPBAt_eq_exists_pinned A a auth

/-- First 64-bit word of `optAuthenticatorPBPinnedAt`: `noneCap` when `none`, `g.rootKey.cap` when `some`. -/
def optAuthCap (g : AuthenticatorPBGhost) : Option AuthenticatorPB → BitVec 64
  | none => noneCap
  | some _ => g.rootKey.cap

/-- Remaining 40 bytes + heap buffers of `optAuthenticatorPBPinnedAt`. -/
def optAuthPayload (A : RustAlloc) (g : AuthenticatorPBGhost) (p : BitVec 64) :
    Option AuthenticatorPB → SepProp
  | none => memRegion (p + 8#64) 40
  | some auth =>
    ((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Buf A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
      ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
      ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Buf A g.macKey.cap g.macKey.ptr auth.macKey

theorem optAuthenticatorPBPinnedAt_eq (A : RustAlloc) (g : AuthenticatorPBGhost) (p : BitVec 64)
    (opt : Option AuthenticatorPB) :
    optAuthenticatorPBPinnedAt A g p opt =
      (p ↦₆₄ optAuthCap g opt) ∗ optAuthPayload A g p opt := by
  cases opt with
  | none => rfl
  | some auth =>
    simp only [optAuthenticatorPBPinnedAt, authenticatorPBPinnedAt, optAuthCap,
      optAuthPayload, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc, arm64_norm]

/-- Bounds extracted from `optAuthPayload` in memory. -/
def OptAuthBounds (g : AuthenticatorPBGhost) (opt : Option AuthenticatorPB) : Prop :=
  (optAuthCap g opt + 1#64 == 0#64) = !opt.isSome ∧
  (optAuthCap g opt + 1#64 != 0#64) = opt.isSome ∧
  ∀ auth, opt = some auth →
    auth.rootKey.length < 2 ^ 63 ∧
    auth.macKey.length < 2 ^ 63 ∧
    (BitVec.ofNat 64 auth.rootKey.length == 0#64) = auth.rootKey.isEmpty ∧
    (BitVec.ofNat 64 auth.rootKey.length != 0#64) = !auth.rootKey.isEmpty ∧
    (BitVec.ofNat 64 auth.macKey.length == 0#64) = auth.macKey.isEmpty ∧
    (BitVec.ofNat 64 auth.macKey.length != 0#64) = !auth.macKey.isEmpty

theorem optAuthPayload_bounds {A : RustAlloc} {g : AuthenticatorPBGhost} {p : BitVec 64}
    {opt : Option AuthenticatorPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optAuthPayload A g p opt ∗ R) :
    OptAuthBounds g opt := by
  cases opt with
  | none =>
    simp only [OptAuthBounds, optAuthCap]
    refine ⟨by decide, by decide, ?_⟩
    intro _ h; cases h
  | some auth =>
    simp only [optAuthPayload] at hm
    have hroot_m : m ⊨ vecU8Buf A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        (((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
         ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         vecU8Buf A g.macKey.cap g.macKey.ptr auth.macKey ∗ R) := by
      convert hm using 1; ac_rfl
    have hmac_m : m ⊨ vecU8Buf A g.macKey.cap g.macKey.ptr auth.macKey ∗
        (((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         vecU8Buf A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
         ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
         ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨hr_le, hr_cap⟩ := vecU8Buf_bounds hroot_m
    have ⟨hm_le, hm_cap⟩ := vecU8Buf_bounds hmac_m
    have hr_lt : auth.rootKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr_le hr_cap
    have hm_lt : auth.macKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hm_le hm_cap
    have hr_z := ofNat_length_beq_zero_of_lt (by omega : auth.rootKey.length < 2 ^ 64)
    have hm_z := ofNat_length_beq_zero_of_lt (by omega : auth.macKey.length < 2 ^ 64)
    refine ⟨cap_add_one_beq_zero_false hr_cap, cap_add_one_bne_zero_true hr_cap, ?_⟩
    intro auth' h'
    cases h'
    exact ⟨hr_lt, hm_lt, hr_z.1, hr_z.2, hm_z.1, hm_z.2⟩

/-- Bounds extracted from a `vecU8Buf A pin.cap pin.ptr bs` in memory. -/
def VecU8FieldBounds (bs : List (BitVec 8)) : Prop :=
  bs.length < 2 ^ 63 ∧
  (BitVec.ofNat 64 bs.length == 0#64) = bs.isEmpty ∧
  (BitVec.ofNat 64 bs.length != 0#64) = !bs.isEmpty

theorem vecU8Buf_fieldBounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    VecU8FieldBounds bs := by
  have ⟨hle, hcap⟩ := vecU8Buf_bounds hm
  have hlt : bs.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle hcap
  have hz := ofNat_length_beq_zero_of_lt (by omega : bs.length < 2 ^ 64)
  exact ⟨hlt, hz.1, hz.2⟩

/-- Encoded length of an optional nested `ProtoAuthenticator` message field with a 1-byte tag:
    `0` when `none`, else `1 + varintLen (BitVec.ofNat 64 inner) + inner` where
    `inner = authenticatorPBEncodedLen auth`. -/
def optAuthenticatorPBFieldEncodedLen : Option AuthenticatorPB → Nat
  | none => 0
  | some auth =>
    let inner := authenticatorPBEncodedLen auth
    1 + varintLen (BitVec.ofNat 64 inner) + inner

theorem bv_u64VarintField_nonzero {v : BitVec 64} (hv : v ≠ 0#64) :
    BitVec.ofNat 64 (varintLen v) + 1#64 =
      BitVec.ofNat 64 (u64VarintFieldEncodedLen v) := by
  unfold u64VarintFieldEncodedLen
  simp only [hv, ↓reduceIte, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_optAuthField_some (auth : AuthenticatorPB) :
    BitVec.ofNat 64 (authenticatorPBEncodedLen auth) +
      BitVec.ofNat 64 (varintLen (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))) + 1#64 =
      BitVec.ofNat 64 (optAuthenticatorPBFieldEncodedLen (some auth)) := by
  unfold optAuthenticatorPBFieldEncodedLen
  simp only [← BitVec.ofNat_add]
  congr 1
  omega

private theorem protoEncodeKey_len_one' (tag : BitVec 32) (wt : Proto.WireType)
    (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeKey tag wt).length = 1 := by
  have hlt : ((tag <<< 3) ||| wt.toU32).zeroExtend 64 < 0x80#64 := by
    rcases htag with ⟨_, h2⟩
    cases wt <;> dsimp [Proto.WireType.toU32] <;> bv_bits
  dsimp only [Proto.encodeKey, Proto.encodeVarint, Proto.encodeVarintAux]
  split
  · rfl
  · contradiction

theorem optAuthenticatorPBFieldEncodedLen_eq_proto (tag : BitVec 32)
    (opt : Option AuthenticatorPB) (htag : tag ≥ 1#32 ∧ tag ≤ 15#32) :
    (Proto.encodeOptMessage ProtoAuthenticator.encodeRaw tag opt).length =
      optAuthenticatorPBFieldEncodedLen opt := by
  cases opt with
  | none => rfl
  | some auth =>
    unfold Proto.encodeOptMessage Proto.encodeMessage optAuthenticatorPBFieldEncodedLen
    simp only [List.length_append, protoEncodeKey_len_one' tag .lengthDelimited htag,
      ← authenticatorPBEncodedLen_eq_proto, ProtoAuthenticator.encodedLen,
      ← protoEncodedLenVarint_eq_varintLen, Proto.encodedLenVarint]

/-! ## 2. Parametric Representation Predicates for `V1State.Unchunked.*` -/

/-- Ghost pins for the 59-insn group (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`: `56` bytes). -/
abbrev Unchunked2PBGhost := AuthenticatorPBGhost

/-- Parametric pinned layout for the 59-insn `Unchunked` group (`56` bytes = `0x38`, align `8`):
    * `a + 0x00`: `auth: Option<ProtoAuthenticator>` (tag 2, 48B)
    * `a + 0x30`: `epoch: u64` (tag 1, 8B) -/
def unchunked2PinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) : SepProp :=
  optAuthenticatorPBPinnedAt A g a auth ∗
    ((a + 0x30#64) ↦₆₄ epoch)

/-- Parametric unpinned layout for the 59-insn `Unchunked` group (`56` bytes = `0x38`, align `8`). -/
def unchunked2At (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) : SepProp :=
  optAuthenticatorPBAt A a auth ∗
    ((a + 0x30#64) ↦₆₄ epoch)

theorem unchunked2At_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) :
    unchunked2At A a epoch auth =
      ∃∗ g : Unchunked2PBGhost, unchunked2PinnedAt A g a epoch auth := by
  simp only [unchunked2At, unchunked2PinnedAt, optAuthenticatorPBAt_eq_exists_pinned,
    sepExists_sepConj_left]

def unchunked2Unpacked (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) : SepProp :=
  (a ↦₆₄ optAuthCap g auth) ∗ optAuthPayload A g a auth ∗
    ((a + 48#64) ↦₆₄ epoch)

theorem unchunked2PinnedAt_eq_unpacked (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) :
    unchunked2PinnedAt A g a epoch auth = unchunked2Unpacked A g a epoch auth := by
  unfold unchunked2PinnedAt unchunked2Unpacked
  rw [optAuthenticatorPBPinnedAt_eq A g a]
  ac_rfl

/-- Ghost pins for the 71-insn group (`EkSent`, `HeaderReceived`: `80` bytes). -/
structure Unchunked3PBGhost where
  /-- Pin for the tag-3 `Vec<u8>` field (`dk` or `hdr`) at `+0x00`. -/
  f3 : VecPin
  /-- Pins for `auth: Option<ProtoAuthenticator>` at `+0x18`. -/
  auth : AuthenticatorPBGhost

/-- Parametric pinned layout for the 71-insn `Unchunked` group (`80` bytes = `0x50`, align `8`):
    * `a + 0x00`: `f3: Vec<u8>` (tag 3, 24B)
    * `a + 0x18`: `auth: Option<ProtoAuthenticator>` (tag 2, 48B)
    * `a + 0x48`: `epoch: u64` (tag 1, 8B) -/
def unchunked3PinnedAt (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) : SepProp :=
  vecU8At A a g.f3.cap g.f3.ptr f3 ∗
    optAuthenticatorPBPinnedAt A g.auth (a + 0x18#64) auth ∗
    ((a + 0x48#64) ↦₆₄ epoch)

/-- Parametric unpinned layout for the 71-insn `Unchunked` group (`80` bytes = `0x50`, align `8`). -/
def unchunked3At (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) : SepProp :=
  rustBytesVecAt A a f3 ∗
    optAuthenticatorPBAt A (a + 0x18#64) auth ∗
    ((a + 0x48#64) ↦₆₄ epoch)

theorem unchunked3At_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) :
    unchunked3At A a epoch auth f3 =
      ∃∗ g : Unchunked3PBGhost, unchunked3PinnedAt A g a epoch auth f3 := by
  simp only [unchunked3At, unchunked3PinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    optAuthenticatorPBAt_eq_exists_pinned, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun ga => Entails.sepExists_elim fun gf3 =>
      Entails.sepExists_right ⟨gf3, ga⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨gf3, ga⟩ =>
      Entails.sepExists_right ga (Entails.sepExists_right gf3 (Entails.refl _))

def unchunked3Unpacked (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
    vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
    ((a + 24#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 24#64) auth ∗
    ((a + 72#64) ↦₆₄ epoch)

theorem unchunked3PinnedAt_eq_unpacked (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 : List (BitVec 8)) :
    unchunked3PinnedAt A g a epoch auth f3 = unchunked3Unpacked A g a epoch auth f3 := by
  unfold unchunked3PinnedAt unchunked3Unpacked
  rw [vecU8At_eq_header_sep_buf, optAuthenticatorPBPinnedAt_eq A g.auth (a + 24#64)]
  simp only [vecHeader, sepConj_assoc, arm64_norm]

/-- Ghost pins for the 82-insn group (`HeaderSent`, `EkSentCt1Received`, `EkReceived`: `104` bytes). -/
structure Unchunked4PBGhost where
  /-- Pin for the tag-3 `Vec<u8>` field (`ek`, `dk`, or `hdr`) at `+0x00`. -/
  f3 : VecPin
  /-- Pin for the tag-4 `Vec<u8>` field (`dk`, `ct1`, or `ek`) at `+0x18`. -/
  f4 : VecPin
  /-- Pins for `auth: Option<ProtoAuthenticator>` at `+0x30`. -/
  auth : AuthenticatorPBGhost

/-- Parametric pinned layout for the 82-insn `Unchunked` group (`104` bytes = `0x68`, align `8`):
    * `a + 0x00`: `f3: Vec<u8>` (tag 3, 24B)
    * `a + 0x18`: `f4: Vec<u8>` (tag 4, 24B)
    * `a + 0x30`: `auth: Option<ProtoAuthenticator>` (tag 2, 48B)
    * `a + 0x60`: `epoch: u64` (tag 1, 8B) -/
def unchunked4PinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 : List (BitVec 8)) : SepProp :=
  vecU8At A a g.f3.cap g.f3.ptr f3 ∗
    vecU8At A (a + 0x18#64) g.f4.cap g.f4.ptr f4 ∗
    optAuthenticatorPBPinnedAt A g.auth (a + 0x30#64) auth ∗
    ((a + 0x60#64) ↦₆₄ epoch)

/-- Parametric unpinned layout for the 82-insn `Unchunked` group (`104` bytes = `0x68`, align `8`). -/
def unchunked4At (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 : List (BitVec 8)) : SepProp :=
  rustBytesVecAt A a f3 ∗
    rustBytesVecAt A (a + 0x18#64) f4 ∗
    optAuthenticatorPBAt A (a + 0x30#64) auth ∗
    ((a + 0x60#64) ↦₆₄ epoch)

theorem unchunked4At_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) :
    unchunked4At A a epoch auth f3 f4 =
      ∃∗ g : Unchunked4PBGhost, unchunked4PinnedAt A g a epoch auth f3 f4 := by
  simp only [unchunked4At, unchunked4PinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    optAuthenticatorPBAt_eq_exists_pinned, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun ga => Entails.sepExists_elim fun gf4 =>
      Entails.sepExists_elim fun gf3 => Entails.sepExists_right ⟨gf3, gf4, ga⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨gf3, gf4, ga⟩ =>
      Entails.sepExists_right ga (Entails.sepExists_right gf4 (Entails.sepExists_right gf3 (Entails.refl _)))

def unchunked4Unpacked (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
    vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
    ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗
    ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
    vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
    ((a + 48#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 48#64) auth ∗
    ((a + 96#64) ↦₆₄ epoch)

theorem unchunked4PinnedAt_eq_unpacked (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 : List (BitVec 8)) :
    unchunked4PinnedAt A g a epoch auth f3 f4 = unchunked4Unpacked A g a epoch auth f3 f4 := by
  unfold unchunked4PinnedAt unchunked4Unpacked
  rw [vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf,
    optAuthenticatorPBPinnedAt_eq A g.auth (a + 48#64)]
  simp only [vecHeader, sepConj_assoc, arm64_norm]

/-- Ghost pins for the 93-insn group (`Ct1Sent`, `Ct1SentEkReceived`: `128` bytes). -/
structure Unchunked5PBGhost where
  /-- Pin for the tag-3 `Vec<u8>` field (`hdr` or `es`) at `+0x00`. -/
  f3 : VecPin
  /-- Pin for the tag-4 `Vec<u8>` field (`es` or `ek`) at `+0x18`. -/
  f4 : VecPin
  /-- Pin for the tag-5 `Vec<u8>` field (`ct1`) at `+0x30`. -/
  f5 : VecPin
  /-- Pins for `auth: Option<ProtoAuthenticator>` at `+0x48`. -/
  auth : AuthenticatorPBGhost

/-- Parametric pinned layout for the 93-insn `Unchunked` group (`128` bytes = `0x80`, align `8`):
    * `a + 0x00`: `f3: Vec<u8>` (tag 3, 24B)
    * `a + 0x18`: `f4: Vec<u8>` (tag 4, 24B)
    * `a + 0x30`: `f5: Vec<u8>` (tag 5, 24B)
    * `a + 0x48`: `auth: Option<ProtoAuthenticator>` (tag 2, 48B)
    * `a + 0x78`: `epoch: u64` (tag 1, 8B) -/
def unchunked5PinnedAt (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 f5 : List (BitVec 8)) : SepProp :=
  vecU8At A a g.f3.cap g.f3.ptr f3 ∗
    vecU8At A (a + 0x18#64) g.f4.cap g.f4.ptr f4 ∗
    vecU8At A (a + 0x30#64) g.f5.cap g.f5.ptr f5 ∗
    optAuthenticatorPBPinnedAt A g.auth (a + 0x48#64) auth ∗
    ((a + 0x78#64) ↦₆₄ epoch)

/-- Parametric unpinned layout for the 93-insn `Unchunked` group (`128` bytes = `0x80`, align `8`). -/
def unchunked5At (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 f5 : List (BitVec 8)) : SepProp :=
  rustBytesVecAt A a f3 ∗
    rustBytesVecAt A (a + 0x18#64) f4 ∗
    rustBytesVecAt A (a + 0x30#64) f5 ∗
    optAuthenticatorPBAt A (a + 0x48#64) auth ∗
    ((a + 0x78#64) ↦₆₄ epoch)

theorem unchunked5At_eq_exists_pinned (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8)) :
    unchunked5At A a epoch auth f3 f4 f5 =
      ∃∗ g : Unchunked5PBGhost, unchunked5PinnedAt A g a epoch auth f3 f4 f5 := by
  simp only [unchunked5At, unchunked5PinnedAt, rustBytesVecAt, vecU8_eq_exists_pin,
    optAuthenticatorPBAt_eq_exists_pinned, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun ga => Entails.sepExists_elim fun gf5 =>
      Entails.sepExists_elim fun gf4 => Entails.sepExists_elim fun gf3 =>
        Entails.sepExists_right ⟨gf3, gf4, gf5, ga⟩ (Entails.refl _)
  · exact Entails.sepExists_elim fun ⟨gf3, gf4, gf5, ga⟩ =>
      Entails.sepExists_right ga (Entails.sepExists_right gf5
        (Entails.sepExists_right gf4 (Entails.sepExists_right gf3 (Entails.refl _))))

def unchunked5Unpacked (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 f5 : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ g.f3.cap) ∗ ((a + 8#64) ↦₆₄ g.f3.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 f3.length) ∗
    vecU8Buf A g.f3.cap g.f3.ptr f3 ∗
    ((a + 24#64) ↦₆₄ g.f4.cap) ∗ ((a + 32#64) ↦₆₄ g.f4.ptr) ∗
    ((a + 40#64) ↦₆₄ BitVec.ofNat 64 f4.length) ∗
    vecU8Buf A g.f4.cap g.f4.ptr f4 ∗
    ((a + 48#64) ↦₆₄ g.f5.cap) ∗ ((a + 56#64) ↦₆₄ g.f5.ptr) ∗
    ((a + 64#64) ↦₆₄ BitVec.ofNat 64 f5.length) ∗
    vecU8Buf A g.f5.cap g.f5.ptr f5 ∗
    ((a + 72#64) ↦₆₄ optAuthCap g.auth auth) ∗ optAuthPayload A g.auth (a + 72#64) auth ∗
    ((a + 120#64) ↦₆₄ epoch)

theorem unchunked5PinnedAt_eq_unpacked (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option AuthenticatorPB) (f3 f4 f5 : List (BitVec 8)) :
    unchunked5PinnedAt A g a epoch auth f3 f4 f5 =
      unchunked5Unpacked A g a epoch auth f3 f4 f5 := by
  unfold unchunked5PinnedAt unchunked5Unpacked
  rw [vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf, vecU8At_eq_header_sep_buf,
    optAuthenticatorPBPinnedAt_eq A g.auth (a + 72#64)]
  simp only [vecHeader, sepConj_assoc, arm64_norm]

/-! ## 3. Concrete Representation Predicates for all 10 `V1State.Unchunked.*` Structs -/

def keysUnsampledPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.KeysUnsampled) : SepProp :=
  unchunked2PinnedAt A g a m.epoch m.auth

def keysUnsampledPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.KeysUnsampled) : SepProp :=
  unchunked2At A a m.epoch m.auth

def noHeaderReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.NoHeaderReceived) : SepProp :=
  unchunked2PinnedAt A g a m.epoch m.auth

def noHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.NoHeaderReceived) : SepProp :=
  unchunked2At A a m.epoch m.auth

def ct2SentPBPinnedAt (A : RustAlloc) (g : Unchunked2PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.Ct2Sent) : SepProp :=
  unchunked2PinnedAt A g a m.epoch m.auth

def ct2SentPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.Ct2Sent) : SepProp :=
  unchunked2At A a m.epoch m.auth

def ekSentPBPinnedAt (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.EkSent) : SepProp :=
  unchunked3PinnedAt A g a m.epoch m.auth m.dk

def ekSentPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.EkSent) : SepProp :=
  unchunked3At A a m.epoch m.auth m.dk

def headerReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked3PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.HeaderReceived) : SepProp :=
  unchunked3PinnedAt A g a m.epoch m.auth m.hdr

def headerReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.HeaderReceived) : SepProp :=
  unchunked3At A a m.epoch m.auth m.hdr

def headerSentPBPinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.HeaderSent) : SepProp :=
  unchunked4PinnedAt A g a m.epoch m.auth m.ek m.dk

def headerSentPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.HeaderSent) : SepProp :=
  unchunked4At A a m.epoch m.auth m.ek m.dk

def ekSentCt1ReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  unchunked4PinnedAt A g a m.epoch m.auth m.dk m.ct1

def ekSentCt1ReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  unchunked4At A a m.epoch m.auth m.dk m.ct1

def ekReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked4PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.EkReceived) : SepProp :=
  unchunked4PinnedAt A g a m.epoch m.auth m.hdr m.ek

def ekReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.EkReceived) : SepProp :=
  unchunked4At A a m.epoch m.auth m.hdr m.ek

def ct1SentPBPinnedAt (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1Sent) : SepProp :=
  unchunked5PinnedAt A g a m.epoch m.auth m.hdr m.es m.ct1

def ct1SentPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1Sent) : SepProp :=
  unchunked5At A a m.epoch m.auth m.hdr m.es m.ct1

def ct1SentEkReceivedPBPinnedAt (A : RustAlloc) (g : Unchunked5PBGhost) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1SentEkReceived) : SepProp :=
  unchunked5PinnedAt A g a m.epoch m.auth m.es m.ek m.ct1

def ct1SentEkReceivedPBAt (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1SentEkReceived) : SepProp :=
  unchunked5At A a m.epoch m.auth m.es m.ek m.ct1

/-! ## 4. Pure `encodedLen` Models & `LibsignalSpqrV1.Proto` Bridge Theorems -/

def unchunked2EncodedLen (epoch : BitVec 64) (auth : Option AuthenticatorPB) : Nat :=
  u64VarintFieldEncodedLen epoch + optAuthenticatorPBFieldEncodedLen auth

def unchunked3EncodedLen (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 : List (BitVec 8)) : Nat :=
  u64VarintFieldEncodedLen epoch + optAuthenticatorPBFieldEncodedLen auth +
    bytesFieldEncodedLen f3

def unchunked4EncodedLen (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 : List (BitVec 8)) : Nat :=
  u64VarintFieldEncodedLen epoch + optAuthenticatorPBFieldEncodedLen auth +
    bytesFieldEncodedLen f3 + bytesFieldEncodedLen f4

def unchunked5EncodedLen (epoch : BitVec 64) (auth : Option AuthenticatorPB)
    (f3 f4 f5 : List (BitVec 8)) : Nat :=
  u64VarintFieldEncodedLen epoch + optAuthenticatorPBFieldEncodedLen auth +
    bytesFieldEncodedLen f3 + bytesFieldEncodedLen f4 + bytesFieldEncodedLen f5

def keysUnsampledPBEncodedLen (m : V1State.Unchunked.KeysUnsampled) : Nat :=
  unchunked2EncodedLen m.epoch m.auth

def noHeaderReceivedPBEncodedLen (m : V1State.Unchunked.NoHeaderReceived) : Nat :=
  unchunked2EncodedLen m.epoch m.auth

def ct2SentPBEncodedLen (m : V1State.Unchunked.Ct2Sent) : Nat :=
  unchunked2EncodedLen m.epoch m.auth

def ekSentPBEncodedLen (m : V1State.Unchunked.EkSent) : Nat :=
  unchunked3EncodedLen m.epoch m.auth m.dk

def headerReceivedPBEncodedLen (m : V1State.Unchunked.HeaderReceived) : Nat :=
  unchunked3EncodedLen m.epoch m.auth m.hdr

def headerSentPBEncodedLen (m : V1State.Unchunked.HeaderSent) : Nat :=
  unchunked4EncodedLen m.epoch m.auth m.ek m.dk

def ekSentCt1ReceivedPBEncodedLen (m : V1State.Unchunked.EkSentCt1Received) : Nat :=
  unchunked4EncodedLen m.epoch m.auth m.dk m.ct1

def ekReceivedPBEncodedLen (m : V1State.Unchunked.EkReceived) : Nat :=
  unchunked4EncodedLen m.epoch m.auth m.hdr m.ek

def ct1SentPBEncodedLen (m : V1State.Unchunked.Ct1Sent) : Nat :=
  unchunked5EncodedLen m.epoch m.auth m.hdr m.es m.ct1

def ct1SentEkReceivedPBEncodedLen (m : V1State.Unchunked.Ct1SentEkReceived) : Nat :=
  unchunked5EncodedLen m.epoch m.auth m.es m.ek m.ct1

theorem keysUnsampledPBEncodedLen_eq_proto (m : V1State.Unchunked.KeysUnsampled) :
    V1State.Unchunked.KeysUnsampled.encodedLen m = keysUnsampledPBEncodedLen m := by
  unfold V1State.Unchunked.KeysUnsampled.encodedLen V1State.Unchunked.KeysUnsampled.encodeRaw
    keysUnsampledPBEncodedLen unchunked2EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩]

theorem noHeaderReceivedPBEncodedLen_eq_proto (m : V1State.Unchunked.NoHeaderReceived) :
    V1State.Unchunked.NoHeaderReceived.encodedLen m = noHeaderReceivedPBEncodedLen m := by
  unfold V1State.Unchunked.NoHeaderReceived.encodedLen V1State.Unchunked.NoHeaderReceived.encodeRaw
    noHeaderReceivedPBEncodedLen unchunked2EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩]

theorem ct2SentPBEncodedLen_eq_proto (m : V1State.Unchunked.Ct2Sent) :
    V1State.Unchunked.Ct2Sent.encodedLen m = ct2SentPBEncodedLen m := by
  unfold V1State.Unchunked.Ct2Sent.encodedLen V1State.Unchunked.Ct2Sent.encodeRaw
    ct2SentPBEncodedLen unchunked2EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩]

theorem ekSentPBEncodedLen_eq_proto (m : V1State.Unchunked.EkSent) :
    V1State.Unchunked.EkSent.encodedLen m = ekSentPBEncodedLen m := by
  unfold V1State.Unchunked.EkSent.encodedLen V1State.Unchunked.EkSent.encodeRaw
    ekSentPBEncodedLen unchunked3EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.dk ⟨by decide, by decide⟩]

theorem headerReceivedPBEncodedLen_eq_proto (m : V1State.Unchunked.HeaderReceived) :
    V1State.Unchunked.HeaderReceived.encodedLen m = headerReceivedPBEncodedLen m := by
  unfold V1State.Unchunked.HeaderReceived.encodedLen V1State.Unchunked.HeaderReceived.encodeRaw
    headerReceivedPBEncodedLen unchunked3EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.hdr ⟨by decide, by decide⟩]

theorem headerSentPBEncodedLen_eq_proto (m : V1State.Unchunked.HeaderSent) :
    V1State.Unchunked.HeaderSent.encodedLen m = headerSentPBEncodedLen m := by
  unfold V1State.Unchunked.HeaderSent.encodedLen V1State.Unchunked.HeaderSent.encodeRaw
    headerSentPBEncodedLen unchunked4EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.ek ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 m.dk ⟨by decide, by decide⟩]

theorem ekSentCt1ReceivedPBEncodedLen_eq_proto (m : V1State.Unchunked.EkSentCt1Received) :
    V1State.Unchunked.EkSentCt1Received.encodedLen m = ekSentCt1ReceivedPBEncodedLen m := by
  unfold V1State.Unchunked.EkSentCt1Received.encodedLen V1State.Unchunked.EkSentCt1Received.encodeRaw
    ekSentCt1ReceivedPBEncodedLen unchunked4EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.dk ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 m.ct1 ⟨by decide, by decide⟩]

theorem ekReceivedPBEncodedLen_eq_proto (m : V1State.Unchunked.EkReceived) :
    V1State.Unchunked.EkReceived.encodedLen m = ekReceivedPBEncodedLen m := by
  unfold V1State.Unchunked.EkReceived.encodedLen V1State.Unchunked.EkReceived.encodeRaw
    ekReceivedPBEncodedLen unchunked4EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.hdr ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 m.ek ⟨by decide, by decide⟩]

theorem ct1SentPBEncodedLen_eq_proto (m : V1State.Unchunked.Ct1Sent) :
    V1State.Unchunked.Ct1Sent.encodedLen m = ct1SentPBEncodedLen m := by
  unfold V1State.Unchunked.Ct1Sent.encodedLen V1State.Unchunked.Ct1Sent.encodeRaw
    ct1SentPBEncodedLen unchunked5EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.hdr ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 m.es ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 5#32 m.ct1 ⟨by decide, by decide⟩]

theorem ct1SentEkReceivedPBEncodedLen_eq_proto (m : V1State.Unchunked.Ct1SentEkReceived) :
    V1State.Unchunked.Ct1SentEkReceived.encodedLen m = ct1SentEkReceivedPBEncodedLen m := by
  unfold V1State.Unchunked.Ct1SentEkReceived.encodedLen V1State.Unchunked.Ct1SentEkReceived.encodeRaw
    ct1SentEkReceivedPBEncodedLen unchunked5EncodedLen
  simp only [List.length_append,
    u64VarintFieldEncodedLen_eq_proto 1#32 m.epoch ⟨by decide, by decide⟩,
    optAuthenticatorPBFieldEncodedLen_eq_proto 2#32 m.auth ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 3#32 m.es ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 4#32 m.ek ⟨by decide, by decide⟩,
    bytesFieldEncodedLen_eq_proto 5#32 m.ct1 ⟨by decide, by decide⟩]

/-! ## 5. Symbol Names, Stack Budgets, `fnOff` Lemmas & `gen_decodes` for Unchunked Leaves -/

/-- Stack budget for all `V1State.Unchunked.*::encoded_len` leaf functions (`0x10` bytes). -/
abbrev unchunkedEncodedLenStack : Nat := 0x10

abbrev keysUnsampledEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#1]"
abbrev keysUnsampledEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::KeysUnsampled as prost::message::Message>::encoded_len [local#2]"

abbrev noHeaderReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#1]"
abbrev noHeaderReceivedEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived as prost::message::Message>::encoded_len [local#2]"

abbrev ct2SentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#1]"
abbrev ct2SentEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct2Sent as prost::message::Message>::encoded_len [local#2]"

abbrev ekSentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#1]"
abbrev ekSentEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent as prost::message::Message>::encoded_len [local#2]"

abbrev headerReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#1]"
abbrev headerReceivedEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived as prost::message::Message>::encoded_len [local#2]"

abbrev headerSentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#1]"
abbrev headerSentEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderSent as prost::message::Message>::encoded_len [local#2]"

abbrev ekSentCt1ReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#1]"
abbrev ekSentCt1ReceivedEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#2]"

abbrev ct1SentEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#1]"
abbrev ct1SentEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#2]"

abbrev ct1SentEkReceivedEncodedLenLocal1Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#1]"
abbrev ct1SentEkReceivedEncodedLenLocal2Name : String :=
  "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived as prost::message::Message>::encoded_len [local#2]"

/-! ## 6. Parametric & Concrete Hoare `Spec`s for `V1State.Unchunked.*::encoded_len` -/

abbrev Unchunked2EncodedLenPinnedGhost := BitVec 64 × Unchunked2PBGhost × BitVec 64 × Option AuthenticatorPB
abbrev Unchunked2EncodedLenGhost := BitVec 64 × BitVec 64 × Option AuthenticatorPB

def unchunked2EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked2EncodedLenPinnedGhost where
  pre := fun ⟨a, g, epoch, auth⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked2EncodedLen epoch auth < 2 ^ 64⌝ ∗
      unchunked2PinnedAt A g a epoch auth ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, g, epoch, auth⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) ∧ sf.trace = s0.trace⌝ ∗
      unchunked2PinnedAt A g a epoch auth ∗ stackAt s0.sp unchunkedEncodedLenStack

def unchunked2EncodedLenSpec (A : RustAlloc) : Spec Unchunked2EncodedLenGhost where
  pre := fun ⟨a, epoch, auth⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked2EncodedLen epoch auth < 2 ^ 64⌝ ∗
      unchunked2At A a epoch auth ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, epoch, auth⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked2EncodedLen epoch auth) ∧ sf.trace = s0.trace⌝ ∗
      unchunked2At A a epoch auth ∗ stackAt s0.sp unchunkedEncodedLenStack

abbrev Unchunked3EncodedLenPinnedGhost :=
  BitVec 64 × Unchunked3PBGhost × BitVec 64 × Option AuthenticatorPB × List (BitVec 8)
abbrev Unchunked3EncodedLenGhost :=
  BitVec 64 × BitVec 64 × Option AuthenticatorPB × List (BitVec 8)

def unchunked3EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked3EncodedLenPinnedGhost where
  pre := fun ⟨a, g, epoch, auth, f3⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked3EncodedLen epoch auth f3 < 2 ^ 64⌝ ∗
      unchunked3PinnedAt A g a epoch auth f3 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, g, epoch, auth, f3⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) ∧ sf.trace = s0.trace⌝ ∗
      unchunked3PinnedAt A g a epoch auth f3 ∗ stackAt s0.sp unchunkedEncodedLenStack

def unchunked3EncodedLenSpec (A : RustAlloc) : Spec Unchunked3EncodedLenGhost where
  pre := fun ⟨a, epoch, auth, f3⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked3EncodedLen epoch auth f3 < 2 ^ 64⌝ ∗
      unchunked3At A a epoch auth f3 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, epoch, auth, f3⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked3EncodedLen epoch auth f3) ∧ sf.trace = s0.trace⌝ ∗
      unchunked3At A a epoch auth f3 ∗ stackAt s0.sp unchunkedEncodedLenStack

abbrev Unchunked4EncodedLenPinnedGhost :=
  BitVec 64 × Unchunked4PBGhost × BitVec 64 × Option AuthenticatorPB × List (BitVec 8) × List (BitVec 8)
abbrev Unchunked4EncodedLenGhost :=
  BitVec 64 × BitVec 64 × Option AuthenticatorPB × List (BitVec 8) × List (BitVec 8)

def unchunked4EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked4EncodedLenPinnedGhost where
  pre := fun ⟨a, g, epoch, auth, f3, f4⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64⌝ ∗
      unchunked4PinnedAt A g a epoch auth f3 f4 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, g, epoch, auth, f3, f4⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) ∧ sf.trace = s0.trace⌝ ∗
      unchunked4PinnedAt A g a epoch auth f3 f4 ∗ stackAt s0.sp unchunkedEncodedLenStack

def unchunked4EncodedLenSpec (A : RustAlloc) : Spec Unchunked4EncodedLenGhost where
  pre := fun ⟨a, epoch, auth, f3, f4⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked4EncodedLen epoch auth f3 f4 < 2 ^ 64⌝ ∗
      unchunked4At A a epoch auth f3 f4 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, epoch, auth, f3, f4⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked4EncodedLen epoch auth f3 f4) ∧ sf.trace = s0.trace⌝ ∗
      unchunked4At A a epoch auth f3 f4 ∗ stackAt s0.sp unchunkedEncodedLenStack

abbrev Unchunked5EncodedLenPinnedGhost :=
  BitVec 64 × Unchunked5PBGhost × BitVec 64 × Option AuthenticatorPB × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)
abbrev Unchunked5EncodedLenGhost :=
  BitVec 64 × BitVec 64 × Option AuthenticatorPB × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)

def unchunked5EncodedLenPinnedSpec (A : RustAlloc) : Spec Unchunked5EncodedLenPinnedGhost where
  pre := fun ⟨a, g, epoch, auth, f3, f4, f5⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked5EncodedLen epoch auth f3 f4 f5 < 2 ^ 64⌝ ∗
      unchunked5PinnedAt A g a epoch auth f3 f4 f5 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, g, epoch, auth, f3, f4, f5⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked5EncodedLen epoch auth f3 f4 f5) ∧ sf.trace = s0.trace⌝ ∗
      unchunked5PinnedAt A g a epoch auth f3 f4 f5 ∗ stackAt s0.sp unchunkedEncodedLenStack

def unchunked5EncodedLenSpec (A : RustAlloc) : Spec Unchunked5EncodedLenGhost where
  pre := fun ⟨a, epoch, auth, f3, f4, f5⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ unchunked5EncodedLen epoch auth f3 f4 f5 < 2 ^ 64⌝ ∗
      unchunked5At A a epoch auth f3 f4 f5 ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun ⟨a, epoch, auth, f3, f4, f5⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (unchunked5EncodedLen epoch auth f3 f4 f5) ∧ sf.trace = s0.trace⌝ ∗
      unchunked5At A a epoch auth f3 f4 f5 ∗ stackAt s0.sp unchunkedEncodedLenStack

/-! ### Concrete `Spec` Wrappers for the 9 `V1State.Unchunked.*` Types -/

structure PinnedEncLenGhost (G M : Type) where
  a : BitVec 64
  g : G
  m : M

structure UnpinnedEncLenGhost (M : Type) where
  a : BitVec 64
  m : M

abbrev KeysUnsampledEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked2PBGhost V1State.Unchunked.KeysUnsampled
abbrev KeysUnsampledEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.KeysUnsampled

def keysUnsampledEncodedLenPinnedSpec (A : RustAlloc) : Spec KeysUnsampledEncodedLenPinnedGhost where
  pre := fun x s => (unchunked2EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s0 sf

def keysUnsampledEncodedLenSpec (A : RustAlloc) : Spec KeysUnsampledEncodedLenGhost where
  pre := fun x s => (unchunked2EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth⟩ s0 sf

abbrev NoHeaderReceivedEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked2PBGhost V1State.Unchunked.NoHeaderReceived
abbrev NoHeaderReceivedEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.NoHeaderReceived

def noHeaderReceivedEncodedLenPinnedSpec (A : RustAlloc) : Spec NoHeaderReceivedEncodedLenPinnedGhost where
  pre := fun x s => (unchunked2EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s0 sf

def noHeaderReceivedEncodedLenSpec (A : RustAlloc) : Spec NoHeaderReceivedEncodedLenGhost where
  pre := fun x s => (unchunked2EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth⟩ s0 sf

abbrev Ct2SentEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked2PBGhost V1State.Unchunked.Ct2Sent
abbrev Ct2SentEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.Ct2Sent

def ct2SentEncodedLenPinnedSpec (A : RustAlloc) : Spec Ct2SentEncodedLenPinnedGhost where
  pre := fun x s => (unchunked2EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth⟩ s0 sf

def ct2SentEncodedLenSpec (A : RustAlloc) : Spec Ct2SentEncodedLenGhost where
  pre := fun x s => (unchunked2EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth⟩ s
  post := fun x s0 sf => (unchunked2EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth⟩ s0 sf

abbrev EkSentEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked3PBGhost V1State.Unchunked.EkSent
abbrev EkSentEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.EkSent

def ekSentEncodedLenPinnedSpec (A : RustAlloc) : Spec EkSentEncodedLenPinnedGhost where
  pre := fun x s => (unchunked3EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩ s
  post := fun x s0 sf => (unchunked3EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk⟩ s0 sf

def ekSentEncodedLenSpec (A : RustAlloc) : Spec EkSentEncodedLenGhost where
  pre := fun x s => (unchunked3EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩ s
  post := fun x s0 sf => (unchunked3EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.dk⟩ s0 sf

abbrev HeaderReceivedEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked3PBGhost V1State.Unchunked.HeaderReceived
abbrev HeaderReceivedEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.HeaderReceived

def headerReceivedEncodedLenPinnedSpec (A : RustAlloc) : Spec HeaderReceivedEncodedLenPinnedGhost where
  pre := fun x s => (unchunked3EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩ s
  post := fun x s0 sf => (unchunked3EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr⟩ s0 sf

def headerReceivedEncodedLenSpec (A : RustAlloc) : Spec HeaderReceivedEncodedLenGhost where
  pre := fun x s => (unchunked3EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩ s
  post := fun x s0 sf => (unchunked3EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr⟩ s0 sf

abbrev HeaderSentEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked4PBGhost V1State.Unchunked.HeaderSent
abbrev HeaderSentEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.HeaderSent

def headerSentEncodedLenPinnedSpec (A : RustAlloc) : Spec HeaderSentEncodedLenPinnedGhost where
  pre := fun x s => (unchunked4EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩ s
  post := fun x s0 sf => (unchunked4EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩ s0 sf

def headerSentEncodedLenSpec (A : RustAlloc) : Spec HeaderSentEncodedLenGhost where
  pre := fun x s => (unchunked4EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩ s
  post := fun x s0 sf => (unchunked4EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.ek, x.m.dk⟩ s0 sf

abbrev EkSentCt1ReceivedEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received
abbrev EkSentCt1ReceivedEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.EkSentCt1Received

def ekSentCt1ReceivedEncodedLenPinnedSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodedLenPinnedGhost where
  pre := fun x s => (unchunked4EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked4EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ s0 sf

def ekSentCt1ReceivedEncodedLenSpec (A : RustAlloc) : Spec EkSentCt1ReceivedEncodedLenGhost where
  pre := fun x s => (unchunked4EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked4EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ s0 sf

abbrev Ct1SentEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent
abbrev Ct1SentEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.Ct1Sent

def ct1SentEncodedLenPinnedSpec (A : RustAlloc) : Spec Ct1SentEncodedLenPinnedGhost where
  pre := fun x s => (unchunked5EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked5EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ s0 sf

def ct1SentEncodedLenSpec (A : RustAlloc) : Spec Ct1SentEncodedLenGhost where
  pre := fun x s => (unchunked5EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked5EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.hdr, x.m.es, x.m.ct1⟩ s0 sf

abbrev Ct1SentEkReceivedEncodedLenPinnedGhost := PinnedEncLenGhost Unchunked5PBGhost V1State.Unchunked.Ct1SentEkReceived
abbrev Ct1SentEkReceivedEncodedLenGhost := UnpinnedEncLenGhost V1State.Unchunked.Ct1SentEkReceived

def ct1SentEkReceivedEncodedLenPinnedSpec (A : RustAlloc) : Spec Ct1SentEkReceivedEncodedLenPinnedGhost where
  pre := fun x s => (unchunked5EncodedLenPinnedSpec A).pre ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked5EncodedLenPinnedSpec A).post ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩ s0 sf

def ct1SentEkReceivedEncodedLenSpec (A : RustAlloc) : Spec Ct1SentEkReceivedEncodedLenGhost where
  pre := fun x s => (unchunked5EncodedLenSpec A).pre ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩ s
  post := fun x s0 sf => (unchunked5EncodedLenSpec A).post ⟨x.a, x.m.epoch, x.m.auth, x.m.es, x.m.ek, x.m.ct1⟩ s0 sf

end CryptoVerification.SpqrV1.ProtoRepr
