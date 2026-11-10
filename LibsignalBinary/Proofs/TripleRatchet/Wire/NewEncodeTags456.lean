/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewEncodeTags123
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<SignalMessage>::new` Segment 2b (`+0x278 .. +0x3dc`)

Encodes protobuf field 4 (`ciphertext`, `+0x278 → +0x2e0`) and optional fields 5 (`pq_ratchet`)
and 6 (`addresses`) (`+0x2e0 → +0x3dc`), yielding `x.serPrefix6 parse = x.serializeContent parse`,
and composes the full `+0x100 → +0x3dc` encoding phase.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Separation-logic helpers for exposing `ciphertext`, `pqRatchet`, and `addresses` -/

def optVecU8RestAt (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    Option (List (BitVec 8)) → SepProp
  | none => memRegion (a + 8#64) 16
  | some bs =>
    ((a + 8#64) ↦₆₄ pin.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ⌜bs.length ≤ pin.cap.toNat ∧ pin.cap.toNat < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
      if pin.cap = 0 then emp
      else
        A.live pin.ptr pin.cap.toNat 1 ∗ (pin.ptr ↦ₛ bs) ∗
          memRegion (pin.ptr + BitVec.ofNat 64 bs.length) (pin.cap.toNat - bs.length)

theorem optVecU8At_expose_cap_rest (A : RustAlloc) (pin : VecPin) (a : BitVec 64)
    (opt : Option (List (BitVec 8))) (hcap : opt = none → pin.cap = noneCap) :
    optVecU8At A pin a opt = (a ↦₆₄ pin.cap) ∗ optVecU8RestAt A pin a opt := by
  cases opt with
  | none =>
    rw [hcap rfl]
    rfl
  | some bs =>
    simp only [optVecU8At, optVecU8RestAt, vecU8At, vecHeader, sepConj_assoc]

theorem eq_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P = Q := by
  rwa [sepConj_emp] at h

theorem wireSignalMessageAt_expose_ct (A : RustAlloc) (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr base : BitVec 64)
    (hct_ne : x.ciphertext ≠ []) (hct_le : x.ciphertext.length ≤ 2 ^ 32) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      base (x.protoMsg uuidTryParse) =
    (ctCopyPtr ↦ₛ x.ciphertext) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ base (some x.senderRatchetKey.serialize) ∗
     ((base + 24#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
     ((base + 24#64 + 8#64) ↦₆₄ ctCopyPtr) ∗
     ((base + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
     ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
     A.live ctCopyPtr x.ciphertext.length 1 ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ (base + 48#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     optVecU8At A ⟨addrCap, addrPtr⟩ (base + 72#64) (x.addresses uuidTryParse) ∗
     optU32At (base + 96#64) (some x.counter) ∗
     optU32At (base + 104#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_ct_nonempty_eq A (base + 24#64) ctCopyPtr x.ciphertext hct_ne (by omega)]
  apply eq_of_sep_focus
  sep_focus

theorem wireSignalMessageAt_expose_pq (A : RustAlloc) (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCopyPtr addrCap addrPtr base : BitVec 64)
    (hpq_ne : x.pqRatchet ≠ [])
    (hpq_pin : PqPinOk (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr x.pqRatchet) :
    wireSignalMessageAt A
      (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrCap addrPtr)
      base (x.protoMsg uuidTryParse) =
    (pqCopyPtr ↦ₛ x.pqRatchet) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ base (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       (base + 24#64) (some x.ciphertext) ∗
     ((base + 48#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
     ((base + 48#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
     ((base + 48#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
     ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
     A.live pqCopyPtr x.pqRatchet.length 1 ∗
     optVecU8At A ⟨addrCap, addrPtr⟩ (base + 72#64) (x.addresses uuidTryParse) ∗
     optU32At (base + 96#64) (some x.counter) ∗
     optU32At (base + 104#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_pq_nonempty_eq A (base + 48#64)
        (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr x.pqRatchet hpq_ne hpq_pin]
  apply eq_of_sep_focus
  sep_focus

theorem wireSignalMessageAt_expose_addrCap (A : RustAlloc) (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr sp0 : BitVec 64)
    (hcap : x.addresses uuidTryParse = none → addrCap = noneCap) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      (sp0 - 288#64) (x.protoMsg uuidTryParse) =
    ((sp0 - 216#64) ↦₆₄ addrCap) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     optVecU8RestAt A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
     optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
     optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) := by
  have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_expose_cap_rest A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64)
        (x.addresses uuidTryParse) hcap]
  dsimp only
  rw [h216]
  sep_focus

@[local simp, local arm64_norm]
theorem bv_ult_zero (v : BitVec 64) : v.ult 0#64 = false := by
  simp [BitVec.ult]

theorem optVecU8At_addr_some_eq (A : RustAlloc) (sp0 addrPtr : BitVec 64)
    (opt : Option (List (BitVec 8))) (ad : List (BitVec 8))
    (hopt : opt = some ad) (had_len : ad.length = 36) :
    optVecU8At A ⟨36#64, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) opt =
    ((sp0 - 216#64) ↦₆₄ 36#64) ∗
    ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
    ((sp0 - 200#64) ↦₆₄ 36#64) ∗
    (addrPtr ↦ₛ ad) ∗
    (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
     A.live addrPtr ad.length 1) := by
  subst hopt
  have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
  have h208 : (sp0 - 216#64) + 8#64 = sp0 - 208#64 := bv_sub_add_lit sp0 216 8
  have h200 : (sp0 - 216#64) + 16#64 = sp0 - 200#64 := bv_sub_add_lit sp0 216 16
  have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
  have hcap_eq : (36#64 : BitVec 64) = BitVec.ofNat 64 ad.length := by rw [had_len]
  rw [hcap_eq, optVecU8At_some_exact_eq A ((sp0 - 288#64) + 0x48#64) addrPtr ad (by omega),
      ← hcap_eq, h216, h208, h200]
  simp only [boxU8Buf, had_ne, ↓reduceIte]
  apply eq_of_sep_focus
  sep_focus

theorem wireSignalMessageAt_expose_addr_some (A : RustAlloc) (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr sp0 : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad) (had_len : ad.length = 36) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
      (sp0 - 288#64) (x.protoMsg uuidTryParse) =
    ((sp0 - 216#64) ↦₆₄ 36#64) ∗
    ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
    ((sp0 - 200#64) ↦₆₄ 36#64) ∗
    (addrPtr ↦ₛ ad) ∗
    (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
     optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
       ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
     optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
       (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
     (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
      A.live addrPtr ad.length 1) ∗
     optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
     optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) := by
  unfold wireSignalMessageAt SignalMessageNewGhost.mkPins SignalMessageNewGhost.protoMsg
  dsimp only
  rw [optVecU8At_addr_some_eq A sp0 addrPtr (x.addresses uuidTryParse) ad had had_len]
  apply eq_of_sep_focus
  sep_focus

theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])

theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P)
    (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm

theorem session2MemcpySpec_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8)) (s0 : State)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : (s0.readReg64 .x2).toNat = bs.length) :
    framelessMemcpySpec.pre (dst, src, bs) s0 = memRegion dst bs.length ∗ (src ↦ₛ bs) := by
  simp only [framelessMemcpySpec, hx0, hx1, hx2, wp_norm, arm64_norm]

theorem encodeVarintSpec_post_eq (A : RustAlloc) (x : EncodeVarintGhost) (s0 sf : State)
    (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    (encodeVarintSpec A).post x s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
            vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
        A.pool ∗ stackAt sp_val encodeVarintStack := by
  simp only [encodeVarintSpec, hsp0]

theorem encodeVarintSpec_pre_eq (A : RustAlloc) (x : EncodeVarintGhost) (s : State)
    (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 < 2 ^ 62) (hsp : s.sp = sp_val) :
    (encodeVarintSpec A).pre x s =
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt sp_val encodeVarintStack := by
  unfold encodeVarintSpec
  dsimp only
  rw [hx0, hx1, hsp, eq_true (Or.inr hlt)]
  simp only [wp_norm, arm64_norm]

theorem encodeVarintSpec_pre_eq_or (A : RustAlloc) (x : EncodeVarintGhost) (s : State)
    (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) (hsp : s.sp = sp_val) :
    (encodeVarintSpec A).pre x s =
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt sp_val encodeVarintStack := by
  unfold encodeVarintSpec
  dsimp only
  rw [hx0, hx1, hsp, eq_true hlt]
  simp only [wp_norm, arm64_norm]

namespace NewEncodeTags456Callees

theorem new_memcpy_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  memcpy_ok_at2_ext hA (name := signalMessageNewName) (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec :=
  hook_ok_at_raw (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::new") (k := num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) rfl (by decide)
    (ls_hook% "memcpy") ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

end NewEncodeTags456Callees

/-! ## Pure arithmetic facts for Tags 4, 5, and 6 -/

theorem bv_sub_ult_false_of_add_lt {tot a b : Nat}
    (htot : (BitVec.ofNat 64 tot).toNat = tot)
    (ha : (BitVec.ofNat 64 a).toNat = a)
    (hb : (BitVec.ofNat 64 b).toNat = b)
    (hlt : a + b < tot) :
    (BitVec.ofNat 64 tot - BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = false := by
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
  rw [BitVec.toNat_sub_of_le]
  · rw [htot, ha, hb]
    omega
  · rw [BitVec.le_def, htot, ha]
    omega

theorem tag4_pure_facts (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (x.serPrefix3 uuidTryParse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length) = false ∧
    (x.serPrefix3 uuidTryParse ++ [0x22#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix3 uuidTryParse ++ [0x22#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++
      x.ciphertext = x.serPrefix4 uuidTryParse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64
        ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
          encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length).ult
      (BitVec.ofNat 64 x.ciphertext.length) = false ∧
    ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length + x.ciphertext.length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64
      ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
      BitVec.ofNat 64 x.ciphertext.length =
      BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le x
  have h6_len : (x.serPrefix6 uuidTryParse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length]
  have hp4_eq : ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++ x.ciphertext =
      x.serPrefix4 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix4, encodeBytesField_4_protoMsg, List.append_assoc]
  have hlen4 : ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length + x.ciphertext.length =
      (x.serPrefix4 uuidTryParse).length := by
    rw [← List.length_append, hp4_eq]
  have hp3_toNat : (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length).toNat =
      (x.serPrefix3 uuidTryParse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp3a_toNat : (BitVec.ofNat 64 ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
      encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length).toNat =
      ((x.serPrefix3 uuidTryParse ++ [0x22#8]) ++
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, by omega, ?_, ?_, ?_, hp4_eq, ?_, by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen4; omega
  · exact bv_sub_ult_false_of_add_lt htot hp3a_toNat hct_toNat (by omega)
  · rw [← BitVec.ofNat_add, hlen4]

theorem tag5_pure_facts (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34)
    (hpq_ne : x.pqRatchet ≠ [])
    (hpq_lt : x.pqRatchet.length < 2 ^ 32) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (BitVec.ofNat 64 x.pqRatchet.length + 1#64 == 0#64) = false ∧
    (x.serPrefix4 uuidTryParse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length) = false ∧
    (x.serPrefix4 uuidTryParse ++ [0x2a#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix4 uuidTryParse ++ [0x2a#8]).length +
      (encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++
      x.pqRatchet = x.serPrefix5 uuidTryParse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64
        ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
          encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length).ult
      (BitVec.ofNat 64 x.pqRatchet.length) = false ∧
    (BitVec.ofNat 64 x.pqRatchet.length == 0#64) = false ∧
    ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length + x.pqRatchet.length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64
      ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
        encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
      BitVec.ofNat 64 x.pqRatchet.length =
      BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le x
  have h6_len : (x.serPrefix6 uuidTryParse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length]
  have hpq_pos : 0 < x.pqRatchet.length := List.length_pos_iff.mpr hpq_ne
  have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpq_bv_hi : BitVec.ofNat 64 x.pqRatchet.length < 4294967296#64 := by
    rw [BitVec.lt_def, hpq_toNat]; change x.pqRatchet.length < 4294967296; omega
  have hpq_bv_lo : 1#64 ≤ BitVec.ofNat 64 x.pqRatchet.length := by
    rw [BitVec.le_def, hpq_toNat]; change 1 ≤ x.pqRatchet.length; omega
  have hp5_eq : ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++ x.pqRatchet =
      x.serPrefix5 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix5, encodeBytesField_5_protoMsg_nonempty x hpq_ne,
      List.append_assoc]
  have hlen5 : ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length + x.pqRatchet.length =
      (x.serPrefix5 uuidTryParse).length := by
    rw [← List.length_append, hp5_eq]
  have hp4_toNat : (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length).toNat =
      (x.serPrefix4 uuidTryParse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp4a_toNat : (BitVec.ofNat 64 ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
      encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length).toNat =
      ((x.serPrefix4 uuidTryParse ++ [0x2a#8]) ++
        encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega,
    by revert hpq_bv_lo hpq_bv_hi; generalize BitVec.ofNat 64 x.pqRatchet.length = v; intros; bv_kernel,
    by omega, ?_, ?_, ?_, hp5_eq, ?_,
    by revert hpq_bv_lo hpq_bv_hi; generalize BitVec.ofNat 64 x.pqRatchet.length = v; intros; bv_kernel,
    by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen5; omega
  · exact bv_sub_ult_false_of_add_lt htot hp4a_toNat hpq_toNat (by omega)
  · rw [← BitVec.ofNat_add, hlen5]

theorem tag6_pure_facts (x : SignalMessageNewGhost)
    (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad)
    (encLen : Nat)
    (henc_eq : encLen = (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    ad.length = 36 ∧
    ad ≠ [] ∧
    (x.serPrefix5 uuidTryParse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length) = false ∧
    (x.serPrefix5 uuidTryParse ++ [0x32#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix5 uuidTryParse ++ [0x32#8]).length + (encodeVarint 36#64).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64) ++ ad = x.serPrefix6 uuidTryParse ∧
    (BitVec.ofNat 64 (encLen + 9) -
      BitVec.ofNat 64 ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64).length).ult
      36#64 = false ∧
    ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36 ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    BitVec.ofNat 64 ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36#64 =
      BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le x
  have h6_len : (x.serPrefix6 uuidTryParse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length]
  have had_len : ad.length = 36 := addresses_length had
  have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
  have hp6_eq : ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64) ++ ad =
      x.serPrefix6 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix6, encodeBytesField_6_protoMsg_some x had,
      encodeVarint_36, List.append_assoc]
  have hlen6 : ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64).length + 36 =
      (x.serPrefix6 uuidTryParse).length := by
    have h := congrArg List.length hp6_eq
    rw [List.length_append, had_len] at h
    exact h
  have hp5_toNat : (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length).toNat =
      (x.serPrefix5 uuidTryParse).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hp5a_toNat : (BitVec.ofNat 64 ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++
      encodeVarint 36#64).length).toNat =
      ((x.serPrefix5 uuidTryParse ++ [0x32#8]) ++ encodeVarint 36#64).length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, had_len, had_ne, by omega, ?_, ?_, ?_, hp6_eq, ?_, by omega, ?_⟩
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · rw [List.length_append] at hlen6; omega
  · exact bv_sub_ult_false_of_add_lt htot hp5a_toNat (by decide) (by omega)
  · rw [← BitVec.ofNat_add, hlen6]

/-! ## Encode tag 4 (`ciphertext`, `+0x278 → +0x2e0`) -/

theorem new_encode_tag4_wpp_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix3 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix4 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, hp3_lt, hcmp4, hvar4_lt, hvar4_fit,
        hp4_eq, hcmp_ct, hp3a_slice_le, hp4_bv_eq⟩ :=
    tag4_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
      henc_lo henc_hi hct_le
  simp only [List.append_assoc, List.singleton_append] at hcmp_ct hp3a_slice_le hp4_bv_eq
  have hp4_eq' :
      (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++ x.ciphertext =
      x.serPrefix4 uuidTryParse := by
    simpa only [List.append_assoc, List.singleton_append] using hp4_eq
  clear hp4_eq
  rw [serVec_expose_one A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
        (x.serPrefix3 uuidTryParse) hp3_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x278 0x2dc
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call
    (x := ⟨BitVec.ofNat 64 x.ciphertext.length, sp0 - 176#64,
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
           serPtr, x.serPrefix3 uuidTryParse ++ [0x22#8]⟩)
    (F := ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
        State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          hvar4_lt
          (by simp only [wp_norm, arm64_norm, hsp])]
    rw [← serVec_pack_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length)
          (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
          (x.serPrefix3 uuidTryParse) 0x22#8 hp3_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar4_fit with ⟨hcap', hptr'⟩
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  by_cases hct_nil : x.ciphertext = []
  · have hct_zero : BitVec.ofNat 64 x.ciphertext.length = 0#64 := by simp [hct_nil]
    have hp4_nil : x.serPrefix3 uuidTryParse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length) = x.serPrefix4 uuidTryParse := by
      simpa only [hct_nil, List.append_nil] using hp4_eq'
    rw [hp4_nil,
        vecU8At_eq_of_pos A (sp0 - 176#64)
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (x.serPrefix4 uuidTryParse) (by omega)]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hct_zero,
        hsp1, hsp0_align, h19_1, h20_1, h21_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1,
        htr1, and_self]
    · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)]
      exact entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := List.length_pos_iff.mpr hct_nil
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hct_nz : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hct_toNat, BitVec.toNat_zero] at this
      omega
    rw [serVec_expose_slice A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr
          (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
          (BitVec.ofNat 64 x.ciphertext.length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
            BitVec.ofNat 64 x.ciphertext.length)
          (x.serPrefix3 uuidTryParse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
          x.ciphertext.length
          hp3a_slice_le htot_lt hserPtr hct_pos rfl rfl rfl,
        wireSignalMessageAt_expose_ct A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr
          (sp0 - 288#64) hct_nil hct_le]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1])
    refine SepWPp.call
      (x := (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length,
             ctCopyPtr, x.ciphertext))
      (F := ((sp0 - 176#64) ↦₆₄
              BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ serPtr) ∗
            ((sp0 - 160#64) ↦₆₄
              BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length) ∗
            A.live serPtr
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
            (serPtr ↦ₛ (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length))) ∗
            memRegion
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
                (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                  encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length -
                x.ciphertext.length) ∗
            A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
             (((sp0 - 288#64) + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             (((sp0 - 288#64) + 0x18#64 + 8#64) ↦₆₄ ctCopyPtr) ∗
             (((sp0 - 288#64) + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
             A.live ctCopyPtr x.ciphertext.length 1 ∗
             optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
               (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
             optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
             optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
             optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [session2MemcpySpec_pre_eq _ _ _ _
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hct_toNat])]
      simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm,
      hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm,
        hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h26_2, h27_2, h28_2, hfp_2,
        htr2, and_self]
    · rw [← hp4_bv_eq,
          stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
          ← hp4_eq',
          ← serVec_pack_slice A sp0
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
              serPtr
              (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
              (BitVec.ofNat 64 x.ciphertext.length)
              (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (x.serPrefix3 uuidTryParse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
              x.ciphertext
              hp3a_slice_le htot_lt hserPtr hct_nil rfl rfl rfl rfl]
      exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag4_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix3 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix4 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag4_wpp_core (NewEncodeTags456Callees.new_memcpy_ok_ext hA) hVarint
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392
    hct_le hpq_lt hserPtr s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag4_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVarint : EncodeVarintOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix3 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix4 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag4_wpp_core NewEncodeTags456Callees.new_memcpy_ok hVarint
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392
    hct_le hpq_lt hserPtr s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Encode tag 6 (`addresses`, `+0x378 → +0x3dc`) -/

theorem new_encode_tag6_wpp_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 988#64)
      s
      (wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix5 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, had_len, had_ne, hp5_lt, hcmp6, hvar6_lt, hvar6_fit,
        hp6_eq, hcmp_ad, hp5a_slice_le, hp6_bv_eq⟩ :=
    tag6_pure_facts x ad had (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
      henc_lo henc_hi
  simp only [List.append_assoc, List.singleton_append] at hcmp_ad hp5a_slice_le hp6_bv_eq
  have hp6_eq' : (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64) ++ ad = x.serPrefix6 uuidTryParse := by
    simpa only [List.append_assoc, List.singleton_append] using hp6_eq
  clear hp6_eq
  rw [serVec_expose_one A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
        (x.serPrefix5 uuidTryParse) hp5_lt htot_lt hserPtr rfl rfl,
      wireSignalMessageAt_expose_addr_some A x rkPtr ctCopyPtr pqCap pqCopyPtr
        addrPtr sp0 ad had had_len]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x378 0x3d8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call
    (x := ⟨36#64, sp0 - 176#64,
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
           serPtr, x.serPrefix5 uuidTryParse ++ [0x32#8]⟩)
    (F := ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (addrPtr ↦ₛ ad) ∗
          (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
        State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          hvar6_lt
          (by simp only [wp_norm, arm64_norm, hsp])]
    rw [← serVec_pack_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
          (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
          (x.serPrefix5 uuidTryParse) 0x32#8 hp5_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar6_fit with ⟨hcap', hptr'⟩
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  rw [serVec_expose_slice A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr
        (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length)
        36#64
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
          36#64)
        (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)
        36
        hp5a_slice_le htot_lt hserPtr (by decide) rfl rfl rfl]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call
    (x := (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length,
           addrPtr, ad))
    (F := ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄
            BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length) ∗
          A.live serPtr
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
              (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length - 36) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have h36_toNat : (36#64 : BitVec 64).toNat = 36 := rfl
    rw [session2MemcpySpec_pre_eq _ _ _ _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, had_len, h36_toNat])]
    simp only [had_len, State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm,
    hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h27_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpySpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.done
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm,
      hsp2, hsp0_align, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h27_2, hfp_2,
      htr2, and_self]
  · rw [← hp6_bv_eq,
        stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
        ← hp6_eq',
        ← serVec_pack_slice A sp0
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr
            (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length)
            36#64
            (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)
            ad
            (by rw [had_len]; exact hp5a_slice_le) htot_lt hserPtr had_ne rfl (by rw [had_len]) rfl rfl,
        had_len]
    exact entails_of_sep_focus (by sep_focus)


/-! ## Encode tags 5 and 6 (`+0x2e0 → +0x3dc`) -/

theorem serPrefix5_of_pq_empty (x : SignalMessageNewGhost)
    (h : x.pqRatchet = []) : x.serPrefix5 uuidTryParse = x.serPrefix4 uuidTryParse := by
  simp [SignalMessageNewGhost.serPrefix5, encodeBytesField_5_protoMsg_empty x h]

theorem serPrefix6_of_addresses_none (x : SignalMessageNewGhost)
    (h : x.addresses uuidTryParse = none) : x.serPrefix6 uuidTryParse = x.serPrefix5 uuidTryParse := by
  simp [SignalMessageNewGhost.serPrefix6, encodeBytesField_6_protoMsg_none x h]

private theorem signalMessageNew_seg2_seq_wpp' {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem new_encode_tag56_wpp_core {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) framelessMemcpySpec)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix4 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  by_cases hpq_nil : x.pqRatchet = []
  · have hpqCap_eq : pqCap = BitVec.allOnes 64 := by
      simpa [PqPinOk, hpq_nil, noneCap] using hpq_pin
    subst hpqCap_eq
    have hp45_eq : x.serPrefix4 uuidTryParse = x.serPrefix5 uuidTryParse :=
      (serPrefix5_of_pq_empty x hpq_nil).symm
    cases haddr_eq : x.addresses uuidTryParse with
    | none =>
      have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
        simpa [haddr_eq, noneCap] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have hp56_eq : x.serPrefix5 uuidTryParse = x.serPrefix6 uuidTryParse :=
        (serPrefix6_of_addresses_none x haddr_eq).symm
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr (BitVec.allOnes 64) addrPtr sp0 (fun _ => rfl)]
      simp only [sepConj_assoc]
      new_fetches_range b (Rust.withPanics ext) 0x2e0 0x374
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
      examples_hide_fetches
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
      · simp only [wp_norm, arm64_norm,
          ← hp56_eq, ← hp45_eq,
          hsp, hsp0_align, hx19, hx21, hx23, hx24, hx25, hx27, hx29, and_self]
      · rw [hp45_eq, hp56_eq]
        exact entails_of_sep_focus (by sep_focus)
    | some ad =>
      have haddrCap_eq : addrCap = 36#64 := by
        simpa [haddr_eq] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have htag6 := new_encode_tag6_wpp_core hmemcpy hVarint x sp0 rkPtr ctCopyPtr
        (BitVec.allOnes 64) pqCopyPtr addrPtr serPtr ad haddr_eq hct_le hpq_lt hserPtr
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
      simp only [sepConj_assoc]
      new_fetches_range b (Rust.withPanics ext) 0x2e0 0x374
      generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (888))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      rw [hp45_eq]
      have hrew :
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗ ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
          optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
            ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
          optVecU8At A ⟨BitVec.allOnes 64, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
            (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
          optVecU8RestAt A ⟨36#64, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
          optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
          optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix5 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack =
          (wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr)
             (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
           vecU8At A (sp0 - 176#64)
             (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
             serPtr (x.serPrefix5 uuidTryParse) ∗
           A.pool ∗ stackAt (sp0 - 416#64) computeMacStack) ∗
          (((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗ ((sp0 - 344#64) ↦₆₄ ctCopyPtr)) := by
        rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
              (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
        sep_focus
      refine signalMessageNew_seg2_seq_wpp' (by simp only [wp_norm, arm64_norm])
        (htag6 _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
          (by simp only [wp_norm, arm64_norm, hx19])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24])
          (by rw [← hp45_eq]; simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx29]))
        hrew
        (fun _ _ hp => panicAllocPost_of_eq hp) ?_
      intro sm hpcm hrunm h1
      refine SepWPp.done hpcm hrunm ⟨by simpa only [wp_norm, arm64_norm] using h1, ?_⟩
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
      exact entails_of_sep_focus (by sep_focus)
  · have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq_nil
    have hpq_pin' := hpq_pin
    simp only [PqPinOk, hemp, Bool.false_eq_true, ↓reduceIte] at hpq_pin'
    obtain ⟨rfl, hpq_pos, _, hpqPtr_ne⟩ := hpq_pin'
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hvar := encodeVarint_ok_at_new_ext hVarint
    have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
    have ⟨htot_toNat, htot_lt, hpq_cmn, hp4_lt, hcmp5, hvar5_lt, hvar5_fit,
          hp5_eq, hcmp_pq, hpq_nz, hp4a_slice_le, hp5_bv_eq⟩ :=
      tag5_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
        henc_lo henc_hi hpq_nil hpq_lt
    have hp5_eq' :
        (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++
          x.pqRatchet = x.serPrefix5 uuidTryParse := by
      simpa only [List.append_assoc, List.singleton_append] using hp5_eq
    simp only [List.append_assoc, List.singleton_append] at hcmp_pq hp4a_slice_le hp5_bv_eq
    have htag6_opt := fun (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad) =>
      new_encode_tag6_wpp_core hmemcpy hVarint x sp0 rkPtr ctCopyPtr
        (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrPtr serPtr ad had
        hct_le hpq_lt hserPtr
    rw [serVec_expose_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
          (x.serPrefix4 uuidTryParse) hp4_lt htot_lt hserPtr rfl rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b1 => ?_
    new_fetches_range b (Rust.withPanics ext) 0x2e0 0x360
    generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    refine SepWPp.call
      (x := ⟨BitVec.ofNat 64 x.pqRatchet.length, sp0 - 176#64,
             BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
             serPtr, x.serPrefix4 uuidTryParse ++ [0x2a#8]⟩)
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ 32#64) ∗
            wireSignalMessageAt A
              (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrCap addrPtr)
              (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => by
        simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
          State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
      rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            hvar5_lt
            (by simp only [wp_norm, arm64_norm, hsp])]
      rw [← serVec_pack_one A sp0
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
            (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
            (x.serPrefix4 uuidTryParse) 0x2a#8 hp4_lt htot_lt hserPtr rfl rfl rfl]
      simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm,
      hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
      at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
    rcases hno_grow hvar5_fit with ⟨hcap', hptr'⟩
    subst cap' ptr'
    simp only [List.append_assoc, List.singleton_append]
    rw [serVec_expose_slice A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr
          (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
          (BitVec.ofNat 64 x.pqRatchet.length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
            BitVec.ofNat 64 x.pqRatchet.length)
          (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
          x.pqRatchet.length
          hp4a_slice_le htot_lt hserPtr hpq_pos rfl rfl rfl,
        wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr addrCap addrPtr
          (sp0 - 288#64) hpq_nil hpq_pin]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    refine SepWPp.call
      (x := (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length,
             pqCopyPtr, x.pqRatchet))
      (F := ((sp0 - 176#64) ↦₆₄
              BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ serPtr) ∗
            ((sp0 - 160#64) ↦₆₄
              BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length) ∗
            A.live serPtr
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
            (serPtr ↦ₛ (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))) ∗
            memRegion
              (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                BitVec.ofNat 64 x.pqRatchet.length)
              ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length -
                x.pqRatchet.length) ∗
            A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
            ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ 32#64) ∗
            (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
             optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
               ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
             (((sp0 - 288#64) + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
             (((sp0 - 288#64) + 0x30#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
             (((sp0 - 288#64) + 0x30#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
             ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
             A.live pqCopyPtr x.pqRatchet.length 1 ∗
             optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
             optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
             optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [session2MemcpySpec_pre_eq _ _ _ _
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hpq_toNat])]
      simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm,
      hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2
    have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
    cases haddr_eq : x.addresses uuidTryParse with
    | none =>
      have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
        simpa [haddr_eq, noneCap] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have hp56_eq : x.serPrefix5 uuidTryParse = x.serPrefix6 uuidTryParse :=
        (serPrefix6_of_addresses_none x haddr_eq).symm
      rw [optVecU8At_expose_cap_rest A ⟨BitVec.allOnes 64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) none (fun _ => rfl),
          h216]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
      · simp only [wp_norm, arm64_norm,
          ← hp56_eq,
          hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h27_2, hfp_2,
          htr2, and_self]
      · rw [← hp56_eq, ← hp5_bv_eq,
            stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
            ← hp5_eq',
            ← serVec_pack_slice A sp0
                (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
                serPtr
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
                (BitVec.ofNat 64 x.pqRatchet.length)
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
                x.pqRatchet
                hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl]
        exact entails_of_sep_focus (by sep_focus)
    | some ad =>
      have haddrCap_eq : addrCap = 36#64 := by
        simpa [haddr_eq] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have htag6 := htag6_opt ad haddr_eq
      rw [optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
          h216]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (888))
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
      have hrew :
          ((serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length) ↦ₛ x.pqRatchet) ∗
          (pqCopyPtr ↦ₛ x.pqRatchet) ∗
          ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length) ∗
          A.live serPtr
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
               encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
              BitVec.ofNat 64 x.pqRatchet.length)
            ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
              (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length -
              x.pqRatchet.length) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
          optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
            ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
          (((sp0 - 288#64) + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          (((sp0 - 288#64) + 0x30#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
          (((sp0 - 288#64) + 0x30#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
          A.live pqCopyPtr x.pqRatchet.length 1 ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          optVecU8RestAt A ⟨36#64, addrPtr⟩ (sp0 - 216#64) (some ad) ∗
          optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
          optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368 =
          (wireSignalMessageAt A
             (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr 36#64 addrPtr)
             (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
           vecU8At A (sp0 - 176#64)
             (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
             serPtr (x.serPrefix5 uuidTryParse) ∗
           A.pool ∗ stackAt (sp0 - 416#64) computeMacStack) ∗
          (((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
           ((sp0 - 344#64) ↦₆₄ ctCopyPtr)) := by
        rw [← hp5_bv_eq, stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
            ← hp5_eq',
            ← serVec_pack_slice A sp0
                (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
                serPtr
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
                (BitVec.ofNat 64 x.pqRatchet.length)
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
                x.pqRatchet
                hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl,
            wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr
              36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
            haddr_eq,
            optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
              ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
            h216]
        sep_focus
      refine signalMessageNew_seg2_seq_wpp' (by simp only [wp_norm, arm64_norm, htr2])
        (htag6 _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun2])
          (by simp only [wp_norm, arm64_norm, hsp2])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
          (by simp only [wp_norm, arm64_norm, h19_2])
          (by simp only [wp_norm, arm64_norm, h20_2])
          (by simp only [wp_norm, arm64_norm, h21_2])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, h23_2])
          (by simp only [wp_norm, arm64_norm, h24_2])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, h27_2])
          (by simp only [wp_norm, arm64_norm, hfp_2]))
        hrew
        (fun _ _ hp => panicAllocPost_of_eq hp) ?_
      intro sm hpcm hrunm h1
      refine SepWPp.done hpcm hrunm ⟨by simpa only [wp_norm, arm64_norm, htr2, hfp_2] using h1, ?_⟩
      rw [wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr
            36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
          haddr_eq,
          optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
          h216]
      dsimp only
      exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag56_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix4 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag56_wpp_core (NewEncodeTags456Callees.new_memcpy_ok_ext hA) hVarint
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
    hct_le hpq_lt hserPtr hpq_pin haddrCap s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag56_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVarint : EncodeVarintOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix4 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag56_wpp_core NewEncodeTags456Callees.new_memcpy_ok hVarint
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408
    hct_le hpq_lt hserPtr hpq_pin haddrCap s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag4_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w392 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 736#64)
      s
      (((sp0 - 392#64) ↦₆₄ w392) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix3 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix4 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63); clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, hp3_lt, hcmp4, hvar4_lt, hvar4_fit,
        hp4_eq, hcmp_ct, hp3a_slice_le, hp4_bv_eq⟩ :=
    tag4_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
      henc_lo henc_hi hct_le
  simp only [List.append_assoc, List.singleton_append] at hcmp_ct hp3a_slice_le hp4_bv_eq
  have hp4_eq' :
      (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length)) ++ x.ciphertext =
      x.serPrefix4 uuidTryParse := by
    simpa only [List.append_assoc, List.singleton_append] using hp4_eq
  clear hp4_eq
  rw [serVec_expose_one A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
        (x.serPrefix3 uuidTryParse) hp3_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  refine signalMessageNew_call_placed
    (x := ⟨BitVec.ofNat 64 x.ciphertext.length, sp0 - 176#64,
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
           serPtr, x.serPrefix3 uuidTryParse ++ [0x22#8]⟩)
    (F := ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
        State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          hvar4_lt
          (by simp only [wp_norm, arm64_norm, hsp])]
    rw [← serVec_pack_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length)
          (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse).length + 1#64)
          (x.serPrefix3 uuidTryParse) 0x22#8 hp3_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar4_fit with ⟨hcap', hptr'⟩
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  by_cases hct_nil : x.ciphertext = []
  · have hct_zero : BitVec.ofNat 64 x.ciphertext.length = 0#64 := by simp [hct_nil]
    have hp4_nil : x.serPrefix3 uuidTryParse ++ 0x22#8 ::
        encodeVarint (BitVec.ofNat 64 x.ciphertext.length) = x.serPrefix4 uuidTryParse := by
      simpa only [hct_nil, List.append_nil] using hp4_eq'
    rw [hp4_nil,
        vecU8At_eq_of_pos A (sp0 - 176#64)
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (x.serPrefix4 uuidTryParse) (by omega)]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hct_zero,
        hsp1, hsp0_align, h19_1, h20_1, h21_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1,
        htr1, and_self]
    · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)]
      exact entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := List.length_pos_iff.mpr hct_nil
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hct_nz : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hct_toNat, BitVec.toNat_zero] at this
      omega
    rw [serVec_expose_slice A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr
          (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
          (BitVec.ofNat 64 x.ciphertext.length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
            encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
            BitVec.ofNat 64 x.ciphertext.length)
          (x.serPrefix3 uuidTryParse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
          x.ciphertext.length
          hp3a_slice_le htot_lt hserPtr hct_pos rfl rfl rfl,
        wireSignalMessageAt_expose_ct A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr
          (sp0 - 288#64) hct_nil hct_le]
    simp only [sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun1])
    refine SepWPp.call
      (x := (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length,
             ctCopyPtr, x.ciphertext))
      (F := ((sp0 - 176#64) ↦₆₄
              BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ serPtr) ∗
            ((sp0 - 160#64) ↦₆₄
              BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length) ∗
            A.live serPtr
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
            (serPtr ↦ₛ (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
              encodeVarint (BitVec.ofNat 64 x.ciphertext.length))) ∗
            memRegion
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
                (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                  encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length -
                x.ciphertext.length) ∗
            A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
             (((sp0 - 288#64) + 0x18#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             (((sp0 - 288#64) + 0x18#64 + 8#64) ↦₆₄ ctCopyPtr) ∗
             (((sp0 - 288#64) + 0x18#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
             ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
             A.live ctCopyPtr x.ciphertext.length 1 ∗
             optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
               (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
             optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
             optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
             optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [session2MemcpySpec_pre_eq _ _ _ _
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hct_toNat])]
      simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm,
      hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm,
        hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h26_2, h27_2, h28_2, hfp_2,
        htr2, and_self]
    · rw [← hp4_bv_eq,
          stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
          ← hp4_eq',
          ← serVec_pack_slice A sp0
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
              serPtr
              (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length)
              (BitVec.ofNat 64 x.ciphertext.length)
              (BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (serPtr + BitVec.ofNat 64 (x.serPrefix3 uuidTryParse ++ 0x22#8 ::
                encodeVarint (BitVec.ofNat 64 x.ciphertext.length)).length +
                BitVec.ofNat 64 x.ciphertext.length)
              (x.serPrefix3 uuidTryParse ++ 0x22#8 :: encodeVarint (BitVec.ofNat 64 x.ciphertext.length))
              x.ciphertext
              hp3a_slice_le htot_lt hserPtr hct_nil rfl rfl rfl rfl]
      exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag6_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrPtr serPtr : BitVec 64)
    (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 888#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix5 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr 36#64 addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63); clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, had_len, had_ne, hp5_lt, hcmp6, hvar6_lt, hvar6_fit,
        hp6_eq, hcmp_ad, hp5a_slice_le, hp6_bv_eq⟩ :=
    tag6_pure_facts x ad had (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
      henc_lo henc_hi
  simp only [List.append_assoc, List.singleton_append] at hcmp_ad hp5a_slice_le hp6_bv_eq
  have hp6_eq' : (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64) ++ ad = x.serPrefix6 uuidTryParse := by
    simpa only [List.append_assoc, List.singleton_append] using hp6_eq
  clear hp6_eq
  rw [serVec_expose_one A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
        (x.serPrefix5 uuidTryParse) hp5_lt htot_lt hserPtr rfl rfl,
      wireSignalMessageAt_expose_addr_some A x rkPtr ctCopyPtr pqCap pqCopyPtr
        addrPtr sp0 ad had had_len]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  refine signalMessageNew_call_placed
    (x := ⟨36#64, sp0 - 176#64,
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
           serPtr, x.serPrefix5 uuidTryParse ++ [0x32#8]⟩)
    (F := ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (addrPtr ↦ₛ ad) ∗
          (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by
      simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
        State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm
    rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          hvar6_lt
          (by simp only [wp_norm, arm64_norm, hsp])]
    rw [← serVec_pack_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length)
          (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length + 1#64)
          (x.serPrefix5 uuidTryParse) 0x32#8 hp5_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf1 _ hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar6_fit with ⟨hcap', hptr'⟩
  subst cap' ptr'
  simp only [List.append_assoc, List.singleton_append]
  rw [serVec_expose_slice A sp0
        (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr
        (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length)
        36#64
        (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
          36#64)
        (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)
        36
        hp5a_slice_le htot_lt hserPtr (by decide) rfl rfl rfl]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call
    (x := (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length,
           addrPtr, ad))
    (F := ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄
            BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length) ∗
          A.live serPtr
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
              (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length - 36) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
          ((sp0 - 200#64) ↦₆₄ 36#64) ∗
          (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
             ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
             (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           (⌜addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
            A.live addrPtr ad.length 1) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
           optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
    (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    have h36_toNat : (36#64 : BitVec 64).toNat = 36 := rfl
    rw [session2MemcpySpec_pre_eq _ _ _ _
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, had_len, h36_toNat])]
    simp only [had_len, State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
    apply satisfies_of_sep_focus hm
    sep_focus
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm,
    hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h27_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpySpec, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.done
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm,
      hsp2, hsp0_align, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h27_2, hfp_2,
      htr2, and_self]
  · rw [← hp6_bv_eq,
        stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
        ← hp6_eq',
        ← serVec_pack_slice A sp0
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr
            (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length)
            36#64
            (BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64).length +
              36#64)
            (x.serPrefix5 uuidTryParse ++ 0x32#8 :: encodeVarint 36#64)
            ad
            (by rw [had_len]; exact hp5a_slice_le) htot_lt hserPtr had_ne rfl (by rw [had_len]) rfl rfl,
        had_len]
    exact entails_of_sep_focus (by sep_focus)

theorem new_encode_tag56_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr w408 : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (hpq_pin : PqPinOk pqCap pqCopyPtr x.pqRatchet)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 736#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = pqCap)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 988#64)
      s
      (((sp0 - 408#64) ↦₆₄ w408) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ 32#64) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix4 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = 32#64 ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = addrCap ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix6 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  by_cases hpq_nil : x.pqRatchet = []
  · have hpqCap_eq : pqCap = BitVec.allOnes 64 := by
      simpa [PqPinOk, hpq_nil, noneCap] using hpq_pin
    subst hpqCap_eq
    have hp45_eq : x.serPrefix4 uuidTryParse = x.serPrefix5 uuidTryParse :=
      (serPrefix5_of_pq_empty x hpq_nil).symm
    cases haddr_eq : x.addresses uuidTryParse with
    | none =>
      have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
        simpa [haddr_eq, noneCap] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have hp56_eq : x.serPrefix5 uuidTryParse = x.serPrefix6 uuidTryParse :=
        (serPrefix6_of_addresses_none x haddr_eq).symm
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr (BitVec.allOnes 64) addrPtr sp0 (fun _ => rfl)]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
      · simp only [wp_norm, arm64_norm,
          ← hp56_eq, ← hp45_eq,
          hsp, hsp0_align, hx19, hx21, hx23, hx24, hx25, hx27, hx29, and_self]
      · rw [hp45_eq, hp56_eq]
        exact entails_of_sep_focus (by sep_focus)
    | some ad =>
      have haddrCap_eq : addrCap = 36#64 := by
        simpa [haddr_eq] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have htag6 := new_encode_tag6_wpp_placed h_mc hVarint x sp0 rkPtr ctCopyPtr
        (BitVec.allOnes 64) pqCopyPtr addrPtr serPtr ad haddr_eq hct_le hpq_lt hserPtr
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
      simp only [sepConj_assoc]
      apply signalMessageNew_of_sepWP_placed (mid := (blkPl_63).base + bv% (888)) hcl
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      intro hcl0
      rw [hp45_eq]
      have hrew :
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗ ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
          optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
            ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
          optVecU8At A ⟨BitVec.allOnes 64, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64)
            (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
          optVecU8RestAt A ⟨36#64, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
          optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
          optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix5 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack =
          (wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr)
             (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
           vecU8At A (sp0 - 176#64)
             (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
             serPtr (x.serPrefix5 uuidTryParse) ∗
           A.pool ∗ stackAt (sp0 - 416#64) computeMacStack) ∗
          (((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗ ((sp0 - 344#64) ↦₆₄ ctCopyPtr)) := by
        rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
              (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
        sep_focus
      refine signalMessageNew_seg2_seq_wpp' (by simp only [wp_norm, arm64_norm])
        (htag6 _ hcl0
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun])
          (by simp only [wp_norm, arm64_norm, hsp])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
          (by simp only [wp_norm, arm64_norm, hx19])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx21])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hx23])
          (by simp only [wp_norm, arm64_norm, hx24])
          (by rw [← hp45_eq]; simp only [wp_norm, arm64_norm, hx25])
          (by simp only [wp_norm, arm64_norm, hx27])
          (by simp only [wp_norm, arm64_norm, hx29]))
        hrew
        (fun _ _ hp => panicAllocPost_of_eq hp) ?_
      intro sm hpcm hrunm h1
      refine SepWPp.done hpcm hrunm ⟨by simpa only [wp_norm, arm64_norm] using h1, ?_⟩
      rw [wireSignalMessageAt_expose_addrCap A x rkPtr ctCopyPtr
            (BitVec.allOnes 64) pqCopyPtr 36#64 addrPtr sp0 (fun h => by simp [h] at haddr_eq)]
      exact entails_of_sep_focus (by sep_focus)
  · have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq_nil
    have hpq_pin' := hpq_pin
    simp only [PqPinOk, hemp, Bool.false_eq_true, ↓reduceIte] at hpq_pin'
    obtain ⟨rfl, hpq_pos, _, hpqPtr_ne⟩ := hpq_pin'
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hmemcpy := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
    have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
    have ⟨htot_toNat, htot_lt, hpq_cmn, hp4_lt, hcmp5, hvar5_lt, hvar5_fit,
          hp5_eq, hcmp_pq, hpq_nz, hp4a_slice_le, hp5_bv_eq⟩ :=
      tag5_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl
        henc_lo henc_hi hpq_nil hpq_lt
    have hp5_eq' :
        (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)) ++
          x.pqRatchet = x.serPrefix5 uuidTryParse := by
      simpa only [List.append_assoc, List.singleton_append] using hp5_eq
    simp only [List.append_assoc, List.singleton_append] at hcmp_pq hp4a_slice_le hp5_bv_eq
    have htag6_opt := fun (ad : List (BitVec 8)) (had : x.addresses uuidTryParse = some ad) =>
      new_encode_tag6_wpp_placed h_mc hVarint x sp0 rkPtr ctCopyPtr
        (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrPtr serPtr ad had
        hct_le hpq_lt hserPtr
    rw [serVec_expose_one A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
          (x.serPrefix4 uuidTryParse) hp4_lt htot_lt hserPtr rfl rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b1 => ?_
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    intro hcl0
    refine signalMessageNew_call_placed
      (x := ⟨BitVec.ofNat 64 x.pqRatchet.length, sp0 - 176#64,
             BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9),
             serPtr, x.serPrefix4 uuidTryParse ++ [0x2a#8]⟩)
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ 32#64) ∗
            wireSignalMessageAt A
              (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr addrCap addrPtr)
              (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => by
        simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC,
          State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
    · intro R' hm
      rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
      rw [encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64)
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            hvar5_lt
            (by simp only [wp_norm, arm64_norm, hsp])]
      rw [← serVec_pack_one A sp0
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length)
            (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
            (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse).length + 1#64)
            (x.serPrefix4 uuidTryParse) 0x2a#8 hp4_lt htot_lt hserPtr rfl rfl rfl]
      simp only [State.mem_setMem, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf1 hcl1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm,
      hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
      at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    rw [encodeVarintSpec_post_eq A _ _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    simp only [wp_norm, arm64_norm] at htr1
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
    rcases hno_grow hvar5_fit with ⟨hcap', hptr'⟩
    subst cap' ptr'
    simp only [List.append_assoc, List.singleton_append]
    rw [serVec_expose_slice A sp0
          (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr
          (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
          (BitVec.ofNat 64 x.pqRatchet.length)
          (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
            BitVec.ofNat 64 x.pqRatchet.length)
          (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
          x.pqRatchet.length
          hp4a_slice_le htot_lt hserPtr hpq_pos rfl rfl rfl,
        wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr addrCap addrPtr
          (sp0 - 288#64) hpq_nil hpq_pin]
    simp only [sepConj_assoc]
    apply signalMessageNew_of_sepWP_placed (mid := lsρ lsMemcpySym) hcl1
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    intro hcl1'
    refine signalMessageNew_call_placed
      (x := (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length,
             pqCopyPtr, x.pqRatchet))
      (F := ((sp0 - 176#64) ↦₆₄
              BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ serPtr) ∗
            ((sp0 - 160#64) ↦₆₄
              BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length) ∗
            A.live serPtr
              (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
            (serPtr ↦ₛ (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
              encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))) ∗
            memRegion
              (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                BitVec.ofNat 64 x.pqRatchet.length)
              ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length -
                x.pqRatchet.length) ∗
            A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
            ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ 32#64) ∗
            (optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
             optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
               ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
             (((sp0 - 288#64) + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
             (((sp0 - 288#64) + 0x30#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
             (((sp0 - 288#64) + 0x30#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
             ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
             A.live pqCopyPtr x.pqRatchet.length 1 ∗
             optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
             optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
             optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
            memRegion (sp0 - 416#64 - 4624#64) 368)
      hcl1' hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      rw [session2MemcpySpec_pre_eq _ _ _ _
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm, hpq_toNat])]
      simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, sepConj_assoc] at hm ⊢
      apply satisfies_of_sep_focus hm
      sep_focus
    intro sf2 hcl2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm,
      hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h26_1, h27_1, h28_1, hfp_1]
      at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2
    have h216 : (sp0 - 288#64) + 0x48#64 = sp0 - 216#64 := bv_sub_add_lit sp0 288 72
    cases haddr_eq : x.addresses uuidTryParse with
    | none =>
      have haddrCap_eq : addrCap = BitVec.allOnes 64 := by
        simpa [haddr_eq, noneCap] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have hp56_eq : x.serPrefix5 uuidTryParse = x.serPrefix6 uuidTryParse :=
        (serPrefix6_of_addresses_none x haddr_eq).symm
      rw [optVecU8At_expose_cap_rest A ⟨BitVec.allOnes 64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) none (fun _ => rfl),
          h216]
      simp only [sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
      · simp only [wp_norm, arm64_norm,
          ← hp56_eq,
          hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h27_2, hfp_2,
          htr2, and_self]
      · rw [← hp56_eq, ← hp5_bv_eq,
            stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
            ← hp5_eq',
            ← serVec_pack_slice A sp0
                (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
                serPtr
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
                (BitVec.ofNat 64 x.pqRatchet.length)
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
                x.pqRatchet
                hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl]
        exact entails_of_sep_focus (by sep_focus)
    | some ad =>
      have haddrCap_eq : addrCap = 36#64 := by
        simpa [haddr_eq] using haddrCap
      clear haddrCap
      subst haddrCap_eq
      have htag6 := htag6_opt ad haddr_eq
      rw [optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
          h216]
      simp only [sepConj_assoc]
      apply signalMessageNew_of_sepWP_placed (mid := (blkPl_63).base + bv% (888)) hcl2
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
      intro hcl2'
      have hrew :
          ((serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length) ↦ₛ x.pqRatchet) ∗
          (pqCopyPtr ↦ₛ x.pqRatchet) ∗
          ((sp0 - 176#64) ↦₆₄
            BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗
          ((sp0 - 160#64) ↦₆₄ BitVec.ofNat 64 (x.serPrefix5 uuidTryParse).length) ∗
          A.live serPtr
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
            encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))) ∗
          memRegion
            (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
               encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
              BitVec.ofNat 64 x.pqRatchet.length)
            ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
              (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length -
              x.pqRatchet.length) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          optVecU8At A ⟨33#64, rkPtr⟩ (sp0 - 288#64) (some x.senderRatchetKey.serialize) ∗
          optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
            ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
          (((sp0 - 288#64) + 0x30#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          (((sp0 - 288#64) + 0x30#64 + 8#64) ↦₆₄ pqCopyPtr) ∗
          (((sp0 - 288#64) + 0x30#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ⌜pqCopyPtr ≠ 0#64 ∧ x.pqRatchet.length < 2 ^ 63⌝ ∗
          A.live pqCopyPtr x.pqRatchet.length 1 ∗
          ((sp0 - 216#64) ↦₆₄ 36#64) ∗
          optVecU8RestAt A ⟨36#64, addrPtr⟩ (sp0 - 216#64) (some ad) ∗
          optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗
          optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368 =
          (wireSignalMessageAt A
             (x.mkPins rkPtr ctCopyPtr (BitVec.ofNat 64 x.pqRatchet.length) pqCopyPtr 36#64 addrPtr)
             (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
           vecU8At A (sp0 - 176#64)
             (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
             serPtr (x.serPrefix5 uuidTryParse) ∗
           A.pool ∗ stackAt (sp0 - 416#64) computeMacStack) ∗
          (((sp0 - 408#64) ↦₆₄ rkPtr) ∗ ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
           ((sp0 - 344#64) ↦₆₄ ctCopyPtr)) := by
        rw [← hp5_bv_eq, stackAt_computeMac_to_encodeVarint (sp0 - 416#64),
            ← hp5_eq',
            ← serVec_pack_slice A sp0
                (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
                serPtr
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length)
                (BitVec.ofNat 64 x.pqRatchet.length)
                (BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (serPtr + BitVec.ofNat 64 (x.serPrefix4 uuidTryParse ++ 0x2a#8 ::
                  encodeVarint (BitVec.ofNat 64 x.pqRatchet.length)).length +
                  BitVec.ofNat 64 x.pqRatchet.length)
                (x.serPrefix4 uuidTryParse ++ 0x2a#8 :: encodeVarint (BitVec.ofNat 64 x.pqRatchet.length))
                x.pqRatchet
                hp4a_slice_le htot_lt hserPtr hpq_nil rfl rfl rfl rfl,
            wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr
              36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
            haddr_eq,
            optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
              ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
            h216]
        sep_focus
      refine signalMessageNew_seg2_seq_wpp' (by simp only [wp_norm, arm64_norm, htr2])
        (htag6 _ hcl2'
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, hrun2])
          (by simp only [wp_norm, arm64_norm, hsp2])
          (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
          (by simp only [wp_norm, arm64_norm, h19_2])
          (by simp only [wp_norm, arm64_norm, h20_2])
          (by simp only [wp_norm, arm64_norm, h21_2])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, h23_2])
          (by simp only [wp_norm, arm64_norm, h24_2])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, h27_2])
          (by simp only [wp_norm, arm64_norm, hfp_2]))
        hrew
        (fun _ _ hp => panicAllocPost_of_eq hp) ?_
      intro sm hpcm hrunm h1
      refine SepWPp.done hpcm hrunm ⟨by simpa only [wp_norm, arm64_norm, htr2, hfp_2] using h1, ?_⟩
      rw [wireSignalMessageAt_expose_pq A x rkPtr ctCopyPtr pqCopyPtr
            36#64 addrPtr (sp0 - 288#64) hpq_nil hpq_pin,
          haddr_eq,
          optVecU8At_expose_cap_rest A ⟨36#64, addrPtr⟩
            ((sp0 - 288#64) + 0x48#64) (some ad) (by nofun),
          h216]
      dsimp only
      exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.LibsignalTripleRatchet
