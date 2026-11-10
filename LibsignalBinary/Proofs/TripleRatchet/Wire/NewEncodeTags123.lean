/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<SignalMessage>::new` Segment 2a (`+0x100 .. +0x278`)

Separation-logic helpers for `wireSignalMessageAt` and `vecU8At` appends, storing
`wire::SignalMessage` and allocating the exact-capacity `serialized` buffer (`+0x100 → +0x1b8`),
and encoding protobuf tags 1–3 (`ratchet_key`, `counter`, `previous_counter`, `+0x1b8 → +0x278`).
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

/-! ## Separation-logic helpers for `wireSignalMessageAt` and `vecU8At` -/

theorem memRegion_8_eq_cells32 (a : BitVec 64) :
    memRegion a 8 =
      (∃∗ w0 : BitVec 32, a ↦₃₂ w0) ∗ (∃∗ w1 : BitVec 32, (a + 4#64) ↦₃₂ w1) := by
  rw [memRegion_split' (b := a) (b' := a + 4#64) (n := 4) (k := 4) (by decide) rfl (by decide),
      memRegion_four a, memRegion_four (a + 4#64)]

theorem memRegion_24_eq_cells3 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
      memRegion_eight a, memRegion_16_eq_cells2 (a + 8#64)]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_kernel
  rw [h16]

/-- Pin relation for the `addresses: Option<Vec<u8>>` words loaded from `sp0 - 312..sp0 - 288`. -/
def AddrPinOk (addrCap addrLen : BitVec 64)
    (addrOpt : Option (List (BitVec 8))) : Prop :=
  match addrOpt with
  | none => addrCap = noneCap
  | some ad => addrCap = 36#64 ∧ addrLen = 36#64 ∧ ad.length = 36

/-- Pin relation for the `pq_ratchet: Option<Vec<u8>>` words. -/
def PqPinOk (cap ptr : BitVec 64) (pq : List (BitVec 8)) : Prop :=
  if pq.isEmpty then
    cap = noneCap
  else
    cap = BitVec.ofNat 64 pq.length ∧ 0 < pq.length ∧ pq.length < 2 ^ 63 ∧ ptr ≠ 0#64

/-- Heap portion of `optSerializeAddressesAt` after extracting the 3 stack header words. -/
def optAddrBuf (A : RustAlloc) (cap ptr len : BitVec 64)
    (addrOpt : Option (List (BitVec 8))) : SepProp :=
  match addrOpt with
  | none => ⌜cap = noneCap⌝ ∗ emp
  | some ad =>
    ⌜cap = 36#64 ∧ len = 36#64 ∧ ad.length = 36⌝ ∗ boxU8Buf A ptr ad

theorem optSerializeAddressesAt_unpack (A : RustAlloc) (r : BitVec 64)
    (x : SignalMessageNewGhost) :
    optSerializeAddressesAt A r (x.addresses uuidTryParse) ⊢
      ∃∗ addrCap : BitVec 64, ∃∗ addrPtr : BitVec 64, ∃∗ addrLen : BitVec 64,
        (r ↦₆₄ addrCap) ∗ ((r + 8#64) ↦₆₄ addrPtr) ∗ ((r + 16#64) ↦₆₄ addrLen) ∗
        optAddrBuf A addrCap addrPtr addrLen (x.addresses uuidTryParse) := by
  cases had : x.addresses uuidTryParse with
  | none =>
    rw [signalMessageNew_optSerializeAddressesAt_none_eq]
    simp only [arm64_norm]
    refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro noneCap)
    refine Entails.trans ?_ (Entails.sepExists_intro w1)
    refine Entails.trans ?_ (Entails.sepExists_intro w0)
    simp only [optAddrBuf, sepConj_emp, arm64_norm]
    exact Entails.of_eq (by ac_rfl)
  | some ad =>
    have hlen : ad.length = 36 := addresses_length had
    rw [signalMessageNew_optSerializeAddressesAt_some_eq A r hlen]
    refine Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro 36#64)
    refine Entails.trans ?_ (Entails.sepExists_intro ptr)
    refine Entails.trans ?_ (Entails.sepExists_intro 36#64)
    simp only [optAddrBuf, arm64_norm]
    refine Entails.pure_right hlen ?_
    exact Entails.of_eq (by ac_rfl)

theorem optVecU8At_of_optAddrBuf (A : RustAlloc) (v cap ptr len : BitVec 64)
    (addrOpt : Option (List (BitVec 8))) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ len) ∗
      optAddrBuf A cap ptr len addrOpt ⊢
    optVecU8At A ⟨cap, ptr⟩ v addrOpt := by
  cases addrOpt with
  | none =>
    simp only [optAddrBuf, sepConj_emp, arm64_norm]
    refine Entails.pure_left fun hcap => ?_
    subst hcap
    rw [optVecU8At_none_eq]
    refine sepConj_mono_right ?_
    exact sepConj_mono (Entails.sepExists_intro ptr) (Entails.sepExists_intro len)
  | some ad =>
    simp only [optAddrBuf, arm64_norm]
    refine Entails.pure_left fun ⟨hcap, hlen_bv, hlen⟩ => ?_
    subst hcap; subst hlen_bv
    have h := optVecU8At_some_exact_eq A v ptr ad (by omega)
    rw [hlen] at h
    exact Entails.of_eq h.symm

theorem optVecU8At_rk_of_vecU8Buf (A : RustAlloc) (a rkPtr : BitVec 64) (pk : PublicKey) :
    ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ rkPtr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
      signalMessageNew_vecU8Buf A 33#64 rkPtr pk.serialize) =
    optVecU8At A ⟨33#64, rkPtr⟩ a (some pk.serialize) := by
  have hlen : pk.serialize.length = 33 := publicKey_serialize_length pk
  have h1 := vecU8Buf_eq_boxU8Buf A rkPtr pk.serialize (by omega)
  have h2 := optVecU8At_some_exact_eq A a rkPtr pk.serialize (by omega)
  rw [hlen] at h1 h2
  rw [h1, h2]

theorem optVecU8At_ct_of_vecU8Buf (A : RustAlloc) (a ctPtr : BitVec 64) (ct : List (BitVec 8))
    (hlen : ct.length < 2 ^ 63) :
    ((a ↦₆₄ BitVec.ofNat 64 ct.length) ∗ ((a + 8#64) ↦₆₄ ctPtr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
      signalMessageNew_vecU8Buf A (BitVec.ofNat 64 ct.length) ctPtr ct) =
    optVecU8At A ⟨BitVec.ofNat 64 ct.length, ctPtr⟩ a (some ct) := by
  rw [vecU8Buf_eq_boxU8Buf A ctPtr ct hlen, optVecU8At_some_exact_eq A a ctPtr ct hlen]

theorem cells3_entails_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_eq_cells3 a]
  exact sepConj_mono (Entails.sepExists_intro w0)
    (sepConj_mono (Entails.sepExists_intro w1) (Entails.sepExists_intro w2))

theorem optVecU8At_expose_cap (A : RustAlloc) (a : BitVec 64)
    (addrCap addrPtr addrLen : BitVec 64)
    (addrOpt : Option (List (BitVec 8)))
    (hpin : AddrPinOk addrCap addrLen addrOpt) :
    optVecU8At A ⟨addrCap, addrPtr⟩ a addrOpt =
      (a ↦₆₄ addrCap) ∗
      match addrOpt with
      | none => memRegion (a + 8#64) 16
      | some ad => ((a + 8#64) ↦₆₄ addrPtr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗ boxU8Buf A addrPtr ad := by
  cases addrOpt with
  | none =>
    simp only [AddrPinOk] at hpin
    subst hpin
    rfl
  | some ad =>
    rcases hpin with ⟨rfl, rfl, hlen⟩
    have h := optVecU8At_some_exact_eq A a addrPtr ad (by omega)
    rw [hlen] at h
    exact h

/-- Construct the `WireSignalMessageGhost` pins for `SignalMessage::new`. -/
def SignalMessageNewGhost.mkPins (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr : BitVec 64) : WireSignalMessageGhost :=
  { rk := ⟨33#64, rkPtr⟩
    ct := ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩
    pq := ⟨pqCap, pqCopyPtr⟩
    addr := ⟨addrCap, addrPtr⟩ }

theorem optVecU8At_rk_eq (A : RustAlloc) (a rkPtr : BitVec 64) (pk : PublicKey) :
    optVecU8At A ⟨33#64, rkPtr⟩ a (some pk.serialize) =
      ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ rkPtr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
        ⌜rkPtr ≠ 0#64 ∧ pk.serialize.length < 2 ^ 63⌝ ∗
        A.live rkPtr pk.serialize.length 1 ∗ (rkPtr ↦ₛ pk.serialize)) := by
  have hlen : pk.serialize.length = 33 := publicKey_serialize_length pk
  have hne : pk.serialize ≠ [] := publicKey_serialize_ne_nil pk
  have h := optVecU8At_some_exact_eq A a rkPtr pk.serialize (by omega)
  rw [hlen] at h
  rw [h]
  simp only [boxU8Buf, hne, ↓reduceIte]

theorem optVecU8At_ct_nonempty_eq (A : RustAlloc) (a ctPtr : BitVec 64) (ct : List (BitVec 8))
    (hne : ct ≠ []) (hlen : ct.length < 2 ^ 63) :
    optVecU8At A ⟨BitVec.ofNat 64 ct.length, ctPtr⟩ a (some ct) =
      ((a ↦₆₄ BitVec.ofNat 64 ct.length) ∗ ((a + 8#64) ↦₆₄ ctPtr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ct.length) ∗
        ⌜ctPtr ≠ 0#64 ∧ ct.length < 2 ^ 63⌝ ∗
        A.live ctPtr ct.length 1 ∗ (ctPtr ↦ₛ ct)) := by
  rw [optVecU8At_some_exact_eq A a ctPtr ct hlen]
  simp only [boxU8Buf, hne, ↓reduceIte]

theorem optVecU8At_pq_nonempty_eq (A : RustAlloc) (a pqCap pqPtr : BitVec 64)
    (pq : List (BitVec 8)) (hne : pq ≠ [])
    (hpin : PqPinOk pqCap pqPtr pq) :
    optVecU8At A ⟨pqCap, pqPtr⟩ a (if pq.isEmpty then none else some pq) =
      ((a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗
        ((a + 16#64) ↦₆₄ pqCap) ∗
        ⌜pqPtr ≠ 0#64 ∧ pq.length < 2 ^ 63⌝ ∗
        A.live pqPtr pq.length 1 ∗ (pqPtr ↦ₛ pq)) := by
  have hemp : pq.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [PqPinOk, hemp, Bool.false_eq_true, ↓reduceIte] at hpin ⊢
  rcases hpin with ⟨rfl, _, hlen, _⟩
  rw [optVecU8At_some_exact_eq A a pqPtr pq hlen]
  simp only [boxU8Buf, hne, ↓reduceIte]

theorem wireSignalMessageAt_expose_rk (A : RustAlloc) (x : SignalMessageNewGhost)
    (rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr a : BitVec 64) :
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
        a (x.protoMsg uuidTryParse) =
      ((rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
       ((a ↦₆₄ 33#64) ∗ ((a + 8#64) ↦₆₄ rkPtr) ∗ ((a + 16#64) ↦₆₄ 33#64) ∗
        ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗
        A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
        optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ (a + 0x18#64)
          (some x.ciphertext) ∗
        optVecU8At A ⟨pqCap, pqCopyPtr⟩ (a + 0x30#64)
          (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
        optVecU8At A ⟨addrCap, addrPtr⟩ (a + 0x48#64) (x.addresses uuidTryParse) ∗
        optU32At (a + 0x60#64) (some x.counter) ∗
        optU32At (a + 0x68#64) (some x.previousCounter))) := by
  simp only [wireSignalMessageAt, SignalMessageNewGhost.mkPins, SignalMessageNewGhost.protoMsg]
  rw [optVecU8At_rk_eq]
  ac_rfl

/-! ## `vecU8At` byte-append and slice-append equality lemmas -/

theorem vecU8At_expose_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        (∃∗ b0 : BitVec 8, (ptr + BitVec.ofNat 64 bs.length) ↦₈ b0) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [vecU8At_eq_of_pos A v cap ptr bs (by omega), hpure, pure_true, emp_sepConj,
      memRegion_split_one (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
        (by omega) (by omega)]

theorem vecU8At_pack_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (b : BitVec 8) (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ b) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) =
    vecU8At A v cap ptr (bs ++ [b]) := by
  rw [vecU8At_eq_of_pos A v cap ptr (bs ++ [b]) (by omega)]
  have hlen : (bs ++ [b]).length = bs.length + 1 := by simp
  have hbv : BitVec.ofNat 64 (bs.length + 1) = BitVec.ofNat 64 bs.length + 1#64 := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + 1#64) =
      ptr + BitVec.ofNat 64 bs.length + 1#64 := by bv_kernel
  have hsub : cap.toNat - (bs.length + 1) = cap.toNat - bs.length - 1 := by omega
  have hpure : (bs.length + 1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, ← pointsToBytes_append_singleton, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hn_pos : 0 < n) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
          (cap.toNat - bs.length - n)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  rw [vecU8At_eq_of_pos A v cap ptr bs (by omega), hpure, pure_true, emp_sepConj,
      memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
        (n := n) (k := cap.toNat - bs.length - n)
        (by omega) rfl (by omega)]

theorem vecU8At_pack_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ []) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
        (cap.toNat - bs.length - payload.length)) =
    vecU8At A v cap ptr (bs ++ payload) := by
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_eq_of_pos A v cap ptr (bs ++ payload) (by omega)]
  have hlen : (bs ++ payload).length = bs.length + payload.length := List.length_append
  have hbv : BitVec.ofNat 64 (bs.length + payload.length) =
      BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length) =
      ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by bv_kernel
  have hsub : cap.toNat - (bs.length + payload.length) =
      cap.toNat - bs.length - payload.length := by omega
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, pointsToBytes_append, hpure, pure_true, emp_sepConj]
  ac_rfl

/-! ## Storing `wire::SignalMessage` at `sp + 0x80` (`+0x100 → +0x13c`) -/

theorem memRegion_wire_112 (sp0 : BitVec 64) :
    memRegion (sp0 - 288#64) 112 =
      cells (sp0 - 288#64) 12 ∗
      (∃∗ w0 : BitVec 32, (sp0 - 192#64) ↦₃₂ w0) ∗
      (∃∗ w1 : BitVec 32, (sp0 - 188#64) ↦₃₂ w1) ∗
      (∃∗ w2 : BitVec 32, (sp0 - 184#64) ↦₃₂ w2) ∗
      (∃∗ w3 : BitVec 32, (sp0 - 180#64) ↦₃₂ w3) := by
  rw [memRegion_split' (b := sp0 - 288#64) (b' := sp0 - 192#64) (n := 96) (k := 16)
        (by decide) (by bv_kernel) (by decide),
      show (96 : Nat) = 8 * 12 by rfl, memRegion_cells (sp0 - 288#64) 12 (by decide),
      memRegion_split' (b := sp0 - 192#64) (b' := sp0 - 184#64) (n := 8) (k := 8)
        (by decide) (by bv_kernel) (by decide),
      memRegion_8_eq_cells32 (sp0 - 192#64),
      memRegion_8_eq_cells32 (sp0 - 184#64)]
  have h188 : sp0 - 192#64 + 4#64 = sp0 - 188#64 := by bv_kernel
  have h180 : sp0 - 184#64 + 4#64 = sp0 - 180#64 := by bv_kernel
  rw [h188, h180]
  ac_rfl

theorem pack_wire_post (A : RustAlloc)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32) :
    (((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
     ((sp0 - 320#64) ↦₆₄ pqCap) ∗
     (((sp0 - 312#64) ↦₆₄ addrCap) ∗ ((sp0 - 304#64) ↦₆₄ addrPtr) ∗ ((sp0 - 296#64) ↦₆₄ addrLen)) ∗
     (((sp0 - 288#64) ↦₆₄ 33#64) ∗ ((sp0 - 280#64) ↦₆₄ rkPtr) ∗ ((sp0 - 272#64) ↦₆₄ 33#64) ∗
       signalMessageNew_vecU8Buf A 33#64 rkPtr x.senderRatchetKey.serialize) ∗
     (((sp0 - 264#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 - 256#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 248#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) ctCopyPtr x.ciphertext) ∗
     (((sp0 - 240#64) ↦₆₄ pqCap) ∗ ((sp0 - 232#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet) ∗
     (((sp0 - 216#64) ↦₆₄ addrCap) ∗ ((sp0 - 208#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 200#64) ↦₆₄ addrLen) ∗
       optAddrBuf A addrCap addrPtr addrLen (x.addresses uuidTryParse)) ∗
     (((sp0 - 192#64) ↦₃₂ 1#32) ∗ ((sp0 - 188#64) ↦₃₂ x.counter)) ∗
     (((sp0 - 184#64) ↦₃₂ 1#32) ∗ ((sp0 - 180#64) ↦₃₂ x.previousCounter))) ⊢
    ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
    ((sp0 - 320#64) ↦₆₄ pqCap) ∗
    memRegion (sp0 - 312#64) 24 ∗
    wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
      (sp0 - 288#64) (x.protoMsg uuidTryParse) := by
  have hrk := optVecU8At_rk_of_vecU8Buf A (sp0 - 288#64) rkPtr x.senderRatchetKey
  have hct := optVecU8At_ct_of_vecU8Buf A (sp0 - 264#64) ctCopyPtr x.ciphertext (by omega)
  have hpq := optVecU8At_of_optPqBuf A (sp0 - 240#64) pqCap pqCopyPtr x.pqRatchet
  have haddr := optVecU8At_of_optAddrBuf A (sp0 - 216#64) addrCap addrPtr addrLen (x.addresses uuidTryParse)
  have hm24 := cells3_entails_memRegion_24 (sp0 - 312#64) addrCap addrPtr addrLen
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub] at hrk hct hpq haddr hm24
  simp (disch := decide) only [wireSignalMessageAt, SignalMessageNewGhost.mkPins,
    SignalMessageNewGhost.protoMsg, optU32At, bv_sub_add_lit, Nat.reduceSub]
  rw [hrk, hct]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono hm24
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hpq (sepConj_mono haddr (Entails.of_eq (by ac_rfl))))))))

namespace NewEncodeTags123Callees
theorem entails_of_sep_focus {P Q : SepProp} (h : P = Q ∗ emp) : P ⊢ Q :=
  Entails.of_eq (by rw [h, sepConj_emp])
theorem satisfies_of_sep_focus {m : Memory} {P Q : SepProp} (hm : m ⊨ P) (h : P = Q ∗ emp) : m ⊨ Q := by
  rwa [h, sepConj_emp] at hm
theorem encodedLenSpec_pre_eq (A : RustAlloc) (x : EncodedLenGhost) (s : State) (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.a) (hfit : WireLengthsFit x.m) (hsp : s.sp = sp_val) :
    (encodedLenSpec A).pre x s = wireSignalMessageAt A x.g x.a x.m ∗ stackAt sp_val encodedLenStack := by
  unfold encodedLenSpec; dsimp only; rw [hx0, hsp, eq_true hfit]; simp only [wp_norm, arm64_norm]
theorem rustAllocSpec_pre_eq (A : RustAlloc) (sz : Nat) (s : State) (sp_val : BitVec 64)
    (hx0 : (s.readReg64 .x0).toNat = sz) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hpos : 0 < sz) (hle : sz ≤ 9223372036854775807) (hsp : s.sp = sp_val) :
    (rustAllocSpec A).pre (sz, 1) s = A.pool ∗ stackAt sp_val allocHookStack := by
  have hlay : LayoutOk sz 1 = True := eq_true ⟨hpos, ⟨0, rfl⟩, by omega⟩
  unfold rustAllocSpec; dsimp only; rw [hx0, hx1, hsp, hlay]; simp only [wp_norm, arm64_norm]
theorem h4608_split (sp0 : BitVec 64) :
    memRegion (sp0 - 416#64 - 4624#64) 4608 =
      memRegion (sp0 - 416#64 - 4624#64) 528 ∗ memRegion (sp0 - 416#64 - 4096#64) 4080 := by
  rw [memRegion_split' (b := sp0 - 416#64 - 4624#64) (b' := sp0 - 416#64 - 4096#64)
    (n := 528) (k := 4080) (by decide) (bv_sub_add_lit (sp0 - 416#64) 4624 528).symm (by decide)]
theorem stackAt_allocHook_eq (sp0 : BitVec 64) :
    stackAt (sp0 - 416#64) allocHookStack =
      memRegion (sp0 - 416#64 - 4096#64) 4080 ∗ stackAt (sp0 - 416#64) encodedLenStack := by
  unfold stackAt allocHookStack encodedLenStack
  rw [memRegion_split' (b := sp0 - 416#64 - 4096#64) (b' := sp0 - 416#64 - 16#64)
    (n := 4080) (k := 16) (by decide) (bv_sub_add_lit (sp0 - 416#64) 4096 4080).symm (by decide)]
theorem session2MemcpySpec_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8)) (s0 : State)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : (s0.readReg64 .x2).toNat = bs.length) :
    framelessMemcpySpec.pre (dst, src, bs) s0 = memRegion dst bs.length ∗ (src ↦ₛ bs) := by
  simp only [framelessMemcpySpec, hx0, hx1, hx2, wp_norm, arm64_norm]
theorem encodeVarintSpec_post_eq (A : RustAlloc) (x : EncodeVarintGhost) (s0 sf : State)
    (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    (encodeVarintSpec A).post x s0 sf = ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧ (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗ vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt sp_val encodeVarintStack := by
  simp only [encodeVarintSpec, hsp0]
theorem encodeVarintSpec_pre_eq (A : RustAlloc) (x : EncodeVarintGhost) (s : State) (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 < 2 ^ 62) (hsp : s.sp = sp_val) :
    (encodeVarintSpec A).pre x s = vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt sp_val encodeVarintStack := by
  unfold encodeVarintSpec; dsimp only; rw [hx0, hx1, hsp, eq_true (Or.inr hlt)]; simp only [wp_norm, arm64_norm]
theorem encodeVarintSpec_pre_eq_or (A : RustAlloc) (x : EncodeVarintGhost) (s : State) (sp_val : BitVec 64)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 ≤ x.cap.toNat ∨ x.bs.length + 10 < 2 ^ 62) (hsp : s.sp = sp_val) :
    (encodeVarintSpec A).pre x s = vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt sp_val encodeVarintStack := by
  unfold encodeVarintSpec; dsimp only; rw [hx0, hx1, hsp, eq_true hlt]; simp only [wp_norm, arm64_norm]
theorem new_shim_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) noAllocShimSpec :=
  shim_ok_at2_ext hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

theorem new_alloc_ok_ext {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")) (rustAllocSpec A) :=
  alloc_ok_at_norm_ext hA (name := signalMessageNewName) (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))

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

theorem rustAllocSpecWithStack_pre_eq (A : RustAlloc) (sz : Nat) (s : State) (sp_val : BitVec 64)
    (hx0 : (s.readReg64 .x0).toNat = sz) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hpos : 0 < sz) (hle : sz ≤ 9223372036854775807) (hsp : s.sp = sp_val) :
    (rustAllocSpecWithStack A extHookStack).pre (sz, 1) s = A.pool ∗ stackAt sp_val extHookStack := by
  have hlay : LayoutOk sz 1 = True := eq_true ⟨hpos, ⟨0, rfl⟩, by omega⟩
  unfold rustAllocSpecWithStack; dsimp only; rw [hx0, hx1, hsp, hlay]; simp only [wp_norm, arm64_norm]

theorem h16896_split (sp0 : BitVec 64) :
    memRegion (sp0 - 416#64 - 16912#64) 16896 =
      memRegion (sp0 - 416#64 - 16912#64) 528 ∗ memRegion (sp0 - 416#64 - 16384#64) 16368 := by
  rw [memRegion_split' (b := sp0 - 416#64 - 16912#64) (b' := sp0 - 416#64 - 16384#64)
    (n := 528) (k := 16368) (by decide) (bv_sub_add_lit (sp0 - 416#64) 16912 528).symm (by decide)]

theorem h16896_split' (sp0 : BitVec 64) :
    memRegion (sp0 - 17328#64) 16896 =
      memRegion (sp0 - 416#64 - 16912#64) 528 ∗ memRegion (sp0 - 416#64 - 16384#64) 16368 := by
  rw [show sp0 - 17328#64 = sp0 - 416#64 - 16912#64 by bv_kernel, h16896_split sp0]

theorem stackAt_extHook_eq (sp0 : BitVec 64) :
    stackAt (sp0 - 416#64) extHookStack =
      memRegion (sp0 - 416#64 - 16384#64) 16368 ∗ stackAt (sp0 - 416#64) encodedLenStack :=
  signalMessageNew_stackAt_split_bottom' (sp0 - 416#64) extHookStack encodedLenStack 16368

theorem session2ShimSpecX_post_eq (img : Obj.Image) (s0 sf : State) (sp_val : BitVec 64)
    (hsp0 : s0.sp = sp_val) :
    (session2ShimSpecX.inImage img).post () s0 sf =
      ⌜sf.trace = s0.trace⌝ ∗ stackAt sp_val extHookStack := by
  simp only [Spec.inImage, session2ShimSpecX, hsp0]

theorem session2MemcpySpecX_pre_eq (dst src : BitVec 64) (bs : List (BitVec 8)) (s0 : State) (sp_val : BitVec 64)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src) (hx2 : (s0.readReg64 .x2).toNat = bs.length)
    (hsp : s0.sp = sp_val) :
    session2MemcpySpecX.pre (dst, src, bs) s0 = memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt sp_val extHookStack := by
  simp only [session2MemcpySpecX, hx0, hx1, hx2, hsp, wp_norm, arm64_norm]

theorem session2MemcpySpecX_post_eq (img : Obj.Image) (dst src : BitVec 64) (bs : List (BitVec 8))
    (s0 sf : State) (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    (session2MemcpySpecX.inImage img).post (dst, src, bs) s0 sf =
      ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      stackAt sp_val extHookStack := by
  simp only [Spec.inImage, session2MemcpySpecX, hsp0]

theorem encodeVarintSpecX_post_eq (A : RustAlloc) (img : Obj.Image) (x : EncodeVarintGhost) (s0 sf : State)
    (sp_val : BitVec 64) (hsp0 : s0.sp = sp_val) :
    ((encodeVarintSpecX A).inImage img).post x s0 sf = ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧ (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗ vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt sp_val encodeVarintStackX := by
  simp only [Spec.inImage, encodeVarintSpecX, hsp0]

theorem encodeVarintSpecX_pre_eq (A : RustAlloc) (img : Obj.Image) (x : EncodeVarintGhost) (s : State) (sp_val : BitVec 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = x.val) (hx1 : s.readReg64 .x1 = x.v)
    (hlt : x.bs.length + 10 < 2 ^ 62) (hsp : s.sp = sp_val) :
    ((encodeVarintSpecX A).inImage img).pre x s = vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt sp_val encodeVarintStackX := by
  have himg : (img.FrozenLoaded s ∧ s.symtab = img.symtab) = True := eq_true ⟨hF, hsym⟩
  unfold Spec.inImage encodeVarintSpecX; dsimp only; rw [himg, hx0, hx1, hsp, eq_true (Or.inr hlt)]; simp only [wp_norm, arm64_norm]

end NewEncodeTags123Callees

theorem new_store_wire_wp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen w376 w320 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 256#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hx9 : s.readReg64 .x9 = pqCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 316#64)
      s
      (((sp0 - 376#64) ↦₆₄ w376) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ addrCap) ∗
       ((sp0 - 304#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 296#64) ↦₆₄ addrLen) ∗
       memRegion (sp0 - 288#64) 112 ∗
       signalMessageNew_vecU8Buf A 33#64 rkPtr x.senderRatchetKey.serialize ∗
       signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       optAddrBuf A addrCap addrPtr addrLen (x.addresses uuidTryParse))
      (fun sf P =>
        (sf.sp = sp0 - 416#64 ∧
         sf.spAligned = true ∧
         sf.readReg64 .x0 = sp0 - 288#64 ∧
         sf.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sf.readReg64 .x20 = x.senderRatchetKeyA ∧
         sf.readReg64 .x21 = 33#64 ∧
         sf.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sf.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sf.readReg64 .x24 = x.ret ∧
         sf.readReg64 .x25 = pqCopyPtr ∧
         sf.readReg64 .x26 = ctCopyPtr ∧
         sf.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sf.readReg64 .x28 = rkPtr ∧
         sf.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sf s) ∧
        (P ⊢
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          memRegion (sp0 - 312#64) 24 ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse))) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  rw [memRegion_wire_112 sp0]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  new_fetches_range b (Rust.withPanics ext) 0x100 0x138
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp, hsp0_align, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, and_self]
  · exact Entails.trans (Entails.of_eq (by ac_rfl))
      (pack_wire_post A x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen hct_bound)

theorem new_store_wire_wp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen w376 w320 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 256#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hx9 : s.readReg64 .x9 = pqCap) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 316#64)
      s
      (((sp0 - 376#64) ↦₆₄ w376) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ addrCap) ∗
       ((sp0 - 304#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 296#64) ↦₆₄ addrLen) ∗
       memRegion (sp0 - 288#64) 112 ∗
       signalMessageNew_vecU8Buf A 33#64 rkPtr x.senderRatchetKey.serialize ∗
       signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       optAddrBuf A addrCap addrPtr addrLen (x.addresses uuidTryParse))
      (fun sf P =>
        (sf.sp = sp0 - 416#64 ∧
         sf.spAligned = true ∧
         sf.readReg64 .x0 = sp0 - 288#64 ∧
         sf.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sf.readReg64 .x20 = x.senderRatchetKeyA ∧
         sf.readReg64 .x21 = 33#64 ∧
         sf.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sf.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sf.readReg64 .x24 = x.ret ∧
         sf.readReg64 .x25 = pqCopyPtr ∧
         sf.readReg64 .x26 = ctCopyPtr ∧
         sf.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sf.readReg64 .x28 = rkPtr ∧
         sf.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sf s) ∧
        (P ⊢
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          memRegion (sp0 - 312#64) 24 ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse))) :=
  new_store_wire_wp_ext x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen w376 w320
    hct_bound s hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hx9

/-! ## `encoded_len` and `serialized` buffer allocation (`+0x13c → +0x1b8`) -/

theorem versionByte_word_eq (v : BitVec 8) :
    ((4#32 ||| ((v.setWidth 32) <<< 4)).setWidth 64).setWidth 8 = versionByte v := by
  unfold versionByte currentVersion
  bv_kernel

theorem encLen_overflow_checks {n : Nat} (h1 : 35 ≤ n) (h2 : n < 2 ^ 34) :
    BitVec.ult (BitVec.ofNat 64 n + 1#64) (BitVec.ofNat 64 n) = false ∧
    BitVec.ult (BitVec.ofNat 64 (n + 9)) (BitVec.ofNat 64 n + 1#64) = false ∧
    (BitVec.ofNat 64 (n + 9)).getLsbD 63 = false ∧
    BitVec.ult 9223372036854775806#64 (BitVec.ofNat 64 n) = false ∧
    BitVec.ofNat 64 n + 9#64 = BitVec.ofNat 64 (n + 9) ∧
    (BitVec.ofNat 64 (n + 9)).toNat = n + 9 := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hn1 : (BitVec.ofNat 64 n + 1#64).toNat = n + 1 := by
    rw [BitVec.toNat_add, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
  have hn9 : (BitVec.ofNat 64 (n + 9)).toNat = n + 9 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hn9⟩
  · simp [BitVec.ult, hn, hn1]
  · simp [BitVec.ult, hn1, hn9]
  · rw [BitVec.getLsbD_eq_getElem (by decide)]
    simp only [BitVec.getElem_eq_testBit_toNat, hn9]
    exact Nat.testBit_lt_two_pow (by omega)
  · simp [BitVec.ult, hn]; omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), hn9]

theorem pack_serPrefix0 (A : RustAlloc) (sp0 serPtr : BitVec 64)
    (v : BitVec 8) (encLen : Nat)
    (h1 : 35 ≤ encLen) (h2 : encLen < 2 ^ 34) (hptr : serPtr ≠ 0#64) :
    (((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 (encLen + 9)) ∗
     ((sp0 - 168#64) ↦₆₄ serPtr) ∗
     ((sp0 - 160#64) ↦₆₄ 1#64) ∗
     A.live serPtr (encLen + 9) 1 ∗
     (serPtr ↦₈ versionByte v) ∗
     memRegion (serPtr + 1#64) (encLen + 8)) =
    vecU8At A (sp0 - 176#64) (BitVec.ofNat 64 (encLen + 9)) serPtr [versionByte v] := by
  have htoNat : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_eq_of_pos A (sp0 - 176#64) (BitVec.ofNat 64 (encLen + 9)) serPtr [versionByte v]
        (by omega)]
  simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub,
    List.length_singleton, htoNat, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have hsub : encLen + 9 - 1 = encLen + 8 := by omega
  have hpure : (1 ≤ encLen + 9 ∧ encLen + 9 < 2 ^ 63 ∧ serPtr ≠ 0#64) = True :=
    eq_true ⟨by omega, by omega, hptr⟩
  rw [hsub, hpure, pure_true, emp_sepConj]

theorem new_alloc_ser_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hEncLen : EncodedLenOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have henc := encodedLen_ok_at_new_ext hEncLen
  have hshim := NewEncodeTags123Callees.new_shim_ok_ext hA
  have halloc := NewEncodeTags123Callees.new_alloc_ok_ext hA
  have ho15c := @oom_at_15c_ext b ext; clear hA hEncLen
  have hfit := wireLengthsFit_protoMsg x hct_bound hpq_bound
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
  have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ := encLen_overflow_checks henc_lo henc_hi
  have h_pos9 : 0 < (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 := by omega
  have h_le9 : (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 ≤ 9223372036854775807 := by omega
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  new_fetches_range b (Rust.withPanics ext) 0x13c 0x1b4
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
    (F := ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    henc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hx0]) hfit (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [encodedLenSpec, wp_norm, arm64_norm, hsp, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := ())
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          stackAt (sp0 - 416#64) encodedLenStack ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    hshim (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; simp only [noAllocShimSpec, sepConj_assoc, emp_sepConj, State.mem_setMem] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimSpec]; refine SepWPp.pure_elim fun htr2 => ?_; simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
  refine SepWPp.call (x := ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9, 1))
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion (sp0 - 416#64 - 4624#64) 528)
    halloc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [NewEncodeTags123Callees.h4608_split sp0] at hm
    rw [NewEncodeTags123Callees.rustAllocSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, h_add9_toNat])
          (by simp only [wp_norm, arm64_norm]) h_pos9 h_le9 (by simp only [wp_norm, arm64_norm, hsp2]),
        NewEncodeTags123Callees.stackAt_allocHook_eq sp0]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
    at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3; apply SepWPp.of_sepWP (mid := entry + bv% (348)); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    exact ho15c (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3]) (by simp only [wp_norm, arm64_norm, htr3])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]; refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [arm64_norm] at hoom hoom_beq
    rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) (by omega) (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::wire::SignalMessage as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
      (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) 1 ∗
            ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8) ∗
            A.pool ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 160#64) ↦₆₄ 1#64) ∗
            memRegion (sp0 - 416#64 - 4624#64) 4608)
      henc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (verW32 <<< 4)) = versionByte x.messageVersion := by
        have _ := hx20; rw [← hver]; unfold versionByte currentVersion; bv_kernel
      rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) hfit (by simp only [wp_norm, arm64_norm, hsp3])]
      simp only [wp_norm, arm64_norm, hsp2] at hm; rw [NewEncodeTags123Callees.stackAt_allocHook_eq sp0, hv] at hm; rw [NewEncodeTags123Callees.h4608_split sp0]
      simp only [sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
      at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    simp only [encodedLenSpec, wp_norm, arm64_norm, hsp3, htr3, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq, eq_false hoom,
        not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4, htr4, and_self]
    · rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)]; unfold SignalMessageNewGhost.serPrefix0
      simp only [wp_norm, arm64_norm, h22_4]
      rw [← pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
            (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length henc_lo henc_hi hoom]
      simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_alloc_ser_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hEncLen : EncodedLenOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_alloc_ser_wpp_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) hEncLen
    x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160
    w384 w380 verW32 hver hct_bound hpq_bound s hpc hrun hsp hsp_align
    hx0 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Encoding tags 1, 2, 3 (`+0x1b8 → +0x278`) -/

theorem serVec_expose_one (A : RustAlloc) (sp0 cap ptr len_bv addr1_bv : BitVec 64)
    (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hlen : len_bv = BitVec.ofNat 64 bs.length)
    (haddr1 : addr1_bv = ptr + len_bv + 1#64) :
    vecU8At A (sp0 - 176#64) cap ptr bs =
      (((sp0 - 176#64) ↦₆₄ cap) ∗ ((sp0 - 168#64) ↦₆₄ ptr) ∗ ((sp0 - 160#64) ↦₆₄ len_bv) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        (∃∗ b0 : BitVec 8, (ptr + len_bv) ↦₈ b0) ∗
        memRegion addr1_bv (cap.toNat - bs.length - 1)) := by
  subst hlen haddr1
  have h8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := bv_sub_add_lit sp0 176 8
  have h16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := bv_sub_add_lit sp0 176 16
  rw [vecU8At_expose_one A (sp0 - 176#64) cap ptr bs hlt hcap hptr, h8, h16]

theorem serVec_pack_one (A : RustAlloc) (sp0 cap ptr len_bv len1_bv addr1_bv : BitVec 64)
    (bs : List (BitVec 8)) (b : BitVec 8)
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64)
    (hlen : len_bv = BitVec.ofNat 64 bs.length)
    (hlen1 : len1_bv = len_bv + 1#64)
    (haddr1 : addr1_bv = ptr + len_bv + 1#64) :
    (((sp0 - 176#64) ↦₆₄ cap) ∗ ((sp0 - 168#64) ↦₆₄ ptr) ∗ ((sp0 - 160#64) ↦₆₄ len1_bv) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ ((ptr + len_bv) ↦₈ b) ∗
      memRegion addr1_bv (cap.toNat - bs.length - 1)) =
    vecU8At A (sp0 - 176#64) cap ptr (bs ++ [b]) := by
  subst hlen hlen1 haddr1
  have h8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := bv_sub_add_lit sp0 176 8
  have h16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := bv_sub_add_lit sp0 176 16
  rw [← vecU8At_pack_one A (sp0 - 176#64) cap ptr bs b hlt hcap hptr, h8, h16]

theorem serVec_expose_slice (A : RustAlloc) (sp0 cap ptr len_bv n_bv addr1_bv : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hn_pos : 0 < n)
    (hlen : len_bv = BitVec.ofNat 64 bs.length)
    (hn : n_bv = BitVec.ofNat 64 n)
    (haddr1 : addr1_bv = ptr + len_bv + n_bv) :
    vecU8At A (sp0 - 176#64) cap ptr bs =
      (((sp0 - 176#64) ↦₆₄ cap) ∗ ((sp0 - 168#64) ↦₆₄ ptr) ∗ ((sp0 - 160#64) ↦₆₄ len_bv) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + len_bv) n ∗
        memRegion addr1_bv (cap.toNat - bs.length - n)) := by
  subst hlen hn haddr1
  have h8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := bv_sub_add_lit sp0 176 8
  have h16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := bv_sub_add_lit sp0 176 16
  rw [vecU8At_expose_slice A (sp0 - 176#64) cap ptr bs n hle hcap hptr hn_pos, h8, h16]

theorem serVec_pack_slice (A : RustAlloc) (sp0 cap ptr len_bv n_bv len1_bv addr1_bv : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ [])
    (hlen : len_bv = BitVec.ofNat 64 bs.length)
    (hn : n_bv = BitVec.ofNat 64 payload.length)
    (hlen1 : len1_bv = len_bv + n_bv)
    (haddr1 : addr1_bv = ptr + len_bv + n_bv) :
    (((sp0 - 176#64) ↦₆₄ cap) ∗ ((sp0 - 168#64) ↦₆₄ ptr) ∗ ((sp0 - 160#64) ↦₆₄ len1_bv) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ ((ptr + len_bv) ↦ₛ payload) ∗
      memRegion addr1_bv (cap.toNat - bs.length - payload.length)) =
    vecU8At A (sp0 - 176#64) cap ptr (bs ++ payload) := by
  subst hlen hn hlen1 haddr1
  have h8 : sp0 - 176#64 + 8#64 = sp0 - 168#64 := bv_sub_add_lit sp0 176 8
  have h16 : sp0 - 176#64 + 16#64 = sp0 - 160#64 := bv_sub_add_lit sp0 176 16
  rw [← vecU8At_pack_slice A (sp0 - 176#64) cap ptr bs payload hle hcap hptr hne, h8, h16]

theorem tag123_pure_facts (x : SignalMessageNewGhost)
    (encLen : Nat)
    (henc_eq : encLen = (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length)
    (hlo : 35 ≤ encLen) (hhi : encLen < 2 ^ 34) :
    (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 ∧
    (BitVec.ofNat 64 (encLen + 9)).toNat < 2 ^ 63 ∧
    (x.serPrefix0).length = 1 ∧
    (BitVec.ofNat 64 (encLen + 9) == 1#64) = false ∧
    (x.serPrefix0 ++ [0x0a#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix0 ++ [0x0a#8]).length + (encodeVarint 33#64).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length = 3 ∧
    (BitVec.ofNat 64 (encLen + 9) - 3#64).ult 33#64 = false ∧
    x.senderRatchetKey.serialize.length = 33 ∧
    x.senderRatchetKey.serialize ≠ [] ∧
    ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) ++ x.senderRatchetKey.serialize =
      x.serPrefix1 uuidTryParse ∧
    (x.serPrefix1 uuidTryParse).length = 36 ∧
    (BitVec.ofNat 64 (encLen + 9) == 36#64) = false ∧
    (x.serPrefix1 uuidTryParse ++ [0x10#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix1 uuidTryParse ++ [0x10#8]).length + (encodeVarint (x.counter.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (x.serPrefix1 uuidTryParse ++ [0x10#8]) ++ encodeVarint (x.counter.zeroExtend 64) =
      x.serPrefix2 uuidTryParse ∧
    (x.serPrefix2 uuidTryParse).length < (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (BitVec.ofNat 64 (encLen + 9) == BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length) = false ∧
    (x.serPrefix2 uuidTryParse ++ [0x18#8]).length + 10 < 2 ^ 62 ∧
    (x.serPrefix2 uuidTryParse ++ [0x18#8]).length +
      (encodeVarint (x.previousCounter.zeroExtend 64)).length ≤
      (BitVec.ofNat 64 (encLen + 9)).toNat ∧
    (x.serPrefix2 uuidTryParse ++ [0x18#8]) ++ encodeVarint (x.previousCounter.zeroExtend 64) =
      x.serPrefix3 uuidTryParse := by
  have htot : (BitVec.ofNat 64 (encLen + 9)).toNat = encLen + 9 := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbv_lo : 44#64 ≤ BitVec.ofNat 64 (encLen + 9) := by
    rw [BitVec.le_def, htot]; change 44 ≤ encLen + 9; omega
  have hbv_hi : BitVec.ofNat 64 (encLen + 9) < 17179869193#64 := by
    rw [BitVec.lt_def, htot]; change encLen + 9 < 17179869193; omega
  have ⟨h0_len, h1_len, h12_le, h23_le, h34_le, h45_le, h56_le⟩ := serPrefix_lengths_le x
  have h6_len : (x.serPrefix6 uuidTryParse).length = 1 + encLen := by
    rw [henc_eq, serPrefix6_length]
  have hp1_eq : ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) ++ x.senderRatchetKey.serialize =
      x.serPrefix1 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix1, encodeBytesField_1_protoMsg, encodeVarint_33,
      List.append_assoc]
  have hp2_eq : (x.serPrefix1 uuidTryParse ++ [0x10#8]) ++ encodeVarint (x.counter.zeroExtend 64) =
      x.serPrefix2 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix2, encodeUint32Field_2_protoMsg, List.append_assoc]
  have hp3_eq : (x.serPrefix2 uuidTryParse ++ [0x18#8]) ++ encodeVarint (x.previousCounter.zeroExtend 64) =
      x.serPrefix3 uuidTryParse := by
    simp [SignalMessageNewGhost.serPrefix3, encodeUint32Field_3_protoMsg, List.append_assoc]
  have hp2_lt : (x.serPrefix2 uuidTryParse).length < encLen + 9 := by omega
  have hp2_toNat : (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length).toNat =
      (x.serPrefix2 uuidTryParse).length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨htot, by omega, h0_len, ?_, ?_, ?_, ?_, ?_,
    publicKey_serialize_length x.senderRatchetKey,
    publicKey_serialize_ne_nil x.senderRatchetKey,
    hp1_eq, h1_len, ?_, ?_, ?_, hp2_eq, by omega, ?_, ?_, ?_, hp3_eq⟩
  · bv_kernel
  · simp [h0_len]
  · simp [h0_len, encodeVarint_33, htot]
  · simp [h0_len, encodeVarint_33]
  · bv_kernel
  · bv_kernel
  · simp [h1_len]
  · have hlen2 : ((x.serPrefix1 uuidTryParse ++ [0x10#8]) ++
        encodeVarint (x.counter.zeroExtend 64)).length = (x.serPrefix2 uuidTryParse).length := by
      rw [hp2_eq]
    rw [List.length_append] at hlen2
    omega
  · apply beq_eq_false_iff_ne.mpr
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  · rw [List.length_append, List.length_singleton]; omega
  · have hlen3 : ((x.serPrefix2 uuidTryParse ++ [0x18#8]) ++
        encodeVarint (x.previousCounter.zeroExtend 64)).length = (x.serPrefix3 uuidTryParse).length := by
      rw [hp3_eq]
    rw [List.length_append] at hlen3
    omega

theorem new_encode_tag1_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 =
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix1 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint
  have hmemcpy := NewEncodeTags123Callees.new_memcpy_ok_ext hA; clear hA hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, h0_len, hcmp1, hvar1_lt, hvar1_fit, hbs1a_len, hcmp_rk, hrk_len, hrk_ne, hp1_eq, _, _, _, _, _, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 1#64 (serPtr + 2#64) x.serPrefix0 (by omega) htot_lt hserPtr (by simp [h0_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x1b8 0x214
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨33#64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix0 ++ [0x0a#8]⟩)
    (F := ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar1_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 1#64 2#64 (serPtr + 2#64) x.serPrefix0 0x0a#8 (by omega) htot_lt hserPtr (by simp [h0_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar1_fit with ⟨hcap', hptr'⟩; subst cap' ptr'
  rw [serVec_expose_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 3#64 33#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) 33
        (by omega) htot_lt hserPtr (by decide) rfl rfl (by bv_kernel),
      wireSignalMessageAt_expose_rk A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr (sp0 - 288#64)]
  simp only [sepConj_assoc]; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := (serPtr + 3#64, rkPtr, x.senderRatchetKey.serialize))
    (F := ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗ ((sp0 - 160#64) ↦₆₄ 3#64) ∗
          A.live serPtr (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)) ∗
          memRegion (serPtr + 36#64) ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
            ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length - 33) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          (((sp0 - 288#64) ↦₆₄ 33#64) ∗ (((sp0 - 288#64) + 8#64) ↦₆₄ rkPtr) ∗ (((sp0 - 288#64) + 16#64) ↦₆₄ 33#64) ∗
           ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗ A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64) (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗ optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [NewEncodeTags123Callees.session2MemcpySpec_pre_eq _ _ _ _ (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrk_len])]
    simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, hrk_len, sepConj_assoc] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpySpec, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2; apply SepWPp.of_sepWP_ret; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, htr2, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp1_eq,
        ← serVec_pack_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr 3#64 33#64 36#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) x.senderRatchetKey.serialize
            (by omega) htot_lt hserPtr hrk_ne rfl (by rw [hrk_len]) rfl (by bv_kernel), hrk_len]
    simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag1_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVarint : EncodeVarintOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 =
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix1 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new hVarint
  have hmemcpy := NewEncodeTags123Callees.new_memcpy_ok (b := b) (C := C) (ctl := ctl) (abs := abs); clear hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, h0_len, hcmp1, hvar1_lt, hvar1_fit, hbs1a_len, hcmp_rk, hrk_len, hrk_ne, hp1_eq, _, _, _, _, _, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 1#64 (serPtr + 2#64) x.serPrefix0 (by omega) htot_lt hserPtr (by simp [h0_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0x1b8 0x214
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨33#64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix0 ++ [0x0a#8]⟩)
    (F := ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar1_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 1#64 2#64 (serPtr + 2#64) x.serPrefix0 0x0a#8 (by omega) htot_lt hserPtr (by simp [h0_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar1_fit with ⟨hcap', hptr'⟩; subst cap' ptr'
  rw [serVec_expose_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 3#64 33#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) 33
        (by omega) htot_lt hserPtr (by decide) rfl rfl (by bv_kernel),
      wireSignalMessageAt_expose_rk A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr (sp0 - 288#64)]
  simp only [sepConj_assoc]; apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::new")); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := (serPtr + 3#64, rkPtr, x.senderRatchetKey.serialize))
    (F := ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗ ((sp0 - 160#64) ↦₆₄ 3#64) ∗
          A.live serPtr (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)) ∗
          memRegion (serPtr + 36#64) ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
            ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length - 33) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          (((sp0 - 288#64) ↦₆₄ 33#64) ∗ (((sp0 - 288#64) + 8#64) ↦₆₄ rkPtr) ∗ (((sp0 - 288#64) + 16#64) ↦₆₄ 33#64) ∗
           ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗ A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64) (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗ optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [NewEncodeTags123Callees.session2MemcpySpec_pre_eq _ _ _ _ (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrk_len])]
    simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, hrk_len, sepConj_assoc] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpySpec, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2; apply SepWPp.of_sepWP_ret; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, htr2, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp1_eq,
        ← serVec_pack_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr 3#64 33#64 36#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) x.senderRatchetKey.serialize
            (by omega) htot_lt hserPtr hrk_ne rfl (by rw [hrk_len]) rfl (by bv_kernel), hrk_len]
    simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag2_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix1 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix2 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint; clear hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, h1_len, hcmp2, hvar2_lt, hvar2_fit, hp2_eq, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 36#64 (serPtr + 37#64) (x.serPrefix1 uuidTryParse) (by omega) htot_lt hserPtr (by simp [h1_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x218 0x240
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨x.counter.zeroExtend 64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix1 uuidTryParse ++ [0x10#8]⟩)
    (F := ((sp0 - 384#64) ↦₃₂ x.counter) ∗ memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar2_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 36#64 37#64 (serPtr + 37#64) (x.serPrefix1 uuidTryParse) 0x10#8 (by omega) htot_lt hserPtr (by simp [h1_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar2_fit with ⟨rfl, rfl⟩; apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1]) (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp2_eq]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag2_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVarint : EncodeVarintOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix1 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix2 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag2_wpp_ext hVarint x sp0 rkPtr ctCopyPtr pqCopyPtr serPtr
    hct_le hpq_lt hserPtr s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29

theorem new_encode_tag3_wpp_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hVarint : EncodeVarintOkExt b A ext)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix2 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix3 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hvar := encodeVarint_ok_at_new_ext hVarint; clear hVarint
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp2_lt, hcmp3, hvar3_lt, hvar3_fit, hp3_eq⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length) (serPtr + BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64)
        (x.serPrefix2 uuidTryParse) hp2_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  new_fetches_range b (Rust.withPanics ext) 0x244 0x274
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr signalMessageNewName = entry
  examples_hide_fetches; apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new"))); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨x.previousCounter.zeroExtend 64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix2 uuidTryParse ++ [0x18#8]⟩)
    (F := ((sp0 - 320#64) ↦₆₄ pqCap) ∗ memRegion (sp0 - 416#64 - 4624#64) 368)
    hvar (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar3_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length) (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64) (x.serPrefix2 uuidTryParse) 0x18#8 hp2_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar3_fit with ⟨rfl, rfl⟩; apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1]) (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align, h19_1, h20_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp3_eq]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag3_wpp {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hVarint : EncodeVarintOk b C A ctl abs)
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr signalMessageNewName + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix2 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix3 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) :=
  new_encode_tag3_wpp_ext hVarint x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr
    hct_le hpq_lt hserPtr s hpc hrun hsp hsp_align
    hx19 hx21 hx23 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Relocatable `[LibsignalPlacement]` segment lemmas (Block `63`) -/

theorem new_store_wire_wp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen w376 w320 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 256#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (hx9 : s.readReg64 .x9 = pqCap) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 316#64)
      s
      (((sp0 - 376#64) ↦₆₄ w376) ∗
       ((sp0 - 320#64) ↦₆₄ w320) ∗
       ((sp0 - 312#64) ↦₆₄ addrCap) ∗
       ((sp0 - 304#64) ↦₆₄ addrPtr) ∗
       ((sp0 - 296#64) ↦₆₄ addrLen) ∗
       memRegion (sp0 - 288#64) 112 ∗
       signalMessageNew_vecU8Buf A 33#64 rkPtr x.senderRatchetKey.serialize ∗
       signalMessageNew_vecU8Buf A (BitVec.ofNat 64 x.ciphertext.length) ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       optAddrBuf A addrCap addrPtr addrLen (x.addresses uuidTryParse))
      (fun sf P =>
        (sf.sp = sp0 - 416#64 ∧
         sf.spAligned = true ∧
         sf.readReg64 .x0 = sp0 - 288#64 ∧
         sf.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sf.readReg64 .x20 = x.senderRatchetKeyA ∧
         sf.readReg64 .x21 = 33#64 ∧
         sf.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sf.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sf.readReg64 .x24 = x.ret ∧
         sf.readReg64 .x25 = pqCopyPtr ∧
         sf.readReg64 .x26 = ctCopyPtr ∧
         sf.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sf.readReg64 .x28 = rkPtr ∧
         sf.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sf s) ∧
        (P ⊢
          ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          memRegion (sp0 - 312#64) 24 ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse))) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  rw [memRegion_wire_112 sp0]; cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp, hsp0_align, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29, and_self]
  · exact Entails.trans (Entails.of_eq (by ac_rfl))
      (pack_wire_post A x sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr addrLen hct_bound)

theorem new_alloc_ser_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_panic : H lsRawVecHandleErrorSym = some Rust.panicked)
    (hEncLen : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 108) (encodedLenSpec A))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr w176 w168 w160 : BitVec 64)
    (w384 w380 verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp0 - 288#64)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 440#64)
      s
      (((sp0 - 384#64) ↦₃₂ w384) ∗
       ((sp0 - 380#64) ↦₃₂ w380) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       ((sp0 - 176#64) ↦₆₄ w176) ∗
       ((sp0 - 168#64) ↦₆₄ w168) ∗
       ((sp0 - 160#64) ↦₆₄ w160) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 ≠ 0#64 ∧
         sm.readReg64 .x23 = 1#64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            (sm.readReg64 .x22) x.serPrefix0 ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  have halloc := new_alloc_placed_ok h_alloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
  have ho15c := @oom_at_15c_placed _ H h_panic; clear h_shim h_alloc h_panic
  have hfit := wireLengthsFit_protoMsg x hct_bound hpq_bound
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_bound hpq_bound
  have ⟨h_adds1, h_cmp9, h_tbz, h_hi, h_add9_eq, h_add9_toNat⟩ := encLen_overflow_checks henc_lo henc_hi
  have h_pos9 : 0 < (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 := by omega
  have h_le9 : (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 ≤ 9223372036854775807 := by omega
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  apply SepWPp.of_sepWP (mid := lsmpl.base 108); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
    (F := ((sp0 - 384#64) ↦₃₂ w384) ∗ ((sp0 - 380#64) ↦₃₂ w380) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    hEncLen (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hx0]) hfit (by simp only [wp_norm, arm64_norm, hsp])]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  simp only [encodedLenSpec, wp_norm, arm64_norm, hsp, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_1, htr1⟩ => ?_
  apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := ())
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          stackAt (sp0 - 416#64) encodedLenStack ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          ((sp0 - 332#64) ↦₃₂ verW32) ∗ ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          A.pool ∗ memRegion (sp0 - 416#64 - 4624#64) 4608)
    hshim (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; simp only [noAllocShimSpec, sepConj_assoc, emp_sepConj, State.mem_setMem] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [noAllocShimSpec]; refine SepWPp.pure_elim fun htr2 => ?_; simp only [wp_norm, arm64_norm, htr1] at htr2
  apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
  refine SepWPp.call (x := ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9, 1))
    (F := wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
          ((sp0 - 176#64) ↦₆₄ w176) ∗ ((sp0 - 168#64) ↦₆₄ w168) ∗ ((sp0 - 160#64) ↦₆₄ w160) ∗
          memRegion (sp0 - 416#64 - 4624#64) 528)
    halloc (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm; rw [NewEncodeTags123Callees.h4608_split sp0] at hm
    rw [NewEncodeTags123Callees.rustAllocSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, h_add9_toNat])
          (by simp only [wp_norm, arm64_norm]) h_pos9 h_le9 (by simp only [wp_norm, arm64_norm, hsp2]),
        NewEncodeTags123Callees.stackAt_allocHook_eq sp0]
    simp only [State.mem_setPC, State.mem_writeReg64, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf3 hpc3 hrun3 hsp3 ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
  simp only [wp_norm, arm64_norm, hsp2, h19_2, h20_2, h21_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2]
    at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
  by_cases hoom : sf3.readReg64 .x0 = 0#64
  · have hoom0 : (sf3.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_oom]; refine SepWPp.pure_elim fun htr3 => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3; apply SepWPp.of_sepWP (mid := (blkPl_63).base + 348#64); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    exact ho15c (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3]) (by simp only [wp_norm, arm64_norm, htr3])
  · have hoom0 : (sf3.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [rustAllocSpec, hoom0, ↓reduceIte, pull_pure_alloc_ok]; refine SepWPp.pure_elim fun ⟨halign_ptr, htr3⟩ => ?_
    simp only [wp_norm, arm64_norm, htr2] at htr3
    have hoom_beq : (sf3.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [arm64_norm] at hoom hoom_beq
    rw [memRegion_split_one (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) (by omega) (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP (mid := lsmpl.base 108); wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
    refine SepWPp.call (x := ⟨sp0 - 288#64, x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr, x.protoMsg uuidTryParse⟩)
      (F := A.live (sf3.readReg64 (Reg.gpr 0#5)) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) 1 ∗
            ((sf3.readReg64 (Reg.gpr 0#5)) ↦₈ versionByte x.messageVersion) ∗
            memRegion (sf3.readReg64 (Reg.gpr 0#5) + 1#64) ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8) ∗
            A.pool ∗ ((sp0 - 384#64) ↦₃₂ x.counter) ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗ ((sp0 - 332#64) ↦₃₂ verW32) ∗
            ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
            ((sp0 - 168#64) ↦₆₄ sf3.readReg64 (Reg.gpr 0#5)) ∗ ((sp0 - 160#64) ↦₆₄ 1#64) ∗
            memRegion (sp0 - 416#64 - 4624#64) 4608)
      hEncLen (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun3])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp3, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
    · intro R' hm
      have hv : BitVec.zeroExtend 8 (4#64 ||| BitVec.zeroExtend 64 (verW32 <<< 4)) = versionByte x.messageVersion := by
        have _ := hx20; rw [← hver]; unfold versionByte currentVersion; bv_kernel
      rw [NewEncodeTags123Callees.encodedLenSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) hfit (by simp only [wp_norm, arm64_norm, hsp3])]
      simp only [wp_norm, arm64_norm, hsp2] at hm; rw [NewEncodeTags123Callees.stackAt_allocHook_eq sp0, hv] at hm; rw [NewEncodeTags123Callees.h4608_split sp0]
      simp only [sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
    intro sf4 hpc4 hrun4 hsp4 ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4⟩
    simp only [wp_norm, arm64_norm, hsp3, h19_3, h20_3, h21_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3]
      at hsp4 h19_4 h20_4 h21_4 h22_4 h23_4 h24_4 h25_4 h26_4 h27_4 h28_4 hfp_4
    simp only [encodedLenSpec, wp_norm, arm64_norm, hsp3, htr3, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0_4, htr4⟩ => ?_; apply SepWPp.of_sepWP_ret; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun4]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, hsp4, hsp0_align, h19_4, h20_4, h21_4, h22_4, ne_eq, eq_false hoom,
        not_false_eq_true, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, hfp_4, htr4, and_self]
    · rw [stackAt_computeMac_to_encodedLen (sp0 - 416#64)]; unfold SignalMessageNewGhost.serPrefix0
      simp only [wp_norm, arm64_norm, h22_4]
      rw [← pack_serPrefix0 A sp0 (sf3.readReg64 (Reg.gpr 0#5)) x.messageVersion
            (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length henc_lo henc_hi hoom]
      simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag1_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_mc : HookSat H lsMemcpySym framelessMemcpySpec)
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 536#64)
      s
      (((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
         (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr x.serPrefix0 ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 =
           BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9) ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = 36#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr)
            (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix1 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63); clear h_mc
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, h0_len, hcmp1, hvar1_lt, hvar1_fit, hbs1a_len, hcmp_rk, hrk_len, hrk_ne, hp1_eq, _, _, _, _, _, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 1#64 (serPtr + 2#64) x.serPrefix0 (by omega) htot_lt hserPtr (by simp [h0_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  refine signalMessageNew_call_placed (x := ⟨33#64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix0 ++ [0x0a#8]⟩)
    (F := ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          wireSignalMessageAt A (x.mkPins rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr) (sp0 - 288#64) (x.protoMsg uuidTryParse) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar1_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 1#64 2#64 (serPtr + 2#64) x.serPrefix0 0x0a#8 (by omega) htot_lt hserPtr (by simp [h0_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar1_fit with ⟨hcap', hptr'⟩; subst cap' ptr'
  rw [serVec_expose_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 3#64 33#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) 33
        (by omega) htot_lt hserPtr (by decide) rfl rfl (by bv_kernel),
      wireSignalMessageAt_expose_rk A x rkPtr ctCopyPtr pqCap pqCopyPtr addrCap addrPtr (sp0 - 288#64)]
  simp only [sepConj_assoc]; apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym); wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
  refine SepWPp.call (x := (serPtr + 3#64, rkPtr, x.senderRatchetKey.serialize))
    (F := ((sp0 - 176#64) ↦₆₄ BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)) ∗
          ((sp0 - 168#64) ↦₆₄ serPtr) ∗ ((sp0 - 160#64) ↦₆₄ 3#64) ∗
          A.live serPtr (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat 1 ∗
          (serPtr ↦ₛ ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64)) ∗
          memRegion (serPtr + 36#64) ((BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9)).toNat -
            ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64).length - 33) ∗
          A.pool ∗ stackAt (sp0 - 416#64) encodeVarintStack ∗ ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
          (((sp0 - 288#64) ↦₆₄ 33#64) ∗ (((sp0 - 288#64) + 8#64) ↦₆₄ rkPtr) ∗ (((sp0 - 288#64) + 16#64) ↦₆₄ 33#64) ∗
           ⌜rkPtr ≠ 0#64 ∧ x.senderRatchetKey.serialize.length < 2 ^ 63⌝ ∗ A.live rkPtr x.senderRatchetKey.serialize.length 1 ∗
           optVecU8At A ⟨BitVec.ofNat 64 x.ciphertext.length, ctCopyPtr⟩ ((sp0 - 288#64) + 0x18#64) (some x.ciphertext) ∗
           optVecU8At A ⟨pqCap, pqCopyPtr⟩ ((sp0 - 288#64) + 0x30#64) (if x.pqRatchet.isEmpty then none else some x.pqRatchet) ∗
           optVecU8At A ⟨addrCap, addrPtr⟩ ((sp0 - 288#64) + 0x48#64) (x.addresses uuidTryParse) ∗
           optU32At ((sp0 - 288#64) + 0x60#64) (some x.counter) ∗ optU32At ((sp0 - 288#64) + 0x68#64) (some x.previousCounter)) ∗
          memRegion (sp0 - 416#64 - 4624#64) 368)
    hmemcpy (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun1])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) (fun _ _ _ hm => not_satisfies_false_sepConj2 hm) ?_
  · intro R' hm
    rw [NewEncodeTags123Callees.session2MemcpySpec_pre_eq _ _ _ _ (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrk_len])]
    simp only [State.mem_setPC, State.mem_setPState, State.mem_writeReg64, hrk_len, sepConj_assoc] at hm ⊢
    exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
  simp only [wp_norm, arm64_norm, hsp1, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1]
    at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
  simp only [framelessMemcpySpec, sepConj_assoc]; refine SepWPp.pure_elim fun ⟨hx0_2, htr2⟩ => ?_
  simp only [wp_norm, arm64_norm, htr1] at htr2; apply SepWPp.of_sepWP_ret; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun2]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp2, hsp0_align, h19_2, h20_2, h21_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, htr2, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp1_eq,
        ← serVec_pack_slice A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr 3#64 33#64 36#64 (serPtr + 36#64) ((x.serPrefix0 ++ [0x0a#8]) ++ encodeVarint 33#64) x.senderRatchetKey.serialize
            (by omega) htot_lt hserPtr hrk_ne rfl (by rw [hrk_len]) rfl (by bv_kernel), hrk_len]
    simp only [sepConj_assoc]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag2_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 =
      BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 580#64)
      s
      (((sp0 - 384#64) ↦₃₂ x.counter) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix1 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 384#64) ↦₃₂ x.counter) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix2 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, h1_len, hcmp2, hvar2_lt, hvar2_fit, hp2_eq, _, _, _, _, _⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr 36#64 (serPtr + 37#64) (x.serPrefix1 uuidTryParse) (by omega) htot_lt hserPtr (by simp [h1_len]) (by bv_kernel)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  refine signalMessageNew_call_placed (x := ⟨x.counter.zeroExtend 64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix1 uuidTryParse ++ [0x10#8]⟩)
    (F := ((sp0 - 384#64) ↦₃₂ x.counter) ∗ memRegion (sp0 - 416#64 - 4624#64) 368)
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar2_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr 36#64 37#64 (serPtr + 37#64) (x.serPrefix1 uuidTryParse) 0x10#8 (by omega) htot_lt hserPtr (by simp [h1_len]) rfl (by bv_kernel)]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar2_fit with ⟨rfl, rfl⟩; apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1]) (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align, h19_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp2_eq]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

theorem new_encode_tag3_wpp_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hVarint : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 10)
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (x : SignalMessageNewGhost)
    (sp0 rkPtr ctCopyPtr pqCap pqCopyPtr serPtr : BitVec 64)
    (hct_le : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_lt : x.pqRatchet.length < 2 ^ 32)
    (hserPtr : serPtr ≠ 0#64)
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx23 : s.readReg64 .x23 = x.previousCounter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = pqCopyPtr)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 632#64)
      s
      (((sp0 - 320#64) ↦₆₄ pqCap) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
         serPtr (x.serPrefix2 uuidTryParse) ∗
       A.pool ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = pqCap ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x23 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = pqCopyPtr ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ pqCap) ∗
          vecU8At A (sp0 - 176#64)
            (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
            serPtr (x.serPrefix3 uuidTryParse) ∗
          A.pool ∗ stackAt (sp0 - 416#64) computeMacStack))
      (PanicAllocPost s) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  have ⟨henc_lo, henc_hi⟩ := encode_protoMsg_length_bounds x hct_le hpq_lt
  have ⟨htot_toNat, htot_lt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp2_lt, hcmp3, hvar3_lt, hvar3_fit, hp3_eq⟩ :=
    tag123_pure_facts x (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length rfl henc_lo henc_hi
  rw [serVec_expose_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
        serPtr (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length) (serPtr + BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64)
        (x.serPrefix2 uuidTryParse) hp2_lt htot_lt hserPtr rfl rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; refine SepWPp.exists_elim fun b1 => ?_
  apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 10) hcl; wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcl0
  refine signalMessageNew_call_placed (x := ⟨x.previousCounter.zeroExtend 64, sp0 - 176#64, BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9), serPtr, x.serPrefix2 uuidTryParse ++ [0x18#8]⟩)
    (F := ((sp0 - 320#64) ↦₆₄ pqCap) ∗ memRegion (sp0 - 416#64 - 4624#64) 368)
    hcl0 hVarint (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align]) (by simp only [wp_norm, arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hm => by simpa only [encodeVarintSpec, allocFailedIn, State.trace_setMem, State.trace_setPC, State.trace_setPState, State.trace_writeReg64, arm64_norm] using allowPanic_frame id hm) ?_
  · intro R' hm; rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64)] at hm
    rw [NewEncodeTags123Callees.encodeVarintSpec_pre_eq A _ _ (sp0 - 416#64) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm]) hvar3_lt (by simp only [wp_norm, arm64_norm, hsp]),
        ← serVec_pack_one A sp0 (BitVec.ofNat 64 ((LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9))
          serPtr (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length) (BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64)
          (serPtr + BitVec.ofNat 64 (x.serPrefix2 uuidTryParse).length + 1#64) (x.serPrefix2 uuidTryParse) 0x18#8 hp2_lt htot_lt hserPtr rfl rfl rfl]
    simp only [State.mem_setMem, sepConj_assoc] at hm ⊢; exact NewEncodeTags123Callees.satisfies_of_sep_focus hm (by sep_focus)
  intro sf1 _ hpc1 hrun1 hsp1 ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, hsp, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx28, hx29]
    at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  rw [NewEncodeTags123Callees.encodeVarintSpec_post_eq A _ _ sf1 (sp0 - 416#64) (by simp only [wp_norm, arm64_norm, hsp])]; simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_; simp only [wp_norm, arm64_norm] at htr1; simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun ⟨_, hno_grow⟩ => ?_
  rcases hno_grow hvar3_fit with ⟨rfl, rfl⟩; apply SepWPp.of_sepWP_ret
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc1]) (by simp only [wp_norm, arm64_norm, hrun1]) ⟨?_, ?_⟩
  · simp only [wp_norm, arm64_norm, hsp1, hsp0_align, h19_1, h20_1, h21_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, htr1, and_self]
  · rw [stackAt_computeMac_to_encodeVarint (sp0 - 416#64), ← hp3_eq]; exact NewEncodeTags123Callees.entails_of_sep_focus (by sep_focus)

end CryptoVerification.LibsignalTripleRatchet
