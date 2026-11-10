/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import ProofLib.SepLogic.Bytes
import ProofLib.VCGen

/-!
# Representation Predicates for `spqr::authenticator::Authenticator` (`48` bytes)

`spqr::authenticator::Authenticator` (`src/authenticator.rs:26–29`) and
`spqr::proto::pq_ratchet::Authenticator` (`ProtoAuthenticator` / `AuthenticatorPB`) have identical
in-memory layouts (`48` bytes = `0x30`, alignment `8`):
- `p + 0x00` (`24` bytes): `root_key: Vec<u8>`
- `p + 0x18` (`24` bytes): `mac_key: Vec<u8>`
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib
open CryptoGames.HMAC
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr

/-! ## Layout Constants -/

abbrev authenticatorSize : Nat := 48

abbrev authenticatorAlign : Nat := 8

/-! ## Symbol Names in `libsignalSessionCode` -/

abbrev authNewName : String :=
  "<spqr::authenticator::Authenticator>::new"

abbrev authMacHdrName : String :=
  "<spqr::authenticator::Authenticator>::mac_hdr"

abbrev authFromPbName : String :=
  "<spqr::authenticator::Authenticator>::from_pb"

abbrev authUpdateName : String :=
  "<spqr::authenticator::Authenticator>::update"

abbrev authEncodeLocal1Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#1]"

abbrev authEncodeLocal2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]"

abbrev authMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::Authenticator, &mut &[u8]>"

/-! ## Ghost Pins and Representation Predicates -/

/-- Ghost `(cap, ptr)` pins for the two `Vec<u8>` fields of an `Authenticator` (`48` bytes). -/
abbrev AuthenticatorGhost := AuthenticatorPBGhost

/-- Pinned representation predicate for `spqr::authenticator::Authenticator` at `p` (`48` bytes = `0x30`):
- `p + 0x00`: `root_key: Vec<u8>` (`24` bytes)
- `p + 0x18`: `mac_key: Vec<u8>` (`24` bytes) -/
def authenticatorPinAt (A : RustAlloc) (g : AuthenticatorGhost) (p : BitVec 64)
    (auth : Authenticator) : SepProp :=
  vecU8At A p g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
    vecU8At A (p + 0x18#64) g.macKey.cap g.macKey.ptr auth.macKey

/-- Unpinned representation predicate for `spqr::authenticator::Authenticator` at `p` (`48` bytes = `0x30`),
existentially quantifying the `(cap, ptr)` pairs of `root_key` and `mac_key`. -/
def authenticatorAt (A : RustAlloc) (p : BitVec 64) (auth : Authenticator) : SepProp :=
  vecU8 A p auth.rootKey ∗
    vecU8 A (p + 0x18#64) auth.macKey

/-! ## Bridge Lemmas to `ProtoRepr.authenticatorPBAt` / `authenticatorPBPinnedAt` -/

@[simp]
theorem authenticatorPinAt_eq_authenticatorPBPinnedAt_intoPb (A : RustAlloc)
    (g : AuthenticatorGhost) (p : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g p auth = authenticatorPBPinnedAt A g p auth.intoPb :=
  rfl

@[simp]
theorem authenticatorAt_eq_authenticatorPBAt_intoPb (A : RustAlloc)
    (p : BitVec 64) (auth : Authenticator) :
    authenticatorAt A p auth = authenticatorPBAt A p auth.intoPb :=
  rfl

@[simp]
theorem authenticatorPBPinnedAt_eq_authenticatorPinAt_fromPb (A : RustAlloc)
    (g : AuthenticatorGhost) (p : BitVec 64) (pb : ProtoAuthenticator) :
    authenticatorPBPinnedAt A g p pb = authenticatorPinAt A g p (Authenticator.fromPb pb) :=
  rfl

@[simp]
theorem authenticatorPBAt_eq_authenticatorAt_fromPb (A : RustAlloc)
    (p : BitVec 64) (pb : ProtoAuthenticator) :
    authenticatorPBAt A p pb = authenticatorAt A p (Authenticator.fromPb pb) :=
  rfl

theorem authenticatorAt_eq_exists_pinned (A : RustAlloc) (p : BitVec 64) (auth : Authenticator) :
    authenticatorAt A p auth = ∃∗ g : AuthenticatorGhost, authenticatorPinAt A g p auth :=
  authenticatorPBAt_eq_exists_pinned A p auth.intoPb

theorem authenticatorPinAt_entails_authenticatorAt (A : RustAlloc)
    (g : AuthenticatorGhost) (p : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g p auth ⊢ authenticatorAt A p auth := by
  rw [authenticatorAt_eq_exists_pinned]
  exact Entails.sepExists_right g (Entails.refl _)

theorem memRegion_authenticator_split (p : BitVec 64) :
    memRegion p 48 = memRegion p 24 ∗ memRegion (p + 0x18#64) 24 :=
  ProofLib.memRegion_split p 24 24 (by decide)

/-! ## Shared Byte, `Vec<u8>`, and `.rodata` Helpers for `Authenticator` Proofs -/

/-- Big-endian 8-byte encoding via `rev64` matches `toBEBytes 8`. -/
theorem unpack64_rev64_eq_toBEBytes (v : BitVec 64) :
    unpack64 (rev64 v) = toBEBytes 8 v := by
  have hr : rev64 v =
      v.extractLsb' 0 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 24 8 ++
      v.extractLsb' 32 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 56 8 := by
    simp only [rev64]
  rw [hr]
  dsimp only [unpack64, toBEBytes, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldr]
  generalize v.extractLsb' 0 8 = b0
  generalize v.extractLsb' 8 8 = b1
  generalize v.extractLsb' 16 8 = b2
  generalize v.extractLsb' 24 8 = b3
  generalize v.extractLsb' 32 8 = b4
  generalize v.extractLsb' 40 8 = b5
  generalize v.extractLsb' 48 8 = b6
  generalize v.extractLsb' 56 8 = b7
  refine List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits,
    List.cons_eq_cons.mpr ⟨by bv_bits, List.cons_eq_cons.mpr ⟨by bv_bits, rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem pointsTo64_rev64_eq_toBEBytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ rev64 v) = (a ↦ₛ toBEBytes 8 v) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_rev64_eq_toBEBytes]

@[simp] theorem toBEBytes_8_length (v : BitVec 64) :
    (toBEBytes 8 v).length = 8 := by
  simp [toBEBytes]

/-- Expose `(ptr ↦ₛ bs)` from `vecU8At A v cap ptr bs`:
even when `cap = 0`, `bs.length ≤ (0#64).toNat = 0` implies `bs = []` so `(ptr ↦ₛ bs) = emp`. -/
theorem vecU8At_expose_entails (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hle, hlt, hptr⟩ => ?_
  refine Entails.trans (Entails.pure_right ⟨hle, hlt, hptr⟩ ?_)
    (Entails.of_eq (show ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) = _ by ac_rfl))
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by change bs.length ≤ 0 at hle; omega)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem vecU8At_unexpose_entails (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ⊢
      vecU8At A v cap ptr bs := by
  unfold vecU8At vecHeader
  rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
  refine Entails.pure_right ⟨hle, hlt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by change bs.length ≤ 0 at hle; omega)
    subst hbs
    simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem subroutine_ok_inImage_rodata1_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {roAddr : BitVec 64} {roBytes : List (BitVec 8)}
    {spec : Spec α}
    (hro : ∀ {s : State} (_ : img.FrozenLoaded s) {P : SepProp},
      (s.mem ⊨ P) → (s.mem ⊨ (roAddr ↦ᵣ roBytes) ∗ P))
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
          (roAddr ↦ᵣ roBytes) ∗ spec.pre x s
        post := fun x s0 sf =>
          (roAddr ↦ᵣ roBytes) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hq => ?_)
  · simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hL, hpre⟩
    exact ⟨hL, hro hL.1 hpre⟩
  · simp only [Spec.inImage]
    dsimp only at hq
    rw [sepConj_assoc] at hq
    exact Satisfies.of_sep_right hq

end CryptoVerification.SpqrV1.Auth

