/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Repr
public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
import ProofLib.SepLogic.WPp

/-!
# Shared Representation and Deallocation Helpers for Unchunked States

**Checked by Lean.**

Representation predicates and deallocation entailments for `Authenticator`,
`ProtoAuthenticator`, `Option<ProtoAuthenticator>`, `spqr::v1::unchunked::*`, and
`spqr::proto::pq_ratchet::v1_state::unchunked::*` (with `Option<...>` niche encodings).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Second niche value `-2` (`0xFFFFFFFFFFFFFFFE#64`) used for the outer `Option` in
    `Option<V1State.Unchunked.NoHeaderReceived>` (`cmn x1, #2; b.eq`). -/
def none2Cap : BitVec 64 := 0xFFFFFFFFFFFFFFFE#64

@[simp, arm64_norm]
theorem none2Cap_add_two_beq_zero : (none2Cap + 2#64 == 0#64) = true := rfl

@[simp, arm64_norm]
theorem noneCap_add_two_beq_zero : (noneCap + 2#64 == 0#64) = false := rfl

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ¬((cap + 2#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have hmax : cap = 0xFFFFFFFFFFFFFFFE#64 := by bv_omega
  subst hmax
  revert h
  decide

/-! ## Stack Frame Helpers for 32-Byte Frames -/

/-- Callee-saved registers not saved in `[sp..sp+32]` when `x19, x29, x30` ARE saved in `[sp..sp+32]`. -/
@[reducible]
def Saved32x19Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem tail_stack_32_from_bottom_unchunked (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom sp allocHookStack 32 (by decide),
      show allocHookStack + 32 = dropStack32 from rfl,
      ← stackAt_dropStack32_split sp]

theorem cells4_entails_stack32_bottom (sp fp lr x20 x19 : BitVec 64) :
    stackAt (sp - 32#64) allocHookStack ∗
      (((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack := by
  rw [tail_stack_32_from_bottom_unchunked sp]
  exact sepConj_mono_right (cells4_sub32_entails sp fp lr x20 x19)

theorem tail_dealloc_unchunked_post (a : BitVec 64) (sz : Nat) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp allocHookStack ∗ memRegion a sz ∗ memRegion (sp - 4128#64) 32 ⊢
    memRegion a sz ∗ pool ∗ stackAt sp dropStack32 := by
  rw [stackAt_dropStack32_split_bottom sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## `Authenticator`, `ProtoAuthenticator`, and `Option<ProtoAuthenticator>` Layouts (`48` B) -/

/-- `spqr::proto::pq_ratchet::Authenticator` at `a` (`48` bytes = `0x30`, align `8`):
    * `a + 0x00..0x18`: `root_key: Vec<u8>` (tag 1, 24B)
    * `a + 0x18..0x30`: `mac_key: Vec<u8>` (tag 2, 24B) -/
def protoAuthenticatorAt (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator) : SepProp :=
  vecU8 A a auth.rootKey ∗
    vecU8 A (a + 24#64) auth.macKey

/-- `Option<spqr::proto::pq_ratchet::Authenticator>` at `a` (`48` bytes = `0x30`, align `8`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40` (`root_key.cap = -1` niche)
    * `some auth`: `protoAuthenticatorAt A a auth` -/
def optProtoAuthenticatorAt (A : RustAlloc) (a : BitVec 64) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => protoAuthenticatorAt A a auth

@[simp]
theorem optProtoAuthenticatorAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40) := rfl

@[simp]
theorem optProtoAuthenticatorAt_some (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator) :
    optProtoAuthenticatorAt A a (some auth) = protoAuthenticatorAt A a auth := rfl

theorem optProtoAuthenticatorAt_none_entails_memRegion_48 (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A a none ⊢ memRegion a 48 := by
  unfold optProtoAuthenticatorAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

/-- Deallocatable header + heap pair for two consecutive `Vec<u8>` fields (`48` bytes total). -/
structure TwoVecGhost where
  v1 : VecPin
  v2 : VecPin

def twoVecHeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8

theorem twoVecHeadersAt_entails_memRegion_48 (a : BitVec 64) (g : TwoVecGhost) :
    twoVecHeadersAt a g ⊢ memRegion a 48 := by
  unfold twoVecHeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.v2.cap g.v2.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  have hgroup :
      ((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 24) (b' := a + 24#64) rfl rfl (by decide)]
  exact sepConj_mono h1 h2

theorem protoAuthenticatorAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    protoAuthenticatorAt A a auth ⊢
      ∃∗ g : TwoVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63⌝ ∗
        twoVecHeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  unfold protoAuthenticatorAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 auth.macKey
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 h2) ?_
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.pure_right hlt ?_
  unfold twoVecHeadersAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

/-! ## Representation Predicates for `spqr::v1::unchunked::*` States -/

def unchunkedCt1SentSize : Nat := 128

/-- `spqr::v1::unchunked::send_ct::Ct1Sent` at `a` (`128` bytes = `0x80`, align `8`):
    * `+0`: `auth: Authenticator` (48B: `root_key` at `+0`, `mac_key` at `+24`)
    * `+48`: `hdr: Vec<u8>` (24B)
    * `+72`: `es: Vec<u8>` (24B)
    * `+96`: `ct1: Vec<u8>` (24B)
    * `+120`: `epoch: u64` (8B) -/
def unchunkedCt1SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.hdr ∗
    vecU8 A (a + 72#64) st.es ∗
    vecU8 A (a + 96#64) st.ct1 ∗
    ((a + 120#64) ↦₆₄ st.epoch)

def unchunkedEkSentSize : Nat := 80

/-- `spqr::v1::unchunked::send_ek::EkSent` at `a` (`80` bytes = `0x50`, align `8`):
    * `+0`: `auth: Authenticator` (48B: `root_key` at `+0`, `mac_key` at `+24`)
    * `+48`: `dk: Vec<u8>` (24B)
    * `+72`: `epoch: u64` (8B) -/
def unchunkedEkSentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.dk ∗
    ((a + 72#64) ↦₆₄ st.epoch)

def unchunkedCt1SentEkReceivedSize : Nat := 128

/-- `spqr::v1::unchunked::send_ct::Ct1SentEkReceived` at `a` (`128` bytes = `0x80`, align `8`):
    * `+0`: `auth: Authenticator` (48B: `root_key` at `+0`, `mac_key` at `+24`)
    * `+48`: `es: Vec<u8>` (24B)
    * `+72`: `ek: Vec<u8>` (24B)
    * `+96`: `ct1: Vec<u8>` (24B)
    * `+120`: `epoch: u64` (8B) -/
def unchunkedCt1SentEkReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.es ∗
    vecU8 A (a + 72#64) st.ek ∗
    vecU8 A (a + 96#64) st.ct1 ∗
    ((a + 120#64) ↦₆₄ st.epoch)

def unchunkedCt2SentSize : Nat := 56

/-- `spqr::v1::unchunked::send_ct::Ct2Sent` at `a` (`56` bytes = `0x38`, align `8`):
    * `+0`: `auth: Authenticator` (48B: `root_key` at `+0`, `mac_key` at `+24`)
    * `+48`: `epoch: u64` (8B) -/
def unchunkedCt2SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

def unchunkedEkSentCt1ReceivedSize : Nat := 104

/-- `spqr::v1::unchunked::send_ek::EkSentCt1Received` at `a` (`104` bytes = `0x68`, align `8`):
    * `+0`: `auth: Authenticator` (48B: `root_key` at `+0`, `mac_key` at `+24`)
    * `+48`: `dk: Vec<u8>` (24B)
    * `+72`: `ct1: Vec<u8>` (24B)
    * `+96`: `epoch: u64` (8B) -/
def unchunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.dk ∗
    vecU8 A (a + 72#64) st.ct1 ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-! ## Representation Predicates for `spqr::proto::pq_ratchet::v1_state::unchunked::*` -/

def protoUnchunkedCt1SentSize : Nat := 128

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent` at `a` (`128` bytes = `0x80`, align `8`):
    * `+0`: `hdr: Vec<u8>` (24B)
    * `+24`: `es: Vec<u8>` (24B)
    * `+48`: `ct1: Vec<u8>` (24B)
    * `+72`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+120`: `epoch: u64` (8B) -/
def protoUnchunkedCt1SentAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) : SepProp :=
  vecU8 A a st.hdr ∗
    vecU8 A (a + 24#64) st.es ∗
    vecU8 A (a + 48#64) st.ct1 ∗
    optProtoAuthenticatorAt A (a + 72#64) st.auth ∗
    ((a + 120#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>` at `a` (`128` bytes = `0x80`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120` (`hdr.cap = -1` niche)
    * `some st`: `protoUnchunkedCt1SentAt A a st` -/
def optProtoUnchunkedCt1SentAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1Sent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some st => protoUnchunkedCt1SentAt A a st

@[simp]
theorem optProtoUnchunkedCt1SentAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedCt1SentAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120) := rfl

@[simp]
theorem optProtoUnchunkedCt1SentAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) :
    optProtoUnchunkedCt1SentAt A a (some st) = protoUnchunkedCt1SentAt A a st := rfl

def protoUnchunkedCt1SentEkReceivedSize : Nat := 128

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived` at `a` (`128` bytes = `0x80`):
    * `+0`: `es: Vec<u8>` (24B)
    * `+24`: `ek: Vec<u8>` (24B)
    * `+48`: `ct1: Vec<u8>` (24B)
    * `+72`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+120`: `epoch: u64` (8B) -/
def protoUnchunkedCt1SentEkReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) : SepProp :=
  vecU8 A a st.es ∗
    vecU8 A (a + 24#64) st.ek ∗
    vecU8 A (a + 48#64) st.ct1 ∗
    optProtoAuthenticatorAt A (a + 72#64) st.auth ∗
    ((a + 120#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1SentEkReceived>` at `a` (`128` bytes):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120` (`es.cap = -1` niche)
    * `some st`: `protoUnchunkedCt1SentEkReceivedAt A a st` -/
def optProtoUnchunkedCt1SentEkReceivedAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some st => protoUnchunkedCt1SentEkReceivedAt A a st

@[simp]
theorem optProtoUnchunkedCt1SentEkReceivedAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedCt1SentEkReceivedAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120) := rfl

@[simp]
theorem optProtoUnchunkedCt1SentEkReceivedAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) :
    optProtoUnchunkedCt1SentEkReceivedAt A a (some st) = protoUnchunkedCt1SentEkReceivedAt A a st := rfl

def protoUnchunkedEkSentSize : Nat := 80

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::EkSent` at `a` (`80` bytes = `0x50`):
    * `+0`: `dk: Vec<u8>` (24B)
    * `+24`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+72`: `epoch: u64` (8B) -/
def protoUnchunkedEkSentAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSent) : SepProp :=
  vecU8 A a st.dk ∗
    optProtoAuthenticatorAt A (a + 24#64) st.auth ∗
    ((a + 72#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::EkSent>` at `a` (`80` bytes = `0x50`):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72` (`dk.cap = -1` niche)
    * `some st`: `protoUnchunkedEkSentAt A a st` -/
def optProtoUnchunkedEkSentAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some st => protoUnchunkedEkSentAt A a st

@[simp]
theorem optProtoUnchunkedEkSentAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedEkSentAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) := rfl

@[simp]
theorem optProtoUnchunkedEkSentAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSent) :
    optProtoUnchunkedEkSentAt A a (some st) = protoUnchunkedEkSentAt A a st := rfl

def protoUnchunkedEkSentCt1ReceivedSize : Nat := 104

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received` at `a` (`104` bytes = `0x68`):
    * `+0`: `dk: Vec<u8>` (24B)
    * `+24`: `ct1: Vec<u8>` (24B)
    * `+48`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+96`: `epoch: u64` (8B) -/
def protoUnchunkedEkSentCt1ReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  vecU8 A a st.dk ∗
    vecU8 A (a + 24#64) st.ct1 ∗
    optProtoAuthenticatorAt A (a + 48#64) st.auth ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received>` at `a` (`104` bytes):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96` (`dk.cap = -1` niche)
    * `some st`: `protoUnchunkedEkSentCt1ReceivedAt A a st` -/
def optProtoUnchunkedEkSentCt1ReceivedAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some st => protoUnchunkedEkSentCt1ReceivedAt A a st

@[simp]
theorem optProtoUnchunkedEkSentCt1ReceivedAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96) := rfl

@[simp]
theorem optProtoUnchunkedEkSentCt1ReceivedAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSentCt1Received) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a (some st) = protoUnchunkedEkSentCt1ReceivedAt A a st := rfl

def protoUnchunkedHeaderReceivedSize : Nat := 80

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived` at `a` (`80` bytes = `0x50`):
    * `+0`: `hdr: Vec<u8>` (24B)
    * `+24`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+72`: `epoch: u64` (8B) -/
def protoUnchunkedHeaderReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.HeaderReceived) : SepProp :=
  vecU8 A a st.hdr ∗
    optProtoAuthenticatorAt A (a + 24#64) st.auth ∗
    ((a + 72#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::HeaderReceived>` at `a` (`80` bytes):
    * `none`: `(a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72` (`hdr.cap = -1` niche)
    * `some st`: `protoUnchunkedHeaderReceivedAt A a st` -/
def optProtoUnchunkedHeaderReceivedAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some st => protoUnchunkedHeaderReceivedAt A a st

@[simp]
theorem optProtoUnchunkedHeaderReceivedAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) := rfl

@[simp]
theorem optProtoUnchunkedHeaderReceivedAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.HeaderReceived) :
    optProtoUnchunkedHeaderReceivedAt A a (some st) = protoUnchunkedHeaderReceivedAt A a st := rfl

def protoUnchunkedNoHeaderReceivedSize : Nat := 56

/-- `spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived` at `a` (`56` bytes = `0x38`):
    * `+0`: `auth: Option<ProtoAuthenticator>` (48B)
    * `+48`: `epoch: u64` (8B) -/
def protoUnchunkedNoHeaderReceivedAt (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.NoHeaderReceived) : SepProp :=
  optProtoAuthenticatorAt A a st.auth ∗
    ((a + 48#64) ↦₆₄ st.epoch)

/-- `Option<spqr::proto::pq_ratchet::v1_state::unchunked::NoHeaderReceived>` at `a` (`56` bytes = `0x38`):
    * `none`: `(a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48` (`auth.root_key.cap = -2` niche;
      `-1` is taken by `some { auth := none, .. }`)
    * `some st`: `protoUnchunkedNoHeaderReceivedAt A a st` -/
def optProtoUnchunkedNoHeaderReceivedAt (A : RustAlloc) (a : BitVec 64) :
    Option V1State.Unchunked.NoHeaderReceived → SepProp
  | none => (a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48
  | some st => protoUnchunkedNoHeaderReceivedAt A a st

@[simp]
theorem optProtoUnchunkedNoHeaderReceivedAt_none (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedNoHeaderReceivedAt A a none = ((a ↦₆₄ none2Cap) ∗ memRegion (a + 8#64) 48) := rfl

@[simp]
theorem optProtoUnchunkedNoHeaderReceivedAt_some (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.NoHeaderReceived) :
    optProtoUnchunkedNoHeaderReceivedAt A a (some st) = protoUnchunkedNoHeaderReceivedAt A a st := rfl

/-! ## Deallocation Entailments for 2-Vec (`56` B), 3-Vec (`80` B), 4-Vec (`104` B), and 5-Vec (`128` B) -/

structure ThreeVecGhost where
  v1 : VecPin
  v2 : VecPin
  v3 : VecPin

structure FourVecGhost where
  v1 : VecPin
  v2 : VecPin
  v3 : VecPin
  v4 : VecPin

structure FiveVecGhost where
  v1 : VecPin
  v2 : VecPin
  v3 : VecPin
  v4 : VecPin
  v5 : VecPin

def twoVec56HeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 16

theorem twoVec56HeadersAt_entails_memRegion_56 (a : BitVec 64) (g : TwoVecGhost) :
    twoVec56HeadersAt a g ⊢ memRegion a 56 := by
  unfold twoVec56HeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_32 (a + 24#64) g.v2.cap g.v2.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  have hgroup :
      ((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 16) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 32) (b' := a + 24#64) rfl rfl (by decide)]
  exact sepConj_mono h1 h2

def threeVec80HeadersAt (a : BitVec 64) (g : ThreeVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 16

theorem threeVec80HeadersAt_entails_memRegion_80 (a : BitVec 64) (g : ThreeVecGhost) :
    threeVec80HeadersAt a g ⊢ memRegion a 80 := by
  unfold threeVec80HeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.v2.cap g.v2.ptr
  have h3 := header_cells_entails_memRegion_32 (a + 48#64) g.v3.cap g.v3.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  have hgroup :
      ((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
        ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 16) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8) ∗
       (((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 56) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 24) (k := 32) (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

def fourVec104HeadersAt (a : BitVec 64) (g : FourVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8 ∗
  ((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 16

theorem fourVec104HeadersAt_entails_memRegion_104 (a : BitVec 64) (g : FourVecGhost) :
    fourVec104HeadersAt a g ⊢ memRegion a 104 := by
  unfold fourVec104HeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.v2.cap g.v2.ptr
  have h3 := header_cells_entails_memRegion_24 (a + 48#64) g.v3.cap g.v3.ptr
  have h4 := header_cells_entails_memRegion_32 (a + 72#64) g.v4.cap g.v4.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  have hgroup :
      ((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
        ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8 ∗
        ((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 16) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8) ∗
       (((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8) ∗
       (((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 80) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 24) (k := 56) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 24) (k := 32) (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))

def fiveVec128HeadersAt (a : BitVec 64) (g : FiveVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8 ∗
  ((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 8 ∗
  ((a + 96#64) ↦₆₄ g.v5.cap) ∗ ((a + 104#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 112#64) 16

theorem fiveVec128HeadersAt_entails_memRegion_128 (a : BitVec 64) (g : FiveVecGhost) :
    fiveVec128HeadersAt a g ⊢ memRegion a 128 := by
  unfold fiveVec128HeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.v2.cap g.v2.ptr
  have h3 := header_cells_entails_memRegion_24 (a + 48#64) g.v3.cap g.v3.ptr
  have h4 := header_cells_entails_memRegion_24 (a + 72#64) g.v4.cap g.v4.ptr
  have h5 := header_cells_entails_memRegion_32 (a + 96#64) g.v5.cap g.v5.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have hd1 : (a + 96#64) + 8#64 = a + 104#64 := by bv_omega
  have hd2 : (a + 96#64) + 16#64 = a + 112#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  rw [hd1, hd2] at h5
  have hgroup :
      ((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
        ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8 ∗
        ((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 8 ∗
        ((a + 96#64) ↦₆₄ g.v5.cap) ∗ ((a + 104#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 112#64) 16) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8) ∗
       (((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8) ∗
       (((a + 72#64) ↦₆₄ g.v4.cap) ∗ ((a + 80#64) ↦₆₄ g.v4.ptr) ∗ memRegion (a + 88#64) 8) ∗
       (((a + 96#64) ↦₆₄ g.v5.cap) ∗ ((a + 104#64) ↦₆₄ g.v5.ptr) ∗ memRegion (a + 112#64) 16)) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 104) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 24) (k := 80) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 24) (k := 56) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 24) (k := 32) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 h5)))

theorem unchunkedCt2SentAt_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) :
    unchunkedCt2SentAt A a st ⊢
      ∃∗ g : TwoVecGhost,
        twoVec56HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  let auth : Authenticator := st.auth
  change (vecU8 A a auth.rootKey ∗ vecU8 A (a + 24#64) auth.macKey) ∗ ((a + 48#64) ↦₆₄ st.epoch) ⊢ _
  unfold vecU8
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 auth.macKey
  have h3 := pointsTo64_entails_memRegion (a + 48#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) h3) ?_
  unfold twoVec56HeadersAt
  dsimp only
  have h16 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 8 = memRegion (a + 40#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8)
          (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  rw [← h16]
  exact Entails.of_eq (by ac_rfl)

theorem unchunkedEkSentAt_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A a st ⊢
      ∃∗ g : ThreeVecGhost,
        threeVec80HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr := by
  let auth : Authenticator := st.auth
  change (vecU8 A a auth.rootKey ∗ vecU8 A (a + 24#64) auth.macKey) ∗
    vecU8 A (a + 48#64) st.dk ∗
    ((a + 72#64) ↦₆₄ st.epoch) ⊢ _
  rw [sepConj_assoc (vecU8 A a auth.rootKey)]
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p3
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 auth.macKey
  have h3 := vecU8At_entails_capPtr_dealloc A (a + 48#64) c3 p3 st.dk
  have h4 := pointsTo64_entails_memRegion (a + 72#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))) ?_
  unfold threeVec80HeadersAt
  dsimp only
  have h16 : memRegion (a + 64#64) 8 ∗ memRegion (a + 72#64) 8 = memRegion (a + 64#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 64#64) (n := 8) (k := 8)
          (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  rw [← h16]
  exact Entails.of_eq (by ac_rfl)

theorem unchunkedEkSentCt1ReceivedAt_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ g : FourVecGhost,
        fourVec104HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr := by
  let auth : Authenticator := st.auth
  change (vecU8 A a auth.rootKey ∗ vecU8 A (a + 24#64) auth.macKey) ∗
    vecU8 A (a + 48#64) st.dk ∗ vecU8 A (a + 72#64) st.ct1 ∗
    ((a + 96#64) ↦₆₄ st.epoch) ⊢ _
  rw [sepConj_assoc (vecU8 A a auth.rootKey)]
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c4
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p4
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩, ⟨c4, p4⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 auth.macKey
  have h3 := vecU8At_entails_capPtr_dealloc A (a + 48#64) c3 p3 st.dk
  have h4 := vecU8At_entails_capPtr_dealloc A (a + 72#64) c4 p4 st.ct1
  have h5 := pointsTo64_entails_memRegion (a + 96#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 h5)))) ?_
  unfold fourVec104HeadersAt
  dsimp only
  have h16 : memRegion (a + 88#64) 8 ∗ memRegion (a + 96#64) 8 = memRegion (a + 88#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 8)
          (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  rw [← h16]
  exact Entails.of_eq (by ac_rfl)

theorem unchunkedCt1SentAt_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A a st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  let auth : Authenticator := st.auth
  change (vecU8 A a auth.rootKey ∗ vecU8 A (a + 24#64) auth.macKey) ∗
    vecU8 A (a + 48#64) st.hdr ∗ vecU8 A (a + 72#64) st.es ∗ vecU8 A (a + 96#64) st.ct1 ∗
    ((a + 120#64) ↦₆₄ st.epoch) ⊢ _
  rw [sepConj_assoc (vecU8 A a auth.rootKey)]
  unfold vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c4
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p4
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c5
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p5
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩, ⟨c4, p4⟩, ⟨c5, p5⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 auth.macKey
  have h3 := vecU8At_entails_capPtr_dealloc A (a + 48#64) c3 p3 st.hdr
  have h4 := vecU8At_entails_capPtr_dealloc A (a + 72#64) c4 p4 st.es
  have h5 := vecU8At_entails_capPtr_dealloc A (a + 96#64) c5 p5 st.ct1
  have h6 := pointsTo64_entails_memRegion (a + 120#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have hd1 : (a + 96#64) + 8#64 = a + 104#64 := by bv_omega
  have hd2 : (a + 96#64) + 16#64 = a + 112#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  rw [hd1, hd2] at h5
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono h5 h6))))) ?_
  unfold fiveVec128HeadersAt
  dsimp only
  have h16 : memRegion (a + 112#64) 8 ∗ memRegion (a + 120#64) 8 = memRegion (a + 112#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 112#64) (n := 8) (k := 8)
          (b' := a + 120#64) rfl (by bv_omega) (by decide)]
  rw [← h16]
  exact Entails.of_eq (by ac_rfl)

theorem unchunkedCt1SentEkReceivedAt_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec128HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr :=
  unchunkedCt1SentAt_entails_dealloc A a
    { epoch := st.epoch, auth := st.auth, hdr := st.es, es := st.ek, ct1 := st.ct1 }

/-! ## Deallocation Entailments for `proto::pq_ratchet::v1_state::unchunked::*` -/

/-- Headers for 1 `Vec<u8>` field at `+0` (`24`B). -/
def protoUnchunked1VecHeadersAt (a : BitVec 64) (v1 : VecPin) : SepProp :=
  (a ↦₆₄ v1.cap) ∗ ((a + 8#64) ↦₆₄ v1.ptr) ∗ memRegion (a + 16#64) 8

theorem protoUnchunked1VecHeadersAt_entails_memRegion_80 (a : BitVec 64) (v1 : VecPin) :
    protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ⊢
      memRegion a 80 := by
  unfold protoUnchunked1VecHeadersAt
  have h1 := header_cells_entails_memRegion_24 a v1.cap v1.ptr
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 56) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 48) (k := 8) (b' := a + 72#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left h1

theorem protoUnchunkedEkSentAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSent) :
    protoUnchunkedEkSentAt A a st ⊢
      ∃∗ v1 : VecPin,
        ⌜v1.cap.toNat < 2 ^ 63⌝ ∗
        protoUnchunked1VecHeadersAt a v1 ∗
        optProtoAuthenticatorAt A (a + 24#64) st.auth ∗
        memRegion (a + 72#64) 8 ∗
        vecCapPtrDealloc A v1.cap v1.ptr := by
  unfold protoUnchunkedEkSentAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  refine Entails.sepExists_right ⟨c1, p1⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 st.dk
  have h2 := pointsTo64_entails_memRegion (a + 72#64) st.epoch
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right h2)) ?_
  rw [sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.pure_right hlt ?_
  unfold protoUnchunked1VecHeadersAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

theorem protoUnchunkedHeaderReceivedAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.HeaderReceived) :
    protoUnchunkedHeaderReceivedAt A a st ⊢
      ∃∗ v1 : VecPin,
        ⌜v1.cap.toNat < 2 ^ 63⌝ ∗
        protoUnchunked1VecHeadersAt a v1 ∗
        optProtoAuthenticatorAt A (a + 24#64) st.auth ∗
        memRegion (a + 72#64) 8 ∗
        vecCapPtrDealloc A v1.cap v1.ptr :=
  protoUnchunkedEkSentAt_entails_dealloc A a
    { epoch := st.epoch, auth := st.auth, dk := st.hdr }

/-- Headers for 2 `Vec<u8>` fields at `+0, +24` (`48`B). -/
def protoUnchunked2VecHeadersAt (a : BitVec 64) (g : TwoVecGhost) : SepProp :=
  twoVecHeadersAt a g

theorem protoUnchunked2VecHeadersAt_entails_memRegion_104 (a : BitVec 64) (g : TwoVecGhost) :
    protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢
      memRegion a 104 := by
  unfold protoUnchunked2VecHeadersAt
  have h1 := twoVecHeadersAt_entails_memRegion_48 a g
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left h1

theorem protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.EkSentCt1Received) :
    protoUnchunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ g : TwoVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63⌝ ∗
        protoUnchunked2VecHeadersAt a g ∗
        optProtoAuthenticatorAt A (a + 48#64) st.auth ∗
        memRegion (a + 96#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  unfold protoUnchunkedEkSentCt1ReceivedAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 st.dk
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 st.ct1
  have h3 := pointsTo64_entails_memRegion (a + 96#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.pure_right hlt ?_
  unfold protoUnchunked2VecHeadersAt twoVecHeadersAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

/-- Headers for 3 `Vec<u8>` fields at `+0, +24, +48` (`72`B). -/
def protoUnchunked3VecHeadersAt (a : BitVec 64) (g : ThreeVecGhost) : SepProp :=
  (a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
  ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8

theorem protoUnchunked3VecHeadersAt_entails_memRegion_128 (a : BitVec 64) (g : ThreeVecGhost) :
    protoUnchunked3VecHeadersAt a g ∗ memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8 ⊢
      memRegion a 128 := by
  unfold protoUnchunked3VecHeadersAt
  have h1 := header_cells_entails_memRegion_24 a g.v1.cap g.v1.ptr
  have h2 := header_cells_entails_memRegion_24 (a + 24#64) g.v2.cap g.v2.ptr
  have h3 := header_cells_entails_memRegion_24 (a + 48#64) g.v3.cap g.v3.ptr
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  have hgroup :
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8 ∗
        ((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8 ∗
        ((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8) ∗
        memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) =
      (((a ↦₆₄ g.v1.cap) ∗ ((a + 8#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 16#64) 8) ∗
       (((a + 24#64) ↦₆₄ g.v2.cap) ∗ ((a + 32#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 40#64) 8) ∗
       (((a + 48#64) ↦₆₄ g.v3.cap) ∗ ((a + 56#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 64#64) 8) ∗
       memRegion (a + 72#64) 48 ∗ memRegion (a + 120#64) 8) := by ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := a) (n := 24) (k := 104) (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 24) (k := 80) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 24) (k := 56) (b' := a + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 48) (k := 8) (b' := a + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))

theorem protoUnchunkedCt1SentEkReceivedAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1SentEkReceived) :
    protoUnchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ g : ThreeVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63⌝ ∗
        protoUnchunked3VecHeadersAt a g ∗
        optProtoAuthenticatorAt A (a + 72#64) st.auth ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr := by
  unfold protoUnchunkedCt1SentEkReceivedAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p3
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 st.es
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) c2 p2 st.ek
  have h3 := vecU8At_entails_capPtr_dealloc A (a + 48#64) c3 p3 st.ct1
  have h4 := pointsTo64_entails_memRegion (a + 120#64) st.epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono_right h4)))) ?_
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.pure_right hlt ?_
  unfold protoUnchunked3VecHeadersAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

theorem protoUnchunkedCt1SentAt_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (st : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a st ⊢
      ∃∗ g : ThreeVecGhost,
        ⌜g.v1.cap.toNat < 2 ^ 63⌝ ∗
        protoUnchunked3VecHeadersAt a g ∗
        optProtoAuthenticatorAt A (a + 72#64) st.auth ∗
        memRegion (a + 120#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr :=
  protoUnchunkedCt1SentEkReceivedAt_entails_dealloc A a
    { epoch := st.epoch, auth := st.auth, es := st.hdr, ek := st.es, ct1 := st.ct1 }

theorem optProtoUnchunkedCt1SentAt_none_entails_memRegion_128 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedCt1SentAt A a none ⊢ memRegion a 128 := by
  unfold optProtoUnchunkedCt1SentAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 120) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedCt1SentEkReceivedAt A a none ⊢ memRegion a 128 :=
  optProtoUnchunkedCt1SentAt_none_entails_memRegion_128 A a

theorem optProtoUnchunkedEkSentAt_none_entails_memRegion_80 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedEkSentAt A a none ⊢ memRegion a 80 := by
  unfold optProtoUnchunkedEkSentAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem optProtoUnchunkedHeaderReceivedAt_none_entails_memRegion_80 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedHeaderReceivedAt A a none ⊢ memRegion a 80 :=
  optProtoUnchunkedEkSentAt_none_entails_memRegion_80 A a

theorem optProtoUnchunkedEkSentCt1ReceivedAt_none_entails_memRegion_104 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedEkSentCt1ReceivedAt A a none ⊢ memRegion a 104 := by
  unfold optProtoUnchunkedEkSentCt1ReceivedAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 (A : RustAlloc) (a : BitVec 64) :
    optProtoUnchunkedNoHeaderReceivedAt A a none ⊢ memRegion a 56 := by
  unfold optProtoUnchunkedNoHeaderReceivedAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a none2Cap)

end CryptoVerification.SpqrV1.Drop
