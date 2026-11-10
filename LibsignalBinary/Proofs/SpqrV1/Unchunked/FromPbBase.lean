/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.Defs
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPb
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp

/-!
# Layout Predicates and Specifications for `<Ct1Sent>::from_pb` and `<EkSentCt1Received>::from_pb`

Defines binary layout predicates (`ct1SentAt`, `ekSentCt1ReceivedAt`, `ct1SentResultAt`,
`ekSentCt1ReceivedResultAt`), `SepWP` contracts (`ct1SentFromPbSpec`, `ekSentCt1ReceivedFromPbSpec`),
and shared `Vec<u8>` / stack helpers.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Stack budget of `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (`0x5dc4c`):
    176-byte own frame (`sub sp, sp, #176`) plus `authFromPbStack` (`4160`B). -/
abbrev ct1SentFromPbStack : Nat := authFromPbStack + 176

/-- Stack budget of `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (`0x5e864`):
    144-byte own frame (`sub sp, sp, #144`) plus `authFromPbStack` (`4160`B). -/
abbrev ekSentCt1ReceivedFromPbStack : Nat := authFromPbStack + 144

/-! ## Binary Layout Predicates -/

/-- `spqr::v1::unchunked::send_ct::Ct1Sent` at `a` (`128` bytes = `0x80`, align `8`):
    - `+0..+48`: `auth: Authenticator` (`root_key` at `+0`, `mac_key` at `+24`)
    - `+48..+72`: `hdr: Vec<u8>`
    - `+72..+96`: `es: Vec<u8>`
    - `+96..+120`: `ct1: Vec<u8>`
    - `+120..+128`: `epoch: u64` -/
def ct1SentAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.hdr ∗
    vecU8 A (a + 72#64) st.es ∗
    vecU8 A (a + 96#64) st.ct1 ∗
    ((a + 120#64) ↦₆₄ st.epoch)

/-- `spqr::v1::unchunked::send_ek::EkSentCt1Received` at `a` (`104` bytes = `0x68`, align `8`):
    - `+0..+48`: `auth: Authenticator` (`root_key` at `+0`, `mac_key` at `+24`)
    - `+48..+72`: `dk: Vec<u8>`
    - `+72..+96`: `ct1: Vec<u8>`
    - `+96..+104`: `epoch: u64` -/
def ekSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) : SepProp :=
  authenticatorAt A a st.auth ∗
    vecU8 A (a + 48#64) st.dk ∗
    vecU8 A (a + 72#64) st.ct1 ∗
    ((a + 96#64) ↦₆₄ st.epoch)

/-- `Result<spqr::v1::unchunked::send_ct::Ct1Sent, spqr::Error>` at `a` (`128` bytes = `0x80`):
    - `.ok st`: `ct1SentAt A a st` (`[a + 0]` is `st.auth.rootKey.cap < 2^63`, so `≠ noneCap`)
    - `.error _`: `(a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 0#8) ∗ memRegion (a + 9#64) 119`
      (`niche = -1` at `+0`, `Error::StateDecode = 0#8` at `+8`). -/
def ct1SentResultAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    StatesResult (Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) → SepProp
  | .ok st => ct1SentAt A a st
  | .error _ => (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 0#8) ∗ memRegion (a + 9#64) 119

/-- `Result<spqr::v1::unchunked::send_ek::EkSentCt1Received, spqr::Error>` at `a` (`104` bytes = `0x68`):
    - `.ok st`: `ekSentCt1ReceivedAt A a st` (`[a + 0]` is `st.auth.rootKey.cap < 2^63`, so `≠ noneCap`)
    - `.error _`: `(a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 0#8) ∗ memRegion (a + 9#64) 95`
      (`niche = -1` at `+0`, `Error::StateDecode = 0#8` at `+8`). -/
def ekSentCt1ReceivedResultAt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) :
    StatesResult (Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) → SepProp
  | .ok st => ekSentCt1ReceivedAt A a st
  | .error _ => (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₈ 0#8) ∗ memRegion (a + 9#64) 95

/-! ## Specifications -/

structure Ct1SentFromPbGhost where
  /-- Sret pointer (`x0`, 128-byte `Result<Ct1Sent, Error>` output). -/
  out : BitVec 64
  /-- Pointer to consumed `spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent` (`x1`, 128 bytes). -/
  pbA : BitVec 64
  /-- Pure `V1State.Unchunked.Ct1Sent` input value. -/
  pb : V1State.Unchunked.Ct1Sent

/-- Specification of `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (`x0 = out`, `x1 = pbA`). -/
def ct1SentFromPbSpec (A : RustAlloc) (F : ShaCompress) : Spec Ct1SentFromPbGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out 128 ∗
      protoUnchunkedCt1SentAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp ct1SentFromPbStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentResultAt A x.out (Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 128 ∗
      A.pool ∗ stackAt s0.sp ct1SentFromPbStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def Ct1SentFromPbOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ct1SentFromPbName)
    ((ct1SentFromPbSpec A F).inImage img)

def Ct1SentFromPbPlacedOk [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (blkPl_339).base
    (ct1SentFromPbSpec A F)

structure EkSentCt1ReceivedFromPbGhost where
  /-- Sret pointer (`x0`, 104-byte `Result<EkSentCt1Received, Error>` output). -/
  out : BitVec 64
  /-- Pointer to consumed `spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received` (`x1`, 104 bytes). -/
  pbA : BitVec 64
  /-- Pure `V1State.Unchunked.EkSentCt1Received` input value. -/
  pb : V1State.Unchunked.EkSentCt1Received

/-- Specification of `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (`x0 = out`, `x1 = pbA`). -/
def ekSentCt1ReceivedFromPbSpec (A : RustAlloc) (F : ShaCompress) :
    Spec EkSentCt1ReceivedFromPbGhost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA⌝ ∗
      memRegion x.out 104 ∗
      protoUnchunkedEkSentCt1ReceivedAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp ekSentCt1ReceivedFromPbStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedResultAt A x.out
        (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 104 ∗
      A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def EkSentCt1ReceivedFromPbOkX (img : Obj.Image) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ekSentCt1ReceivedFromPbName)
    ((ekSentCt1ReceivedFromPbSpec A F).inImage img)

def EkSentCt1ReceivedFromPbPlacedOk [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_348).rebase (blkPl_348).base H) (blkPl_348).base
    (ekSentCt1ReceivedFromPbSpec A F)

/-! ## Shared Memory, Stack, and `Vec<u8>` Helpers -/

/-- Heap payload + bounds of a `Vec<u8>` separated from its 3 header words. -/
def vecU8Payload (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
    (if cap = 0#64 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Payload
  ac_rfl

theorem vecU8_of_header_payload (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Payload A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_payload]
  exact Entails.refl _

theorem vecU8Payload_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Payload A cap ptr bs ⊢ vecCapPtrDealloc A cap ptr := by
  unfold vecU8Payload vecCapPtrDealloc
  apply Entails.pure_left; intro ⟨hle, hlt, _⟩
  by_cases hcap : (cap == 0#64) = true
  · have h0 : cap = 0#64 := of_decide_eq_true hcap
    subst h0
    simp only [beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  · have hne : cap ≠ 0#64 := by
      intro h0; subst h0; exact hcap rfl
    simp only [hcap, hne, Bool.false_eq_true, ↓reduceIte]
    have hm1 := pointsToBytes_entails_memRegion ptr bs
    have hm2 : memRegion ptr bs.length ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        memRegion ptr cap.toNat := by
      rw [← ProofLib.memRegion_split' (b := ptr) (n := bs.length) (k := cap.toNat - bs.length)
        (N := cap.toNat) (b' := ptr + BitVec.ofNat 64 bs.length) (by omega) rfl (by omega)]
    rw [← hm2]
    exact sepConj_mono_right (sepConj_mono_left hm1)

theorem header3_entails_memRegion_24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (Drop.pointsTo64_entails_memRegion (a + 16#64) w2))) ?_
  exact header_cells_entails_memRegion_24 a w0 w1

theorem ofNat_beq_lit_iff {n k : Nat} (hn : n < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 n == BitVec.ofNat 64 k) = (n == k) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hk64 : k < 2 ^ 64 := by omega
  by_cases h : n = k
  · subst h; simp
  · have hne : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := by
      intro heq
      have h1 := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hk64] at h1
      exact h h1
    simp [hne, h]

theorem memRegion_128_err_split (a : BitVec 64) :
    memRegion a 128 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ b8 : BitVec 8,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b8) ∗ memRegion (a + 9#64) 119 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 120) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 119) (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_one (a + 8#64), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b8
  refine Entails.sepExists_right w0 (Entails.sepExists_right b8 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_104_err_split (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ b8 : BitVec 8,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ b8) ∗ memRegion (a + 9#64) 95 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 96) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 95) (b' := a + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_one (a + 8#64), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b8
  refine Entails.sepExists_right w0 (Entails.sepExists_right b8 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_ct1SentFromPb_split (sp : BitVec 64) :
    stackAt sp ct1SentFromPbStack =
      stackAt (sp - 176#64) authFromPbStack ∗
      memRegion (sp - 176#64) 128 ∗
      cells (sp - 48#64) 6 := by
  rw [show ct1SentFromPbStack = (authFromPbStack + 128) + 8 * 6 from rfl,
      ProofLib.stackAt_split_cells sp (authFromPbStack + 128) 6 (by decide)]
  have h1 : stackAt (sp - 48#64) (authFromPbStack + 128) =
      stackAt (sp - 176#64) authFromPbStack ∗ memRegion (sp - 176#64) 128 := by
    unfold stackAt authFromPbStack allocHookStack
    rw [ProofLib.memRegion_split' (b := (sp - 48#64) - BitVec.ofNat 64 (4096 + 64 + 128))
          (n := 4160) (k := 128) (b' := sp - 176#64) rfl (by bv_omega) (by decide)]
    have hb : (sp - 48#64) - BitVec.ofNat 64 (4096 + 64 + 128) =
        (sp - 176#64) - BitVec.ofNat 64 (4096 + 64) := by bv_omega
    rw [hb]
  rw [h1, sepConj_assoc]

theorem stackAt_ekSentCt1ReceivedFromPb_split (sp : BitVec 64) :
    stackAt sp ekSentCt1ReceivedFromPbStack =
      stackAt (sp - 144#64) authFromPbStack ∗
      memRegion (sp - 144#64) 96 ∗
      cells (sp - 48#64) 6 := by
  rw [show ekSentCt1ReceivedFromPbStack = (authFromPbStack + 96) + 8 * 6 from rfl,
      ProofLib.stackAt_split_cells sp (authFromPbStack + 96) 6 (by decide)]
  have h1 : stackAt (sp - 48#64) (authFromPbStack + 96) =
      stackAt (sp - 144#64) authFromPbStack ∗ memRegion (sp - 144#64) 96 := by
    unfold stackAt authFromPbStack allocHookStack
    rw [ProofLib.memRegion_split' (b := (sp - 48#64) - BitVec.ofNat 64 (4096 + 64 + 96))
          (n := 4160) (k := 96) (b' := sp - 144#64) rfl (by bv_omega) (by decide)]
    have hb : (sp - 48#64) - BitVec.ofNat 64 (4096 + 64 + 96) =
        (sp - 144#64) - BitVec.ofNat 64 (4096 + 64) := by bv_omega
    rw [hb]
  rw [h1, sepConj_assoc]

theorem stackAt_ct1SentFromPb_restore (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 176#64) authFromPbStack ∗
      memRegion (sp - 176#64) 128 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp ct1SentFromPbStack := by
  rw [stackAt_ct1SentFromPb_split sp]
  exact sepConj_mono_right (sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19))

theorem stackAt_ct1SentFromPb_split_dropStack32 (sp : BitVec 64) :
    stackAt sp ct1SentFromPbStack =
      memRegion (sp - 4336#64) 208 ∗ stackAt sp dropStack32 :=
  ProofLib.stackAt_split_bottom sp dropStack32 208 (by decide)

theorem stackAt_ct1SentFromPb_split_allocHook (sp : BitVec 64) :
    stackAt sp ct1SentFromPbStack =
      memRegion (sp - 4336#64) 240 ∗ stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack 240 (by decide)

theorem stackAt_authFromPb_split_allocHook_sub176 (sp : BitVec 64) :
    stackAt (sp - 176#64) authFromPbStack =
      memRegion (sp - 4336#64) 64 ∗ stackAt (sp - 176#64) allocHookStack := by
  have h := ProofLib.stackAt_split_bottom (sp - 176#64) allocHookStack 64 (by decide)
  have hb : (sp - 176#64) - BitVec.ofNat 64 (allocHookStack + 64) = sp - 4336#64 := by
    change (sp - 176#64) - 4160#64 = sp - 4336#64
    bv_omega
  rw [hb] at h
  exact h

theorem stackAt_ct1SentFromPb_restore_from_allocHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion (sp - 4336#64) 64 ∗
      stackAt (sp - 176#64) allocHookStack ∗
      memRegion (sp - 176#64) 128 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp ct1SentFromPbStack := by
  rw [← sepConj_assoc, ← stackAt_authFromPb_split_allocHook_sub176 sp]
  exact stackAt_ct1SentFromPb_restore sp fp lr x22 x21 x20 x19

theorem stackAt_ct1SentFromPb_tail_allocHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion (sp - 4336#64) 64 ∗
      stackAt (sp - 176#64) allocHookStack ∗
      memRegion (sp - 176#64) 128 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 4336#64) 240 ∗ stackAt sp allocHookStack := by
  rw [← stackAt_ct1SentFromPb_split_allocHook sp]
  exact stackAt_ct1SentFromPb_restore_from_allocHook sp fp lr x22 x21 x20 x19

theorem stackAt_ct1SentFromPb_tail_dropStack32 (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 176#64) authFromPbStack ∗
      memRegion (sp - 176#64) 128 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 4336#64) 208 ∗ stackAt sp dropStack32 := by
  rw [← stackAt_ct1SentFromPb_split_dropStack32 sp]
  exact stackAt_ct1SentFromPb_restore sp fp lr x22 x21 x20 x19

theorem stackAt_ekSentCt1ReceivedFromPb_restore (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    stackAt (sp - 144#64) authFromPbStack ∗
      memRegion (sp - 144#64) 96 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp ekSentCt1ReceivedFromPbStack := by
  rw [stackAt_ekSentCt1ReceivedFromPb_split sp]
  exact sepConj_mono_right (sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19))

theorem stackAt_ekSentCt1ReceivedFromPb_split_allocHook (sp : BitVec 64) :
    stackAt sp ekSentCt1ReceivedFromPbStack =
      memRegion (sp - 4304#64) 208 ∗ stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack 208 (by decide)

theorem stackAt_authFromPb_split_allocHook_sub144 (sp : BitVec 64) :
    stackAt (sp - 144#64) authFromPbStack =
      memRegion (sp - 4304#64) 64 ∗ stackAt (sp - 144#64) allocHookStack := by
  have h := ProofLib.stackAt_split_bottom (sp - 144#64) allocHookStack 64 (by decide)
  have hb : (sp - 144#64) - BitVec.ofNat 64 (allocHookStack + 64) = sp - 4304#64 := by
    change (sp - 144#64) - 4160#64 = sp - 4304#64
    bv_omega
  rw [hb] at h
  exact h

theorem stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion (sp - 4304#64) 64 ∗
      stackAt (sp - 144#64) allocHookStack ∗
      memRegion (sp - 144#64) 96 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp ekSentCt1ReceivedFromPbStack := by
  rw [← sepConj_assoc, ← stackAt_authFromPb_split_allocHook_sub144 sp]
  exact stackAt_ekSentCt1ReceivedFromPb_restore sp fp lr x22 x21 x20 x19

theorem stackAt_ekSentCt1ReceivedFromPb_tail_allocHook
    (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    memRegion (sp - 4304#64) 64 ∗
      stackAt (sp - 144#64) allocHookStack ∗
      memRegion (sp - 144#64) 96 ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    memRegion (sp - 4304#64) 208 ∗ stackAt sp allocHookStack := by
  rw [← stackAt_ekSentCt1ReceivedFromPb_split_allocHook sp]
  exact stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook sp fp lr x22 x21 x20 x19

theorem fnAddr_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k = (P.rebase b X).fnAddr n2) :
    (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k = (P.rebase b X).fnAddr n1 := by
  rw [← hrel, BitVec.add_sub_cancel]

theorem vecU8_unpack (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜bs.length < 2 ^ 63 ∧ c.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         vecU8Payload A c p bs) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro c
  apply Entails.sepExists_elim; intro p
  refine Entails.sepExists_right c (Entails.sepExists_right p ?_)
  rw [vecU8At_eq_header_payload A a c p bs]
  unfold vecU8Payload
  have hpull :
      (a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
          if c = 0#64 then emp
          else A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length)) =
      ⌜bs.length ≤ c.toNat ∧ c.toNat < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
        ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         (if c = 0#64 then emp
          else A.live p c.toNat 1 ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (c.toNat - bs.length))) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
  refine Entails.pure_right ⟨Nat.lt_of_le_of_lt hle hlt, hlt⟩ ?_
  exact Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _)

theorem protoUnchunkedCt1SentAt_unpack (A : RustAlloc) (a : BitVec 64)
    (pb : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a pb ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
      ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64,
        ⌜pb.hdr.length < 2 ^ 63 ∧ pb.es.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧
          c1.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A (a + 72#64) pb.auth ∗
         ((a + 120#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.hdr ∗
         vecU8Payload A c2 p2 pb.es ∗
         vecU8Payload A c3 p3 pb.ct1) := by
  unfold protoUnchunkedCt1SentAt
  refine Entails.trans
    (sepConj_mono (vecU8_unpack A a pb.hdr)
      (sepConj_mono (vecU8_unpack A (a + 24#64) pb.es)
        (sepConj_mono (vecU8_unpack A (a + 48#64) pb.ct1) (Entails.refl _)))) ?_
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
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right c2 (Entails.sepExists_right p2
      (Entails.sepExists_right c3 (Entails.sepExists_right p3 ?_)))))
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2, hb1, hb2]
  have hpull :
      ((⌜pb.hdr.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         vecU8Payload A c1 p1 pb.hdr)) ∗
       (⌜pb.es.length < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗
        (((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         vecU8Payload A c2 p2 pb.es)) ∗
       (⌜pb.ct1.length < 2 ^ 63 ∧ c3.toNat < 2 ^ 63⌝ ∗
        (((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         vecU8Payload A c3 p3 pb.ct1)) ∗
       optProtoAuthenticatorAt A (a + 72#64) pb.auth ∗
       ((a + 120#64) ↦₆₄ pb.epoch)) =
      (⌜pb.hdr.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
       ⌜pb.es.length < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗
       ⌜pb.ct1.length < 2 ^ 63 ∧ c3.toNat < 2 ^ 63⌝ ∗
       ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        optProtoAuthenticatorAt A (a + 72#64) pb.auth ∗
        ((a + 120#64) ↦₆₄ pb.epoch) ∗
        vecU8Payload A c1 p1 pb.hdr ∗
        vecU8Payload A c2 p2 pb.es ∗
        vecU8Payload A c3 p3 pb.ct1)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro ⟨hl1, hc1⟩
  apply Entails.pure_left; intro ⟨hl2, _⟩
  apply Entails.pure_left; intro ⟨hl3, _⟩
  exact Entails.pure_right ⟨hl1, hl2, hl3, hc1⟩ (Entails.refl _)

theorem protoUnchunkedEkSentCt1ReceivedAt_unpack (A : RustAlloc) (a : BitVec 64)
    (pb : V1State.Unchunked.EkSentCt1Received) :
    protoUnchunkedEkSentCt1ReceivedAt A a pb ⊢
      ∃∗ c1 : BitVec 64, ∃∗ p1 : BitVec 64,
      ∃∗ c2 : BitVec 64, ∃∗ p2 : BitVec 64,
        ⌜pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A (a + 48#64) pb.auth ∗
         ((a + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1) := by
  unfold protoUnchunkedEkSentCt1ReceivedAt
  refine Entails.trans
    (sepConj_mono (vecU8_unpack A a pb.dk)
      (sepConj_mono (vecU8_unpack A (a + 24#64) pb.ct1) (Entails.refl _))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right c1 (Entails.sepExists_right p1
    (Entails.sepExists_right c2 (Entails.sepExists_right p2 ?_)))
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2]
  have hpull :
      ((⌜pb.dk.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
        ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         vecU8Payload A c1 p1 pb.dk)) ∗
       (⌜pb.ct1.length < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗
        (((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         vecU8Payload A c2 p2 pb.ct1)) ∗
       optProtoAuthenticatorAt A (a + 48#64) pb.auth ∗
       ((a + 96#64) ↦₆₄ pb.epoch)) =
      (⌜pb.dk.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
       ⌜pb.ct1.length < 2 ^ 63 ∧ c2.toNat < 2 ^ 63⌝ ∗
       ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        optProtoAuthenticatorAt A (a + 48#64) pb.auth ∗
        ((a + 96#64) ↦₆₄ pb.epoch) ∗
        vecU8Payload A c1 p1 pb.dk ∗
        vecU8Payload A c2 p2 pb.ct1)) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro ⟨hl1, hc1⟩
  apply Entails.pure_left; intro ⟨hl2, _⟩
  exact Entails.pure_right ⟨hl1, hl2, hc1⟩ (Entails.refl _)

@[arm64_norm]
theorem extractLsb'_0_64_append (v2 v1 : BitVec 64) :
    (v2 ++ v1).extractLsb' 0 64 = v1 := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getElem_append, hi]

@[arm64_norm]
theorem extractLsb'_64_64_append (v2 v1 : BitVec 64) :
    (v2 ++ v1).extractLsb' 64 64 = v2 := by
  ext i hi
  simp [BitVec.getElem_extractLsb', BitVec.getElem_append,
    show ¬(64 + i < 64) by omega]

/-- Tail of `authenticatorPBPinnedAt A ga p auth` after separating `(p ↦₆₄ ga.rootKey.cap)`. -/
def authPBPinnedTailAt (A : RustAlloc) (ga : AuthenticatorPBGhost) (p : BitVec 64)
    (auth : ProtoAuthenticator) : SepProp :=
  ((p + 8#64) ↦₆₄ ga.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    vecU8Payload A ga.rootKey.cap ga.rootKey.ptr auth.rootKey ∗
    vecU8At A (p + 24#64) ga.macKey.cap ga.macKey.ptr auth.macKey

theorem authenticatorPBPinnedAt_eq_cap_tail (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (p : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga p auth =
      (p ↦₆₄ ga.rootKey.cap) ∗ authPBPinnedTailAt A ga p auth := by
  unfold authenticatorPBPinnedAt authPBPinnedTailAt
  rw [vecU8At_eq_header_payload A p ga.rootKey.cap ga.rootKey.ptr auth.rootKey]
  ac_rfl

theorem optProtoAuthenticatorAt_some_unpack (A : RustAlloc) (p : BitVec 64)
    (auth : ProtoAuthenticator) :
    optProtoAuthenticatorAt A p (some auth) ⊢
      ∃∗ ga : AuthenticatorPBGhost,
        ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗
        ((p ↦₆₄ ga.rootKey.cap) ∗ authPBPinnedTailAt A ga p auth) := by
  rw [optProtoAuthenticatorAt_some]
  change authenticatorPBAt A p auth ⊢ _
  rw [authenticatorPBAt_eq_exists_pinned]
  apply Entails.sepExists_elim; intro ga
  refine Entails.sepExists_right ga ?_
  rw [authenticatorPBPinnedAt_eq_cap_tail]
  unfold authPBPinnedTailAt vecU8Payload
  have hpull :
      (p ↦₆₄ ga.rootKey.cap) ∗ ((p + 8#64) ↦₆₄ ga.rootKey.ptr) ∗
        ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        (⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧
            ga.rootKey.cap.toNat < 2 ^ 63 ∧ ga.rootKey.ptr ≠ 0#64⌝ ∗
          if ga.rootKey.cap = 0#64 then emp
          else A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
            memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
              (ga.rootKey.cap.toNat - auth.rootKey.length)) ∗
        vecU8At A (p + 24#64) ga.macKey.cap ga.macKey.ptr auth.macKey =
      ⌜auth.rootKey.length ≤ ga.rootKey.cap.toNat ∧
          ga.rootKey.cap.toNat < 2 ^ 63 ∧ ga.rootKey.ptr ≠ 0#64⌝ ∗
        ((p ↦₆₄ ga.rootKey.cap) ∗ ((p + 8#64) ↦₆₄ ga.rootKey.ptr) ∗
          ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          (if ga.rootKey.cap = 0#64 then emp
           else A.live ga.rootKey.ptr ga.rootKey.cap.toNat 1 ∗ (ga.rootKey.ptr ↦ₛ auth.rootKey) ∗
             memRegion (ga.rootKey.ptr + BitVec.ofNat 64 auth.rootKey.length)
               (ga.rootKey.cap.toNat - auth.rootKey.length)) ∗
          vecU8At A (p + 24#64) ga.macKey.cap ga.macKey.ptr auth.macKey) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro ⟨hle, hlt, hne⟩
  exact Entails.pure_right hlt (Entails.pure_right ⟨hle, hlt, hne⟩ (Entails.refl _))

theorem authenticatorPBPinnedAt_entails_dealloc (A : RustAlloc) (ga : AuthenticatorPBGhost)
    (p : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga p auth ⊢
      twoVecHeadersAt p ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  unfold authenticatorPBPinnedAt
  have h1 := vecU8At_entails_capPtr_dealloc A p ga.rootKey.cap ga.rootKey.ptr auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc A (p + 24#64) ga.macKey.cap ga.macKey.ptr auth.macKey
  have ha1 : (p + 24#64) + 8#64 = p + 32#64 := by bv_omega
  have ha2 : (p + 24#64) + 16#64 = p + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 h2) ?_
  unfold twoVecHeadersAt
  dsimp only
  exact Entails.of_eq (by ac_rfl)

def auth48HeadersAt (a : BitVec 64) (ga : TwoVecGhost) : SepProp :=
  ((a + 48#64) ↦₆₄ ga.v1.cap) ∗ ((a + 56#64) ↦₆₄ ga.v1.ptr) ∗ memRegion (a + 64#64) 8 ∗
  ((a + 72#64) ↦₆₄ ga.v2.cap) ∗ ((a + 80#64) ↦₆₄ ga.v2.ptr) ∗ memRegion (a + 88#64) 8

theorem twoVecHeadersAt_48_eq (a : BitVec 64) (ga : TwoVecGhost) :
    twoVecHeadersAt (a + 48#64) ga = auth48HeadersAt a ga := by
  unfold twoVecHeadersAt auth48HeadersAt
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  have h3 : (a + 48#64) + 24#64 = a + 72#64 := by bv_omega
  have h4 : (a + 48#64) + 32#64 = a + 80#64 := by bv_omega
  have h5 : (a + 48#64) + 40#64 = a + 88#64 := by bv_omega
  rw [h1, h2, h3, h4, h5]

theorem auth48HeadersAt_entails_memRegion_48 (a : BitVec 64) (ga : TwoVecGhost) :
    auth48HeadersAt a ga ⊢ memRegion (a + 48#64) 48 := by
  rw [← twoVecHeadersAt_48_eq]
  exact twoVecHeadersAt_entails_memRegion_48 (a + 48#64) ga

theorem optProtoAuthenticatorAt_48_none (A : RustAlloc) (a : BitVec 64) :
    optProtoAuthenticatorAt A (a + 48#64) none =
      ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 40 := by
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  rw [optProtoAuthenticatorAt_none, h1]

theorem optProtoAuthenticatorAt_48_none_entails_memRegion_48 (A : RustAlloc) (a : BitVec 64) :
    ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 40 ⊢ memRegion (a + 48#64) 48 := by
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  rw [← h1]
  exact optProtoAuthenticatorAt_none_entails_memRegion_48 A (a + 48#64)

theorem authenticatorAt_unpack (A : RustAlloc) (p : BitVec 64) (auth : Authenticator) :
    authenticatorAt A p auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64,
      ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        ((p ↦₆₄ ca1) ∗ ((p + 8#64) ↦₆₄ pa1) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((p + 24#64) ↦₆₄ ca2) ∗ ((p + 32#64) ↦₆₄ pa2) ∗ ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗
        vecU8Payload A ca2 pa2 auth.macKey := by
  unfold authenticatorAt
  refine Entails.trans
    (sepConj_mono (vecU8_unpack A p auth.rootKey) (vecU8_unpack A (p + 24#64) auth.macKey)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ca1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pa1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro ca2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pa2
  refine Entails.sepExists_right ca1 (Entails.sepExists_right pa1
    (Entails.sepExists_right ca2 (Entails.sepExists_right pa2 ?_)))
  have ha1 : (p + 24#64) + 8#64 = p + 32#64 := by bv_omega
  have ha2 : (p + 24#64) + 16#64 = p + 40#64 := by bv_omega
  rw [ha1, ha2]
  have hpull :
      (⌜auth.rootKey.length < 2 ^ 63 ∧ ca1.toNat < 2 ^ 63⌝ ∗
        ((p ↦₆₄ ca1) ∗ ((p + 8#64) ↦₆₄ pa1) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         vecU8Payload A ca1 pa1 auth.rootKey)) ∗
      (⌜auth.macKey.length < 2 ^ 63 ∧ ca2.toNat < 2 ^ 63⌝ ∗
        (((p + 24#64) ↦₆₄ ca2) ∗ ((p + 32#64) ↦₆₄ pa2) ∗ ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
         vecU8Payload A ca2 pa2 auth.macKey)) =
      ⌜auth.rootKey.length < 2 ^ 63 ∧ ca1.toNat < 2 ^ 63⌝ ∗
      ⌜auth.macKey.length < 2 ^ 63 ∧ ca2.toNat < 2 ^ 63⌝ ∗
      (((p ↦₆₄ ca1) ∗ ((p + 8#64) ↦₆₄ pa1) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
        ((p + 24#64) ↦₆₄ ca2) ∗ ((p + 32#64) ↦₆₄ pa2) ∗ ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
       vecU8Payload A ca1 pa1 auth.rootKey ∗
       vecU8Payload A ca2 pa2 auth.macKey) := by ac_rfl
  rw [hpull]
  apply Entails.pure_left; intro _
  apply Entails.pure_left; intro _
  exact Entails.refl _

theorem ct1SentAt_pack (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (ca1 pa1 ca2 pa2 c1 p1 c2 p2 c3 p3 epoch : BitVec 64)
    (auth : Authenticator) (hdr es ct1 : List (BitVec 8)) :
    ((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
     ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 es.length) ∗
     ((out + 96#64) ↦₆₄ c3) ∗ ((out + 104#64) ↦₆₄ p3) ∗ ((out + 112#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
     ((out + 120#64) ↦₆₄ epoch)) ∗
    vecU8Payload A ca1 pa1 auth.rootKey ∗
    vecU8Payload A ca2 pa2 auth.macKey ∗
    vecU8Payload A c1 p1 hdr ∗
    vecU8Payload A c2 p2 es ∗
    vecU8Payload A c3 p3 ct1 ⊢
    ct1SentAt A (F := F) out
      { epoch := epoch, auth := auth, hdr := hdr, es := es, ct1 := ct1 } := by
  unfold ct1SentAt authenticatorAt
  dsimp only
  have h1 := vecU8_of_header_payload A out ca1 pa1 auth.rootKey
  have h2 := vecU8_of_header_payload A (out + 24#64) ca2 pa2 auth.macKey
  have h3 := vecU8_of_header_payload A (out + 48#64) c1 p1 hdr
  have h4 := vecU8_of_header_payload A (out + 72#64) c2 p2 es
  have h5 := vecU8_of_header_payload A (out + 96#64) c3 p3 ct1
  have ha1 : (out + 24#64) + 8#64 = out + 32#64 := by bv_omega
  have ha2 : (out + 24#64) + 16#64 = out + 40#64 := by bv_omega
  have hb1 : (out + 48#64) + 8#64 = out + 56#64 := by bv_omega
  have hb2 : (out + 48#64) + 16#64 = out + 64#64 := by bv_omega
  have hc1 : (out + 72#64) + 8#64 = out + 80#64 := by bv_omega
  have hc2 : (out + 72#64) + 16#64 = out + 88#64 := by bv_omega
  have hd1 : (out + 96#64) + 8#64 = out + 104#64 := by bv_omega
  have hd2 : (out + 96#64) + 16#64 = out + 112#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  rw [hd1, hd2] at h5
  refine Entails.trans (Entails.of_eq (show _ =
    (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ca1 pa1 auth.rootKey) ∗
     (((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ca2 pa2 auth.macKey)) ∗
    (((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
     vecU8Payload A c1 p1 hdr) ∗
    (((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 es.length) ∗
     vecU8Payload A c2 p2 es) ∗
    (((out + 96#64) ↦₆₄ c3) ∗ ((out + 104#64) ↦₆₄ p3) ∗ ((out + 112#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
     vecU8Payload A c3 p3 ct1) ∗
    ((out + 120#64) ↦₆₄ epoch) by ac_rfl)) ?_
  exact sepConj_mono (sepConj_mono h1 h2)
    (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5)))

theorem ekSentCt1ReceivedAt_pack (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (ca1 pa1 ca2 pa2 c1 p1 c2 p2 epoch : BitVec 64)
    (auth : Authenticator) (dk ct1 : List (BitVec 8)) :
    ((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 dk.length) ∗
     ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
     ((out + 96#64) ↦₆₄ epoch)) ∗
    vecU8Payload A ca1 pa1 auth.rootKey ∗
    vecU8Payload A ca2 pa2 auth.macKey ∗
    vecU8Payload A c1 p1 dk ∗
    vecU8Payload A c2 p2 ct1 ⊢
    ekSentCt1ReceivedAt A (F := F) out
      { epoch := epoch, auth := auth, dk := dk, ct1 := ct1 } := by
  unfold ekSentCt1ReceivedAt authenticatorAt
  dsimp only
  have h1 := vecU8_of_header_payload A out ca1 pa1 auth.rootKey
  have h2 := vecU8_of_header_payload A (out + 24#64) ca2 pa2 auth.macKey
  have h3 := vecU8_of_header_payload A (out + 48#64) c1 p1 dk
  have h4 := vecU8_of_header_payload A (out + 72#64) c2 p2 ct1
  have ha1 : (out + 24#64) + 8#64 = out + 32#64 := by bv_omega
  have ha2 : (out + 24#64) + 16#64 = out + 40#64 := by bv_omega
  have hb1 : (out + 48#64) + 8#64 = out + 56#64 := by bv_omega
  have hb2 : (out + 48#64) + 16#64 = out + 64#64 := by bv_omega
  have hc1 : (out + 72#64) + 8#64 = out + 80#64 := by bv_omega
  have hc2 : (out + 72#64) + 16#64 = out + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [hc1, hc2] at h4
  refine Entails.trans (Entails.of_eq (show _ =
    (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      vecU8Payload A ca1 pa1 auth.rootKey) ∗
     (((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
      vecU8Payload A ca2 pa2 auth.macKey)) ∗
    (((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 dk.length) ∗
     vecU8Payload A c1 p1 dk) ∗
    (((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
     vecU8Payload A c2 p2 ct1) ∗
    ((out + 96#64) ↦₆₄ epoch) by ac_rfl)) ?_
  exact sepConj_mono (sepConj_mono h1 h2)
    (sepConj_mono h3 (sepConj_mono_left h4))

theorem memRegion_ct1Sent_scratch_split (sp : BitVec 64) :
    memRegion (sp - 176#64) 128 =
      memRegion (sp - 176#64) 8 ∗
      memRegion (sp - 168#64) 48 ∗
      cells (sp - 120#64) 9 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 120)
        (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 48) (k := 72)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 120#64) 9 (by decide)]

theorem memRegion_ct1Sent_scratch_restore (sp : BitVec 64)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 s6 s7 s8 : BitVec 64) :
    memRegion (sp - 176#64) 8 ∗
      (((sp - 168#64) ↦₆₄ a0) ∗ ((sp - 160#64) ↦₆₄ a1) ∗ ((sp - 152#64) ↦₆₄ a2) ∗
       ((sp - 144#64) ↦₆₄ a3) ∗ ((sp - 136#64) ↦₆₄ a4) ∗ ((sp - 128#64) ↦₆₄ a5)) ∗
      (((sp - 120#64) ↦₆₄ s0) ∗ ((sp - 112#64) ↦₆₄ s1) ∗ ((sp - 104#64) ↦₆₄ s2) ∗
       ((sp - 96#64) ↦₆₄ s3) ∗ ((sp - 88#64) ↦₆₄ s4) ∗ ((sp - 80#64) ↦₆₄ s5) ∗
       ((sp - 72#64) ↦₆₄ s6) ∗ ((sp - 64#64) ↦₆₄ s7) ∗ ((sp - 56#64) ↦₆₄ s8)) ⊢
      memRegion (sp - 176#64) 128 := by
  rw [memRegion_ct1Sent_scratch_split sp, ProofLib.memRegion_cells (sp - 168#64) 6 (by decide)]
  have h1 : (((sp - 168#64) ↦₆₄ a0) ∗ ((sp - 160#64) ↦₆₄ a1) ∗ ((sp - 152#64) ↦₆₄ a2) ∗
       ((sp - 144#64) ↦₆₄ a3) ∗ ((sp - 136#64) ↦₆₄ a4) ∗ ((sp - 128#64) ↦₆₄ a5)) ⊢
      cells (sp - 168#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  have h2 : (((sp - 120#64) ↦₆₄ s0) ∗ ((sp - 112#64) ↦₆₄ s1) ∗ ((sp - 104#64) ↦₆₄ s2) ∗
       ((sp - 96#64) ↦₆₄ s3) ∗ ((sp - 88#64) ↦₆₄ s4) ∗ ((sp - 80#64) ↦₆₄ s5) ∗
       ((sp - 72#64) ↦₆₄ s6) ∗ ((sp - 64#64) ↦₆₄ s7) ∗ ((sp - 56#64) ↦₆₄ s8)) ⊢
      cells (sp - 120#64) 9 := by
    cells_unfold
    exact Entails.sepExists_right s0 (Entails.sepExists_right s1
      (Entails.sepExists_right s2 (Entails.sepExists_right s3
        (Entails.sepExists_right s4 (Entails.sepExists_right s5
          (Entails.sepExists_right s6 (Entails.sepExists_right s7
            (Entails.sepExists_right s8 (Entails.refl _)))))))))
  exact sepConj_mono_right (sepConj_mono h1 h2)

theorem memRegion_ekSentCt1Received_scratch_split (sp : BitVec 64) :
    memRegion (sp - 144#64) 96 =
      memRegion (sp - 144#64) 48 ∗
      cells (sp - 96#64) 6 := by
  rw [ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 48)
        (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 6 (by decide)]

theorem memRegion_ekSentCt1Received_scratch_restore (sp : BitVec 64)
    (a0 a1 a2 a3 a4 a5 s0 s1 s2 s3 s4 s5 : BitVec 64) :
    (((sp - 144#64) ↦₆₄ a0) ∗ ((sp - 136#64) ↦₆₄ a1) ∗ ((sp - 128#64) ↦₆₄ a2) ∗
     ((sp - 120#64) ↦₆₄ a3) ∗ ((sp - 112#64) ↦₆₄ a4) ∗ ((sp - 104#64) ↦₆₄ a5)) ∗
    (((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗
     ((sp - 72#64) ↦₆₄ s3) ∗ ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5)) ⊢
      memRegion (sp - 144#64) 96 := by
  rw [memRegion_ekSentCt1Received_scratch_split sp,
      ProofLib.memRegion_cells (sp - 144#64) 6 (by decide)]
  have h1 : (((sp - 144#64) ↦₆₄ a0) ∗ ((sp - 136#64) ↦₆₄ a1) ∗ ((sp - 128#64) ↦₆₄ a2) ∗
       ((sp - 120#64) ↦₆₄ a3) ∗ ((sp - 112#64) ↦₆₄ a4) ∗ ((sp - 104#64) ↦₆₄ a5)) ⊢
      cells (sp - 144#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  have h2 : (((sp - 96#64) ↦₆₄ s0) ∗ ((sp - 88#64) ↦₆₄ s1) ∗ ((sp - 80#64) ↦₆₄ s2) ∗
       ((sp - 72#64) ↦₆₄ s3) ∗ ((sp - 64#64) ↦₆₄ s4) ∗ ((sp - 56#64) ↦₆₄ s5)) ⊢
      cells (sp - 96#64) 6 := by
    cells_unfold
    exact Entails.sepExists_right s0 (Entails.sepExists_right s1
      (Entails.sepExists_right s2 (Entails.sepExists_right s3
        (Entails.sepExists_right s4 (Entails.sepExists_right s5 (Entails.refl _))))))
  exact sepConj_mono h1 h2

theorem memRegion_128_eq_cells16 (out : BitVec 64) :
    memRegion out 128 = cells out 16 :=
  ProofLib.memRegion_cells out 16 (by decide)

theorem memRegion_104_eq_cells13 (out : BitVec 64) :
    memRegion out 104 = cells out 13 :=
  ProofLib.memRegion_cells out 13 (by decide)

theorem unpacked_ct1Sent_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (c1 p1 w1 c2 p2 w2 c3 p3 w3 epoch : BitVec 64)
    (auth : Option ProtoAuthenticator) (hdr es ct1 : List (BitVec 8)) :
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1) ∗
      ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2) ∗
      ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ w3) ∗
      optProtoAuthenticatorAt A (a + 72#64) auth ∗
      ((a + 120#64) ↦₆₄ epoch) ∗
      vecU8Payload A c1 p1 hdr ∗
      vecU8Payload A c2 p2 es ∗
      vecU8Payload A c3 p3 ct1 ⊢
    protoUnchunked3VecHeadersAt a ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩ ∗
      optProtoAuthenticatorAt A (a + 72#64) auth ∗
      memRegion (a + 120#64) 8 ∗
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 ∗
      vecCapPtrDealloc A c3 p3 := by
  unfold protoUnchunked3VecHeadersAt
  dsimp only
  have hm1 := Drop.pointsTo64_entails_memRegion (a + 16#64) w1
  have hm2 := Drop.pointsTo64_entails_memRegion (a + 40#64) w2
  have hm3 := Drop.pointsTo64_entails_memRegion (a + 64#64) w3
  have hm4 := Drop.pointsTo64_entails_memRegion (a + 120#64) epoch
  have hd1 := vecU8Payload_entails_dealloc A c1 p1 hdr
  have hd2 := vecU8Payload_entails_dealloc A c2 p2 es
  have hd3 := vecU8Payload_entails_dealloc A c3 p3 ct1
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm1
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm2
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm3
          (sepConj_mono_right (sepConj_mono hm4
            (sepConj_mono hd1 (sepConj_mono hd2 hd3))))))))))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem unpacked_ekSentCt1Received_entails_dealloc (A : RustAlloc) (a : BitVec 64)
    (c1 p1 w1 c2 p2 w2 epoch : BitVec 64)
    (auth : Option ProtoAuthenticator) (dk ct1 : List (BitVec 8)) :
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1) ∗
      ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2) ∗
      optProtoAuthenticatorAt A (a + 48#64) auth ∗
      ((a + 96#64) ↦₆₄ epoch) ∗
      vecU8Payload A c1 p1 dk ∗
      vecU8Payload A c2 p2 ct1 ⊢
    protoUnchunked2VecHeadersAt a ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ∗
      optProtoAuthenticatorAt A (a + 48#64) auth ∗
      memRegion (a + 96#64) 8 ∗
      vecCapPtrDealloc A c1 p1 ∗
      vecCapPtrDealloc A c2 p2 := by
  unfold protoUnchunked2VecHeadersAt twoVecHeadersAt
  dsimp only
  have hm1 := Drop.pointsTo64_entails_memRegion (a + 16#64) w1
  have hm2 := Drop.pointsTo64_entails_memRegion (a + 40#64) w2
  have hm3 := Drop.pointsTo64_entails_memRegion (a + 96#64) epoch
  have hd1 := vecU8Payload_entails_dealloc A c1 p1 dk
  have hd2 := vecU8Payload_entails_dealloc A c2 p2 ct1
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm1
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hm2
        (sepConj_mono_right (sepConj_mono hm3
          (sepConj_mono hd1 hd2))))))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem unpacked_ct1Sent_auth_none_pack (A : RustAlloc) (a : BitVec 64)
    (c1 p1 c2 p2 c3 p3 epoch : BitVec 64)
    (hdr es ct1 : List (BitVec 8)) :
    (a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
      ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 es.length) ∗
      ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
      (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
      ((a + 120#64) ↦₆₄ epoch) ∗
      vecU8Payload A c1 p1 hdr ∗
      vecU8Payload A c2 p2 es ∗
      vecU8Payload A c3 p3 ct1 ⊢
    protoUnchunkedCt1SentEkReceivedAt A a
      { epoch := epoch, auth := none, es := hdr, ek := es, ct1 := ct1 } := by
  unfold protoUnchunkedCt1SentEkReceivedAt
  dsimp only
  rw [optProtoAuthenticatorAt_72_none]
  have h1 := vecU8_of_header_payload A a c1 p1 hdr
  have h2 := vecU8_of_header_payload A (a + 24#64) c2 p2 es
  have h3 := vecU8_of_header_payload A (a + 48#64) c3 p3 ct1
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  refine Entails.trans (Entails.of_eq (show _ =
    ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
     vecU8Payload A c1 p1 hdr) ∗
    (((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 es.length) ∗
     vecU8Payload A c2 p2 es) ∗
    (((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ct1.length) ∗
     vecU8Payload A c3 p3 ct1) ∗
    (((a + 72#64) ↦₆₄ noneCap) ∗ memRegion (a + 80#64) 40) ∗
    ((a + 120#64) ↦₆₄ epoch) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))

theorem unpacked_ct1Sent_headers_entails_memRegion_72_8 (a : BitVec 64)
    (c1 p1 w1 c2 p2 w2 c3 p3 w3 epoch : BitVec 64) :
    ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1) ∗
     ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2) ∗
     ((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ w3) ∗
     ((a + 120#64) ↦₆₄ epoch)) ⊢
    memRegion a 72 ∗ memRegion (a + 120#64) 8 := by
  have h1 := header3_entails_memRegion_24 a c1 p1 w1
  have h2 := header3_entails_memRegion_24 (a + 24#64) c2 p2 w2
  have h3 := header3_entails_memRegion_24 (a + 48#64) c3 p3 w3
  have h4 := Drop.pointsTo64_entails_memRegion (a + 120#64) epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hb1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have hb2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hb1, hb2] at h3
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 48)
        (b' := a + 24#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 24) (k := 24)
        (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1)) ∗
     (((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2)) ∗
     (((a + 48#64) ↦₆₄ c3) ∗ ((a + 56#64) ↦₆₄ p3) ∗ ((a + 64#64) ↦₆₄ w3))) ∗
    ((a + 120#64) ↦₆₄ epoch) by ac_rfl)) ?_
  exact sepConj_mono (sepConj_mono h1 (sepConj_mono h2 h3)) h4

theorem memRegion_72_auth72_8_entails_128 (a : BitVec 64) (ga : TwoVecGhost) :
    memRegion a 72 ∗ auth72HeadersAt a ga ∗ memRegion (a + 120#64) 8 ⊢
      memRegion a 128 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 72) (k := 56)
        (b' := a + 72#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 72#64) (n := 48) (k := 8)
        (b' := a + 120#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (auth72HeadersAt_entails_memRegion_48 a ga))

theorem unpacked_ekSentCt1Received_headers_entails_memRegion_48_8 (a : BitVec 64)
    (c1 p1 w1 c2 p2 w2 epoch : BitVec 64) :
    ((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1) ∗
     ((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2) ∗
     ((a + 96#64) ↦₆₄ epoch)) ⊢
    memRegion a 48 ∗ memRegion (a + 96#64) 8 := by
  have h1 := header3_entails_memRegion_24 a c1 p1 w1
  have h2 := header3_entails_memRegion_24 (a + 24#64) c2 p2 w2
  have h3 := Drop.pointsTo64_entails_memRegion (a + 96#64) epoch
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [ProofLib.memRegion_split' (b := a) (n := 24) (k := 24)
        (b' := a + 24#64) rfl rfl (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    (((a ↦₆₄ c1) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ w1)) ∗
     (((a + 24#64) ↦₆₄ c2) ∗ ((a + 32#64) ↦₆₄ p2) ∗ ((a + 40#64) ↦₆₄ w2))) ∗
    ((a + 96#64) ↦₆₄ epoch) by ac_rfl)) ?_
  exact sepConj_mono (sepConj_mono h1 h2) h3

theorem memRegion_48_auth48_8_entails_104 (a : BitVec 64) (ga : TwoVecGhost) :
    memRegion a 48 ∗ auth48HeadersAt a ga ∗ memRegion (a + 96#64) 8 ⊢
      memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56)
        (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8)
        (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (auth48HeadersAt_entails_memRegion_48 a ga))

end CryptoVerification.SpqrV1.Unchunked
