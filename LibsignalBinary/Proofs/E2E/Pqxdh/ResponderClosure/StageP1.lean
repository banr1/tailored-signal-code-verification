/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prog
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# Stage P1 Layouts and Callee Contracts for `message_decrypt_prekey::<PqxdhRng>::{closure#0}`

Defines isolated Stage P1 store-callee contracts (`load_session` and `is_trusted_identity`),
coroutine and stack-frame layout predicates (`decryptPrekeySavedRegsAt`, `decryptPrekeyCoroInitAt`,
`sessionRecordEmptyAt`), and scratch-slot packing helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Isolated Callee Contracts for Stage P1 (`+0x0000..+0x0868`) -/

/-- Trivial no-op `drop_in_place` contract for boxed store futures (`0x01fe4`). -/
def futNoopDropSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝

/-- Isolated external callee contracts for Stage P1 (`load_session` and `is_trusted_identity`
trait shims, future polls, and future drops). Peer proofs (`InMem` / `StoreKit`) instantiate
this structure directly. -/
structure StageP1CalleeContracts (A : RustAlloc) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (loadDropAddr trustDropAddr : BitVec 64) : Prop where
  alloc : AllocHooks A abs
  loadFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) loadDropAddr futNoopDropSpec
  trustFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) trustDropAddr futNoopDropSpec

/-! ## 2. Coroutine & Stack Frame Layouts for `0x4b0cc` -/

/-- Callee-saved registers `x19..x30` saved at `sp0 - 0x60#64 .. sp0` in `0x4b0cc` prologue. -/
def decryptPrekeySavedRegsAt (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((8#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x30) ∗
  ((16#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x28) ∗
  ((24#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x27) ∗
  ((32#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x26) ∗
  ((40#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x25) ∗
  ((48#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x24) ∗
  ((56#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x23) ∗
  ((64#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x22) ∗
  ((72#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x21) ∗
  ((80#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x20) ∗
  ((88#64 + (sp0 - 0x60#64)) ↦₆₄ s0.readReg64 .x19)

/-- Initial 14 words (`0x00..0x70`) of the `message_decrypt_prekey::{closure#0}` coroutine at
`coroPtr`. -/
def decryptPrekeyCoroInitAt (coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64) : SepProp :=
  (coroPtr ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x08#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x10#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x18#64) ↦₆₄ sessStorePtr) ∗
  ((coroPtr + 0x20#64) ↦₆₄ sessStoreVt) ∗
  ((coroPtr + 0x28#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x30#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x38#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x40#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x48#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x50#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x58#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x60#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x68#64) ↦₆₄ rngPtr)

/-- Copied 14 words (`0x70..0xe0`) of the `message_decrypt_prekey::{closure#0}` coroutine at
`coroPtr`. -/
def decryptPrekeyCoroCopyAt (coroPtr msgPtr remoteAddrPtr localAddrPtr
    sessStorePtr sessStoreVt idStorePtr idStoreVt
    preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt rngPtr : BitVec 64) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ sessStoreVt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0xb0#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0xb8#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0xc0#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0xd8#64) ↦₆₄ rngPtr)

/-- Empty `SessionRecord` header (`32` B at `recPtr = coroPtr + 0xe0#64`):
`previous_sessions` empty `VecDeque` (`cap = 0, ptr = 8, len = 0`) and `current_session = None`
(`-1`). -/
def sessionRecordEmptyHeaderAt (recPtr : BitVec 64) : SepProp :=
  (recPtr ↦₆₄ 0#64) ∗
  ((recPtr + 0x08#64) ↦₆₄ 8#64) ∗
  ((recPtr + 0x10#64) ↦₆₄ 0#64) ∗
  ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64)

/-- Inlined `process_prekey_impl` coroutine initial state (`coroPtr + 0x2c8..0x390`, 25 words):
12 header words at `0x2c8..0x328` and 13 active words at `0x328..0x390`. -/
def processPrekeyInnerInitAt (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) : SepProp :=
  ((coroPtr + 0x2c8#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x2d0#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x2d8#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x2e0#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x2e8#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x2f0#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x2f8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x300#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x308#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x310#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x318#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x320#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x328#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x330#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x338#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x340#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((coroPtr + 0x348#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x350#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x358#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x360#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x368#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x370#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x378#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x380#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x388#64) ↦₆₄ (msgPtr + 0xc8#64))

/-- Inlined `process_prekey_impl` post-trust coroutine fields written at `+0x0734..+0x0760`
(`coroPtr + 0x428..0x468` and `coroPtr + 0x490..0x4b0`). -/
def processPrekeyPostTrustAt (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64) : SepProp :=
  ((coroPtr + 0x428#64) ↦₆₄ spkStorePtr) ∗
  ((coroPtr + 0x430#64) ↦₆₄ spkStoreVt) ∗
  ((coroPtr + 0x438#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x440#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x448#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x450#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x458#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x460#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x490#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x498#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x4a0#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x4a8#64) ↦₆₄ (coroPtr + 0xe0#64))

/-! ## 3. Branch Condition & Memory Packing Lemmas for Stage P1 -/

@[local simp, wp_norm, arm64_norm]
private theorem cond_le_subs32_0_4_true :
    ConditionHolds .LE (subsPState32 0#32 4#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_le_subs32_0_2_true :
    ConditionHolds .LE (subsPState32 0#32 2#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_adds64_neg1_3_true :
    ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 3#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_adds64_neg1_2_true :
    ConditionHolds .NE (addsPState64 0xffffffffffffffff#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_eq_adds64_neg1_1_true :
    ConditionHolds .EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_adds64_neg2_3_true :
    ConditionHolds .NE (addsPState64 0xfffffffffffffffe#64 3#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, wp_norm, arm64_norm]
private theorem cond_ne_adds64_neg2_2_false :
    ConditionHolds .NE (addsPState64 0xfffffffffffffffe#64 2#64) = false := by
  simp only [ConditionHolds, addsPState64]; decide

private theorem bv_add_sub_lit (x a b : BitVec 64) :
    a + (x - b) = x - (b - a) := by bv_omega

/-- Fold the `load_session` scratch slots (`sp + 0xd8..0x234` and `sp + 0x3e0..0x550`) back into
`memRegion (sp + 0xd8#64) 348 ∗ memRegion (sp + 0x3e0#64) 368`. -/
theorem loadSessionScratch_fold_p1 (sp w0 w8 w20 w28 w36 w44 u0 u1 u2 u3 : BitVec 64)
    (d16 d52 du4 : BitVec 32) {bs312 : List (BitVec 8)} (hbs312 : bs312.length = 312) :
    ((sp + 0xd8#64) ↦ₛ bs312) ∗
    ((sp + 0x210#64) ↦₆₄ u0) ∗ ((sp + 0x218#64) ↦₆₄ u1) ∗
    ((sp + 0x220#64) ↦₆₄ u2) ∗ ((sp + 0x228#64) ↦₆₄ u3) ∗
    ((sp + 0x230#64) ↦₃₂ du4) ∗
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₆₄ w8) ∗
    ((sp + 0x3f0#64) ↦₃₂ d16) ∗ ((sp + 0x3f4#64) ↦₆₄ w20) ∗
    ((sp + 0x3fc#64) ↦₆₄ w28) ∗ ((sp + 0x404#64) ↦₆₄ w36) ∗
    ((sp + 0x40c#64) ↦₆₄ w44) ∗ ((sp + 0x414#64) ↦₃₂ d52) ∗
    ((sp + 0x418#64) ↦ₛ bs312) ⊢
      memRegion (sp + 0xd8#64) 348 ∗
      memRegion (sp + 0x3e0#64) 368 := by
  have hb1 : ((sp + 0xd8#64) ↦ₛ bs312) ⊢ memRegion (sp + 0xd8#64) 312 := by
    have h := pointsToBytes_entails_memRegion (sp + 0xd8#64) bs312
    rwa [hbs312] at h
  have hb2 : ((sp + 0x418#64) ↦ₛ bs312) ⊢ memRegion (sp + 0x418#64) 312 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x418#64) bs312
    rwa [hbs312] at h
  rw [ProofLib.memRegion_split' (b := sp + 0xd8#64) (n := 312) (k := 36)
        (b' := sp + 0x210#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x210#64) (n := 8) (k := 28)
        (b' := sp + 0x218#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x218#64) (n := 8) (k := 20)
        (b' := sp + 0x220#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x220#64) (n := 8) (k := 12)
        (b' := sp + 0x228#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x228#64) (n := 8) (k := 4)
        (b' := sp + 0x230#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 360)
        (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 352)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 4) (k := 348)
        (b' := sp + 0x3f4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f4#64) (n := 8) (k := 340)
        (b' := sp + 0x3fc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3fc#64) (n := 8) (k := 332)
        (b' := sp + 0x404#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x404#64) (n := 8) (k := 324)
        (b' := sp + 0x40c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x40c#64) (n := 8) (k := 316)
        (b' := sp + 0x414#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x414#64) (n := 4) (k := 312)
        (b' := sp + 0x418#64) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono hb1
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) hb2)))))))))))))

/-- Fold the 48-byte `is_trusted_identity` poll output slot at `sp + 0x3e0..0x410` into
`memRegion (sp + 0x3e0#64) 48`. -/
theorem trustOut48_fold_p1 (sp w0 : BitVec 64) (b8 : BitVec 8) (d9 : BitVec 32)
    (h13 : BitVec 16) (b15 : BitVec 8) (w16 : BitVec 64) (d24 d28 : BitVec 32)
    (w32 w40 : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗
    ((sp + 0x3e8#64) ↦₈ b8) ∗
    ((sp + 0x3e9#64) ↦₃₂ d9) ∗
    ((sp + 0x3ed#64) ↦₁₆ h13) ∗
    ((sp + 0x3ef#64) ↦₈ b15) ∗
    ((sp + 0x3f0#64) ↦₆₄ w16) ∗
    ((sp + 0x3f8#64) ↦₃₂ d24) ∗
    ((sp + 0x3fc#64) ↦₃₂ d28) ∗
    ((sp + 0x400#64) ↦₆₄ w32) ∗
    ((sp + 0x408#64) ↦₆₄ w40) ⊢
      memRegion (sp + 0x3e0#64) 48 := by
  have h16_ent : ∀ (p : BitVec 64) (v : BitVec 16), (p ↦₁₆ v) ⊢ memRegion p 2 := by
    intro p v
    have h := pointsToBytes_entails_memRegion p (unpack16 v)
    rwa [ ← pointsTo16_eq_pointsToBytes, unpack16_length] at h
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 40)
        (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 1) (k := 39)
        (b' := sp + 0x3e9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e9#64) (n := 4) (k := 35)
        (b' := sp + 0x3ed#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ed#64) (n := 2) (k := 33)
        (b' := sp + 0x3ef#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ef#64) (n := 1) (k := 32)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 24)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 4) (k := 20)
        (b' := sp + 0x3fc#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3fc#64) (n := 4) (k := 16)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 8)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (h16_ent _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (pointsTo64_entails_memRegion _ _)))))))))

end CryptoVerification.E2E.Pqxdh.ResponderClosure
