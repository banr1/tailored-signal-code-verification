/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Stage P2 Callee Contracts, `KeyPair` Layouts, and Branch Normalization

Defines isolated Stage P2 store-callee contracts (`StageP2CalleeContracts`), unaligned 64-byte
`KeyPair` / prekey-record poll layouts (`keyPair64UnalignedAt`), and branch-condition normalization
lemmas for `message_decrypt_prekey::<PqxdhRng>::{closure#0}`.
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
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Isolated Callee Contracts & Stubs for Stage P2 (`+0x0868..+0x1778`) -/

/-- Isolated external callee contracts for Stage P2 (`spk`, `kyber`, `opk`, `ik`, `regId`
future drops). Downstream closure and assembly proofs instantiate this structure directly. -/
structure StageP2CalleeContracts (A : RustAlloc) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (spkDropAddr kyberDropAddr opkDropAddr ikDropAddr regIdDropAddr : BitVec 64) : Prop where
  alloc : AllocHooks A abs
  spkFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) spkDropAddr futNoopDropSpec
  kyberFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) kyberDropAddr futNoopDropSpec
  opkFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) opkDropAddr futNoopDropSpec
  ikFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) ikDropAddr futNoopDropSpec
  regIdFutDrop : subroutine_ok (tripleRatchetProgAt b C ctl abs) regIdDropAddr futNoopDropSpec

/-! ## 2. Coroutine & KeyPair Layouts for Stage P2 -/

/-- Active 10 words of inlined `process_prekey_impl` stored at `coroPtr + 0x3f8..0x488`:
`0x3f8..0x428` (`kyberStore`, `preKeyStore`, `idStore` fat pointers) and
`0x468..0x488` (`msgPtr`, `remoteAddrPtr`, `localAddrPtr`, `sessionRecordPtr`). -/
def processPrekeyActive10At (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt : BitVec 64) : SepProp :=
  ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
  ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
  ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
  ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))

/-- 7 contiguous bytes at `a .. a + 7`. -/
def bytes7At (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)

/-- 64-byte `curve::KeyPair` in the unaligned `7B + 7×8B + 1B` layout starting at `a`. -/
def keyPair64UnalignedAt (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (b63 : BitVec 8) : SepProp :=
  bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
  ((a + 0x07#64) ↦₆₄ w0) ∗
  ((a + 0x0f#64) ↦₆₄ w1) ∗
  ((a + 0x17#64) ↦₆₄ w2) ∗
  ((a + 0x1f#64) ↦₆₄ w3) ∗
  ((a + 0x27#64) ↦₆₄ w4) ∗
  ((a + 0x2f#64) ↦₆₄ w5) ∗
  ((a + 0x37#64) ↦₆₄ w6) ∗
  ((a + 0x3f#64) ↦₈ b63)

/-- `SignedPreKeyRecord` / `KyberPreKeyRecord` 64-byte `Poll::Ready(Ok(rec))` output at `a = sp +
0x3e0`. -/
def preKeyRecordOut64At
  (a pubCap pubPtr pubLen privCap privPtr privLen sigCap sigPtr : BitVec 64) : SepProp :=
  (a ↦₆₄ pubCap) ∗
  ((a + 0x08#64) ↦₆₄ pubPtr) ∗
  ((a + 0x10#64) ↦₆₄ pubLen) ∗
  ((a + 0x18#64) ↦₆₄ privCap) ∗
  ((a + 0x20#64) ↦₆₄ privPtr) ∗
  ((a + 0x28#64) ↦₆₄ privLen) ∗
  ((a + 0x30#64) ↦₆₄ sigCap) ∗
  ((a + 0x38#64) ↦₆₄ sigPtr)

/-! ## 3. Arithmetic & Branch Condition Normalization Lemmas -/

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs32_4_3 :
    ConditionHolds CondCode.NE (subsPState32 4#32 3#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_33_2 :
    ConditionHolds CondCode.NE (addsPState64 33#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_adds64_33_1 :
    ConditionHolds CondCode.EQ (addsPState64 33#64 1#64) = false := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_subs32_0_1 :
    ConditionHolds CondCode.NE (subsPState32 0#32 1#32) = true := by
  simp only [ConditionHolds, subsPState32]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_1569_2 :
    ConditionHolds CondCode.NE (addsPState64 1569#64 2#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_eq_adds64_1569_1 :
    ConditionHolds CondCode.EQ (addsPState64 1569#64 1#64) = false := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_neg2_2 :
    ConditionHolds CondCode.NE (addsPState64 0xfffffffffffffffe#64 2#64) = false := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem cond_ne_adds64_neg2_3 :
    ConditionHolds CondCode.NE (addsPState64 0xfffffffffffffffe#64 3#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
theorem zext64_bv32_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).setWidth 8 = b0 := by
  rw [BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le _ (by decide)]
  simp only [BitVec.setWidth_append, Nat.le_refl, ↓reduceDIte, BitVec.setWidth_eq]

@[local simp, local wp_norm, local arm64_norm]
theorem zext64_bv32_shr8_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).ushiftRight 8).setWidth 8 = b1 := by
  rw [BitVec.ushiftRight_eq]; bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem zext64_bv32_shr16_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).ushiftRight 16).setWidth 8 = b2 := by
  rw [BitVec.ushiftRight_eq]; bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem zext64_bv32_shr24_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).ushiftRight 24).setWidth 8 = b3 := by
  rw [BitVec.ushiftRight_eq]; bv_bits

@[local simp, local wp_norm, local arm64_norm]
theorem zext64_bv8_setWidth_8 (b0 : BitVec 8) :
    (b0.zeroExtend 64).setWidth 8 = b0 :=
  _root_.BitVec.setWidth_setWidth_of_le b0 (_root_.Nat.le_add_left 8 56)

theorem adrp_logLevel_0xd64 {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64) (he : entry = b + 0x7200c#64) :
    (((entry + 0xd64#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x72000) = b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) ∧
    ((((entry + 0xd64#64) &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x72000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) := by
  subst he
  have hp : ((b + 0x7200c#64 + 0xd64#64) &&& 18446744073709547520#64) = b + 0x72000#64 := by
    rw [BitVec.add_assoc, ProofLib.ObjectLoad.adrp_page_of_aligned hb]
    rfl
  rw [hp]
  constructor <;> bv_omega

end CryptoVerification.E2E.Pqxdh.ResponderClosure
