/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesDecode
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Small Callee Proofs for PQXDH Initiator

Proves `subroutine_ok` on `tripleRatchetProgAt` and `[LibsignalPlacement]` for
`<kem::Public as KeyKind>::key_length`, `<KyberPreKeyId as Display>::fmt`,
`<PqxdhRng as RngCore>::{fill_bytes, next_u32, next_u64}`,
`<SessionState>::set_unacknowledged_kyber_pre_key_id`, `<SessionState>::set_kyber_ciphertext`, and
`<PrivateKey>::public_key`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## 1. `<kem::Public as KeyKind>::key_length` (`0x29a18`, 2 instructions) -/

section KemPublicKeyLength

@[simp, arm64_norm]
abbrev kemPublicKeyLengthName : String :=
  "<libsignal_protocol::kem::Public as libsignal_protocol::kem::KeyKind>::key_length"

def kemPublicKeyLengthSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = 0x620#64 ∧ sf.trace = s0.trace⌝

theorem kemPublicKeyLength_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr kemPublicKeyLengthName)
      kemPublicKeyLengthSpec := by
  unfold kemPublicKeyLengthSpec
  code_fetches CryptoVerification.libsignalSessionCode kemPublicKeyLength b
    (Rust.withPanics (trTrapExterns C abs))
    libsignalSessionCode_fnOff_0x29afc 0x29afc 8
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem kemPublicKeyLength_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kemPublicKeyLengthName)
      kemPublicKeyLengthSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr kemPublicKeyLengthName]
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap kemPublicKeyLength_ok_trap

end KemPublicKeyLength

/-! ## 3. `<PqxdhRng as RngCore>::{fill_bytes, next_u32, next_u64}` (`0x76664..0x4f784`) -/

section PqxdhRng

@[simp, arm64_norm]
abbrev pqxdhRngFillBytesName : String :=
  "<libsignal_pqxdh_e2e::PqxdhRng as rand_core::RngCore>::fill_bytes"

@[simp, arm64_norm]
abbrev pqxdhRngNextU32Name : String :=
  "<libsignal_pqxdh_e2e::PqxdhRng as rand_core::RngCore>::next_u32"

@[simp, arm64_norm]
abbrev pqxdhRngNextU64Name : String :=
  "<libsignal_pqxdh_e2e::PqxdhRng as rand_core::RngCore>::next_u64"

def pqxdhRngFillBytesSpec (ctl : BitVec 64) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, len, cur, rest) s =>
    ⌜s.readReg64 .x1 = dst ∧ (s.readReg64 .x2).toNat = len⌝ ∗
      memRegion dst len ∗ tapeAfter ctl cur rest 0
  post := fun (dst, len, cur, rest) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ (rest ++ List.replicate len 0#8).take len) ∗
      tapeAfter ctl cur rest (min len rest.length)

private theorem memRegion_4_pointsTo32_at_sub20 (sp : BitVec 64) (v : BitVec 64) :
    ((sp - 24#64) ↦₆₄ v) ⊢
      (∃∗ lo : BitVec 32, (sp - 24#64) ↦₃₂ lo) ∗
      (∃∗ hi : BitVec 32, (sp - 20#64) ↦₃₂ hi) := by
  refine Entails.trans (pointsTo64_entails_memRegion (sp - 24#64) v) ?_
  rw [memRegion_split (sp - 24#64) 4 4 (by decide),
      memRegion_four (sp - 24#64),
      show sp - 24#64 + 4#64 = sp - 20#64 by bv_arith,
      memRegion_four (sp - 20#64)]
  exact Entails.refl _

private theorem pointsTo32_two_entails_cell (sp : BitVec 64) (lo hi : BitVec 32) :
    ((sp - 24#64) ↦₃₂ lo) ∗ ((sp - 20#64) ↦₃₂ hi) ⊢
      ∃∗ u1 : BitVec 64, (sp - 24#64) ↦₆₄ u1 := by
  rw [← ProofLib.memRegion_eight (sp - 24#64),
      memRegion_split (sp - 24#64) 4 4 (by decide),
      show sp - 24#64 + 4#64 = sp - 20#64 by bv_arith]
  exact sepConj_mono (pointsTo32_entails_memRegion _ lo) (pointsTo32_entails_memRegion _ hi)

def rngWord32 (rest : List (BitVec 8)) : BitVec 32 :=
  let bs := rest ++ List.replicate 4 0#8
  pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)

def pqxdhRngNextU32Spec (ctl : BitVec 64) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (cur, rest) s =>
    tapeAfter ctl cur rest 0 ∗ cells (s.sp - 32#64) 4
  post := fun (cur, rest) s0 sf =>
    ⌜sf.readReg64 .x0 = (rngWord32 rest).zeroExtend 64 ∧ sf.trace = s0.trace⌝ ∗
      tapeAfter ctl cur rest (min 4 rest.length) ∗ cells (s0.sp - 32#64) 4

def rngWord64 (rest : List (BitVec 8)) : BitVec 64 :=
  let bs := rest ++ List.replicate 8 0#8
  pack64 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8)
    (bs.getD 4 0#8) (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8)

def pqxdhRngNextU64Spec (ctl : BitVec 64) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (cur, rest) s =>
    tapeAfter ctl cur rest 0 ∗ cells (s.sp - 32#64) 4
  post := fun (cur, rest) s0 sf =>
    ⌜sf.readReg64 .x0 = rngWord64 rest ∧ sf.trace = s0.trace⌝ ∗
      tapeAfter ctl cur rest (min 8 rest.length) ∗ cells (s0.sp - 32#64) 4

end PqxdhRng

/-! ## 4. `<SessionState>::set_unacknowledged_kyber_pre_key_id` (`0x123d0`, 13 instructions) -/

section SetUnackKyberPreKeyId

@[simp, arm64_norm]
abbrev setUnackKyberPreKeyIdName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id"

def setUnackKyberPreKeyIdSpec : Spec (BitVec 64 × BitVec 64 × BitVec 32) where
  pre := fun (statePtr, cap, kyberPreKeyId) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ (s.readReg64 .x1).setWidth 32 = kyberPreKeyId ∧
      cap + 1#64 ≠ 0#64⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      (∃∗ w : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w)
  post := fun (statePtr, cap, kyberPreKeyId) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      ((statePtr + 0x140#64) ↦₃₂ kyberPreKeyId)

private theorem cond_eq_adds_1_false_trap {cap : BitVec 64} (hne : cap + 1#64 ≠ 0#64) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [ProofLib.conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

theorem setUnackKyberPreKeyId_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr setUnackKyberPreKeyIdName)
      setUnackKyberPreKeyIdSpec := by
  unfold setUnackKyberPreKeyIdSpec
  code_fetches CryptoVerification.libsignalSessionCode setUnackKyberPreKeyId b
    (Rust.withPanics (trTrapExterns C abs))
    libsignalSessionCode_fnOff_0x123d0 0x123d0 52
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨statePtr, cap, kyberPreKeyId⟩
  dsimp only at *
  subst h_1 h_2
  wp_pull_exists
  have hcond : ConditionHolds .EQ (addsPState64 cap 1#64) = false :=
    cond_eq_adds_1_false_trap ‹_›
  wp_steps
  wp_done

theorem setUnackKyberPreKeyId_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr setUnackKyberPreKeyIdName)
      setUnackKyberPreKeyIdSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr setUnackKyberPreKeyIdName]
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap setUnackKyberPreKeyId_ok_trap

end SetUnackKyberPreKeyId

/-! ## 5. `<SessionState>::set_kyber_ciphertext` (`0x12064`, 22 instructions) -/

section SetKyberCiphertext

@[simp, arm64_norm]
abbrev setKyberCiphertextName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"

def setKyberCiphertextNoneSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (statePtr, ctPtr, ctLen) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x1 = ctPtr ∧ s.readReg64 .x2 = ctLen⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w1 : BitVec 64, (statePtr + 0x130#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (statePtr + 0x138#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w3) ∗
      cells (s.sp - 48#64) 6
  post := fun (statePtr, ctPtr, ctLen) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x130#64) ↦₆₄ ctPtr) ∗
      ((statePtr + 0x138#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x140#64) ↦₃₂ 0xffffffff#32) ∗
      cells (s0.sp - 48#64) 6

theorem setKyberCiphertext_none_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr setKyberCiphertextName)
      setKyberCiphertextNoneSpec := by
  unfold setKyberCiphertextNoneSpec
  cells_unfold
  code_fetches CryptoVerification.libsignalSessionCode setKyberCiphertext b
    (Rust.withPanics (trTrapExterns C abs))
    libsignalSessionCode_fnOff_0x12064 0x12064 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨statePtr, ctPtr, ctLen⟩
  dsimp only at *
  subst h h_1 h_2
  wp_pull_exists
  wp_steps
  wp_done

theorem setKyberCiphertext_none_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr setKyberCiphertextName)
      setKyberCiphertextNoneSpec := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr setKyberCiphertextName]
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap setKyberCiphertext_none_ok_trap

end SetKyberCiphertext

/-! ## 6. `<PrivateKey>::public_key` (`0x3e594`, 26 instructions) -/

section PrivateKeyPublicKey

open CryptoVerification.LibsignalTripleRatchet.Keys

@[simp, arm64_norm]
abbrev privateKeyPublicKeyName : String :=
  "<libsignal_core::curve::PrivateKey>::public_key"

def privateKeyPublicKeySpec (pubKey : PubKeyFn) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64) where
  pre := fun (privPtr, sk, outPtr) s =>
    ⌜s.readReg64 .x0 = privPtr ∧ s.readReg64 .x8 = outPtr⌝ ∗
      (privPtr ↦ₛ sk.toList) ∗ memRegion outPtr 33 ∗
      cells (s.sp - 64#64) 8
  post := fun (privPtr, sk, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (privPtr ↦ₛ sk.toList) ∗
      (outPtr ↦₈ 0#8) ∗
      ((outPtr + 1#64) ↦ₛ (pubKey (Ratchet.clampScalar sk)).toList) ∗
      cells (s0.sp - 64#64) 8

private theorem cells8_split_publicKey (sp : BitVec 64) :
    cells (sp - 64#64) 8 =
      memRegion (sp - 64#64) 32 ∗ cells (sp - 32#64) 4 := by
  rw [← ProofLib.memRegion_cells (sp - 64#64) 8 (by decide),
      memRegion_split (sp - 64#64) 32 32 (by decide),
      show sp - 64#64 + 32#64 = sp - 32#64 by bv_arith,
      ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]

private theorem memRegion_33_split_1_32 (a : BitVec 64) :
    memRegion a 33 = (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 32 := by
  rw [memRegion_split a 1 32 (by decide), memRegion_one]

private theorem replicate32_zero_entails_view1 (sp : BitVec 64) :
    ((sp - 64#64) ↦ₛ List.replicate 32 0#8) ⊢
      (∃∗ b0 : BitVec 8, (sp - 64#64) ↦₈ b0) ∗
      (∃∗ u1 : BitVec 64, (sp - 63#64) ↦₆₄ u1) ∗
      (∃∗ u9 : BitVec 64, (sp - 55#64) ↦₆₄ u9) ∗
      memRegion (sp - 47#64) 15 := by
  have h1 := memRegion_32_view1 (sp - 64#64)
  have h63 : sp - 64#64 + 1#64 = sp - 63#64 := by bv_arith
  have h55 : sp - 64#64 + 9#64 = sp - 55#64 := by bv_arith
  have h47 : sp - 64#64 + 17#64 = sp - 47#64 := by bv_arith
  simp only [h63, h55, h47] at h1
  rw [← h1]
  exact pointsToBytes_entails_memRegion_of_eq (by decide)

theorem privateKeyPublicKey_ok_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr privateKeyPublicKeyName)
      (privateKeyPublicKeySpec C.pubKey) := by
  unfold privateKeyPublicKeySpec
  have hpub := pubFromSecret_ok_at_trap (b := b) (C := C)
    (abs := abs) (name := privateKeyPublicKeyName) (k := num% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from" - 0x3e678))
    (by simp only [libsignalSessionCode_fnOff_0x3e678, (ls_stub% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from")])
  have hdrop := CryptoVerification.LibsignalTripleRatchet.Keys.staticDrop_ok_at_tripleRatchet_trap
      (b := b) (C := C)
    (abs := abs) (name := privateKeyPublicKeyName) (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - 0x3e678))
    (by simp only [libsignalSessionCode_fnOff_0x3e678, (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")])
  simp only [derivePublicKeyBytesSpec] at hpub
  simp only [zeroizeSecretSpec] at hdrop
  code_fetches CryptoVerification.libsignalSessionCode privateKeyPublicKey b
    (Rust.withPanics (trTrapExterns C abs))
    libsignalSessionCode_fnOff_0x3e678 0x3e678 104
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨privPtr, sk, outPtr⟩
  dsimp only at *
  subst h h_1
  rw [cells8_split_publicKey s0.sp,
      memRegion_32_view1 (s0.sp - 64#64),
      memRegion_33_split_1_32 (s0.readReg64 (.gpr 8#5))]
  cells_unfold
  refine SepWP.weaken_pre
    (Entails.of_eq (by rw [vec32_view2 (s0.readReg64 (.gpr 0#5)) sk])) ?_
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) sk).symm)
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) sk))
    (by sep_focus) ?_
  wp_steps
  refine SepWP.fold
    (by simpa only [bv_sub_add_lit, sepConj_assoc] using stur_q0_reframe (s0.sp - 64#64) sk)
    (by sep_focus) ?_
  wp_pull_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) sk).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq
      (by simpa only [bv_sub_add_lit] using (clampScalar_view2 (s0.sp - 64#64) sk).symm))
    (by sep_focus) ?_
  wp_call hpub ⟨s0.sp - 64#64, Ratchet.clampScalar sk, s0.readReg64 (.gpr 8#5) + 1#64⟩
  wp_steps
  refine SepWP.fold
    (pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length (Ratchet.clampScalar sk)))
    (by sep_focus) ?_
  wp_call hdrop (s0.sp - 64#64)
  wp_steps
  refine SepWP.fold (replicate32_zero_entails_view1 s0.sp) (by sep_focus) ?_
  wp_pull_exists
  wp_done

theorem privateKeyPublicKey_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr privateKeyPublicKeyName)
      (privateKeyPublicKeySpec C.pubKey) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr privateKeyPublicKeyName]
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap privateKeyPublicKey_ok_trap

end PrivateKeyPublicKey

/-! ## 2. `<KyberPreKeyId as Display>::fmt` (`0x245ac`, 15 instructions) -/

section KyberPreKeyIdDisplay

@[simp, arm64_norm]
abbrev kyberPreKeyIdDisplayName : String :=
  "<libsignal_protocol::state::kyber_prekey::KyberPreKeyId as core::fmt::Display>::fmt"

abbrev kyberPreKeyIdDisplayStack : Nat := extHookStack + 0x20

private theorem stackAt_kyberPreKeyIdDisplay (sp : BitVec 64) :
    stackAt sp kyberPreKeyIdDisplayStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

def kyberPreKeyIdDisplaySpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (f, v, vt, bs) s =>
    ⌜s.readReg64 .x1 = f⌝ ∗ (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗ vecU8 A v bs ∗ A.pool ∗
      stackAt s.sp kyberPreKeyIdDisplayStack
  post := fun (f, v, vt, _) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗ (f ↦₆₄ v) ∗
      ((f + 8#64) ↦₆₄ vt) ∗ (∃∗ bs' : List (BitVec 8), vecU8 A v bs') ∗ A.pool ∗
      stackAt s0.sp kyberPreKeyIdDisplayStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

attribute [local irreducible] Program.fnAddr Program.fnOff
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  libsignalSessionCode_fnOff_0x245ac (ls_stub% "core::fmt::write")

theorem kyberPreKeyIdDisplay_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr kyberPreKeyIdDisplayName)
      (kyberPreKeyIdDisplaySpec A) := by
  simp only [kyberPreKeyIdDisplaySpec, stackAt_kyberPreKeyIdDisplay]
  cells_unfold
  have hwrite := ProtocolAddressDisplay.fmtWrite_ok_at_trap (b := b) (C := C)
    (name := kyberPreKeyIdDisplayName) (k := num% (ls_off% "core::fmt::write" - 0x245ac)) hW
  clear hW
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff kyberPreKeyIdDisplayName = 0x245ac :=
    libsignalSessionCode_fnOff_0x245ac
  code_fetches CryptoVerification.libsignalSessionCode
    kyberPreKeyIdDisplay b
    (Rust.withPanics (trTrapExterns C abs)) hfn 0x245ac 60
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b
        (Rust.withPanics (trTrapExterns C abs))).fnAddr kyberPreKeyIdDisplayName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hwrite ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr kyberPreKeyIdDisplayName = entry
  examples_hide_fetches
  obtain ⟨f, v, vt, bs⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::fmt::write" - 0x245ac))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (v, bs))
    (ret_pc := entry + 48#64) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame
      (ProtocolAddressDisplay.allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24
  simp (config := { decide := true }) only [arm64_norm] at hx25 hx26 hx27 hx28 hfp
  apply SepWPp.of_sepWP_ret
  simp only [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps
  wp_done

theorem kyberPreKeyIdDisplay_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr kyberPreKeyIdDisplayName)
      (kyberPreKeyIdDisplaySpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr kyberPreKeyIdDisplayName]
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (kyberPreKeyIdDisplay_ok_trap b C A abs hW)

end KyberPreKeyIdDisplay

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

theorem kemPublicKeyLength_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_110).rebase (blkPl_110).base H) (blkPl_110).base
      kemPublicKeyLengthSpec := by
  unfold kemPublicKeyLengthSpec; wp_init x s0; wp_steps; wp_done

theorem setUnackKyberPreKeyId_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_34).rebase (blkPl_34).base H) (blkPl_34).base
      setUnackKyberPreKeyIdSpec := by
  unfold setUnackKyberPreKeyIdSpec; wp_init x s0
  rcases x with ⟨statePtr, cap, kyberPreKeyId⟩; dsimp only at *; subst h_1 h_2
  wp_pull_exists
  have hcond : ConditionHolds .EQ (addsPState64 cap 1#64) = false := cond_eq_adds_1_false_trap ‹_›
  wp_steps; wp_done

theorem setKyberCiphertext_none_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_31).rebase (blkPl_31).base H) (blkPl_31).base
      setKyberCiphertextNoneSpec := by
  unfold setKyberCiphertextNoneSpec; cells_unfold; wp_init x s0
  rcases x with ⟨statePtr, ctPtr, ctLen⟩; dsimp only at *; subst h h_1 h_2
  wp_pull_exists; wp_steps; wp_done

theorem kyberPreKeyIdDisplay_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hW : HookSat H lsFmtWriteSym (fmtWriteSpec A)) :
    subroutine_ok ((blkPC_81).rebase (blkPl_81).base H) (blkPl_81).base
      (kyberPreKeyIdDisplaySpec A) := by
  simp only [kyberPreKeyIdDisplaySpec, stackAt_kyberPreKeyIdDisplay]; cells_unfold
  have hwrite : subroutine_ok ((blkPC_81).rebase (blkPl_81).base H) (lsρ lsFmtWriteSym)
      (fmtWriteSpec A) := ls_hook_ok_of_mem hW
  wpp_init x s0; obtain ⟨f, v, vt, bs⟩ := x; dsimp only at *
  apply SepWPp.of_sepWP (mid := lsρ lsFmtWriteSym)
  wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (v, bs))
    (ret_pc := (blkPl_81).base + 48#64) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame
      (ProtocolAddressDisplay.allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24
  simp (config := { decide := true }) only [arm64_norm] at hx25 hx26 hx27 hx28 hfp
  apply SepWPp.of_sepWP_ret
  simp only [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps; wp_done

end CryptoVerification.E2E.Pqxdh
