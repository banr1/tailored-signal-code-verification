/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.Common
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers

/-!
# Shared Stack and Memory Helpers for `InMemSessionStore::store_session::{closure#0}` (`0x08ee4`)
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.HashbrownBin
open LoadSingle
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [arm64_norm ↓, wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeReg64_sp
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  calleeSavedVRegs_rebuild_d8_d9

theorem memRegion_8_eq_pointsTo64 (a : BitVec 64) :
    memRegion a 8 = ∃∗ v : BitVec 64, (a ↦₆₄ v) :=
  ProofLib.memRegion_eight a

theorem memRegion_4_eq_pointsTo32 (a : BitVec 64) :
    memRegion a 4 = ∃∗ v : BitVec 32, (a ↦₃₂ v) :=
  ProofLib.memRegion_four a

theorem memRegion_1_eq_pointsTo8 (a : BitVec 64) :
    memRegion a 1 = ∃∗ v : BitVec 8, (a ↦₈ v) :=
  ProofLib.memRegion_one a

@[arm64_norm, wp_norm]
theorem sp_store_prologue_eqs (sp : BitVec 64) :
    sp + bv% (2 ^ 64 - 112) = sp - 112#64 ∧
    sp - 112#64 + 8#64 = sp - 104#64 ∧
    sp - 112#64 + 16#64 = sp - 96#64 ∧
    sp - 112#64 + 16#64 + 8#64 = sp - 88#64 ∧
    sp - 112#64 + 32#64 = sp - 80#64 ∧
    sp - 112#64 + 32#64 + 8#64 = sp - 72#64 ∧
    sp - 112#64 + 48#64 = sp - 64#64 ∧
    sp - 112#64 + 48#64 + 8#64 = sp - 56#64 ∧
    sp - 112#64 + 64#64 = sp - 48#64 ∧
    sp - 112#64 + 64#64 + 8#64 = sp - 40#64 ∧
    sp - 112#64 + 80#64 = sp - 32#64 ∧
    sp - 112#64 + 80#64 + 8#64 = sp - 24#64 ∧
    sp - 112#64 + 96#64 = sp - 16#64 ∧
    sp - 112#64 + 96#64 + 8#64 = sp - 8#64 ∧
    sp - 112#64 - 1200#64 = sp - 1312#64 ∧
    sp - 1312#64 + 0#64 = sp - 1312#64 ∧
    sp - 1312#64 + 8#64 = sp - 1304#64 ∧
    sp - 1312#64 + 16#64 = sp - 1296#64 ∧
    sp - 1312#64 + 24#64 = sp - 1288#64 ∧
    sp - 1312#64 + 24#64 + 8#64 = sp - 1280#64 ∧
    sp - 1312#64 + 44#64 = sp - 1268#64 ∧
    sp - 1312#64 + 48#64 = sp - 1264#64 ∧
    sp - 1312#64 + 56#64 = sp - 1256#64 ∧
    sp - 1312#64 + 56#64 + 8#64 = sp - 1248#64 ∧
    sp - 1312#64 + 72#64 = sp - 1240#64 ∧
    sp - 1312#64 + 80#64 = sp - 1232#64 ∧
    sp - 1312#64 + 104#64 = sp - 1208#64 ∧
    sp - 1232#64 + 32#64 = sp - 1200#64 ∧
    sp - 1312#64 + 448#64 = sp - 864#64 ∧
    sp - 1312#64 + 784#64 = sp - 528#64 ∧
    sp - 528#64 + 8#64 = sp - 520#64 ∧
    sp - 528#64 + 24#64 = sp - 504#64 ∧
    sp - 528#64 + 32#64 = sp - 496#64 ∧
    sp - 1312#64 + 792#64 = sp - 520#64 ∧
    sp - 1312#64 + 800#64 = sp - 512#64 ∧
    sp - 1312#64 + 808#64 = sp - 504#64 ∧
    sp - 1312#64 + 1200#64 = sp - 112#64 ∧
    sp - 112#64 + 112#64 = sp := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega,
    by bv_omega, by bv_omega, by bv_omega⟩

/-- Decomposes the 7168-byte `storeSessionClosureStack` at `sp` into caller scratch below
`sp - 1312#64`, local frame slots in `[sp - 1312#64, sp - 112#64)`, and 14 saved 64-bit registers
in `[sp - 112#64, sp)`. -/
theorem stackAt_store_eq (sp : BitVec 64) :
    stackAt sp storeSessionClosureStack =
      stackAt (sp - 1312#64) (storeSessionClosureStack - 1312) ∗
      (∃∗ c_sp0 : BitVec 64, ((sp - 1312#64) ↦₆₄ c_sp0)) ∗
      (∃∗ c_sp8 : BitVec 64, ((sp - 1304#64) ↦₆₄ c_sp8)) ∗
      (∃∗ c_sp16 : BitVec 64, ((sp - 1296#64) ↦₆₄ c_sp16)) ∗
      (∃∗ c_sp24 : BitVec 64, ((sp - 1288#64) ↦₆₄ c_sp24)) ∗
      (∃∗ c_sp32 : BitVec 64, ((sp - 1280#64) ↦₆₄ c_sp32)) ∗
      memRegion (sp - 1272#64) 4 ∗
      (∃∗ c_sp44 : BitVec 32, ((sp - 1268#64) ↦₃₂ c_sp44)) ∗
      memRegion (sp - 1264#64) 24 ∗
      (∃∗ c_sp72 : BitVec 8, ((sp - 1240#64) ↦₈ c_sp72)) ∗
      memRegion (sp - 1239#64) 7 ∗
      memRegion (sp - 1232#64) 24 ∗
      (∃∗ c_sp104 : BitVec 64, ((sp - 1208#64) ↦₆₄ c_sp104)) ∗
      memRegion (sp - 1200#64) 336 ∗
      memRegion (sp - 864#64) 336 ∗
      memRegion (sp - 528#64) 344 ∗
      memRegion (sp - 184#64) 24 ∗
      memRegion (sp - 160#64) 48 ∗
      (∃∗ c_d9 : BitVec 64, ((sp - 112#64) ↦₆₄ c_d9)) ∗
      (∃∗ c_d8 : BitVec 64, ((sp - 104#64) ↦₆₄ c_d8)) ∗
      (∃∗ c_x29 : BitVec 64, ((sp - 96#64) ↦₆₄ c_x29)) ∗
      (∃∗ c_x30 : BitVec 64, ((sp - 88#64) ↦₆₄ c_x30)) ∗
      (∃∗ c_x28 : BitVec 64, ((sp - 80#64) ↦₆₄ c_x28)) ∗
      (∃∗ c_x27 : BitVec 64, ((sp - 72#64) ↦₆₄ c_x27)) ∗
      (∃∗ c_x26 : BitVec 64, ((sp - 64#64) ↦₆₄ c_x26)) ∗
      (∃∗ c_x25 : BitVec 64, ((sp - 56#64) ↦₆₄ c_x25)) ∗
      (∃∗ c_x24 : BitVec 64, ((sp - 48#64) ↦₆₄ c_x24)) ∗
      (∃∗ c_x23 : BitVec 64, ((sp - 40#64) ↦₆₄ c_x23)) ∗
      (∃∗ c_x22 : BitVec 64, ((sp - 32#64) ↦₆₄ c_x22)) ∗
      (∃∗ c_x21 : BitVec 64, ((sp - 24#64) ↦₆₄ c_x21)) ∗
      (∃∗ c_x20 : BitVec 64, ((sp - 16#64) ↦₆₄ c_x20)) ∗
      (∃∗ c_x19 : BitVec 64, ((sp - 8#64) ↦₆₄ c_x19)) := by
  have h0 : stackAt (sp - 1312#64) (storeSessionClosureStack - 1312) =
      memRegion (sp - 19456#64) 18144 := by
    change memRegion (sp - 1312#64 - 18144#64) 18144 = memRegion (sp - 19456#64) 18144
    rw [show sp - 1312#64 - 18144#64 = sp - 19456#64 by bv_omega]
  rw [h0]
  unfold stackAt storeSessionClosureStack
  change memRegion (sp - 19456#64) 19456 = _
  rw [memRegion_split (sp - 19456#64) 18144 1312 (by decide),
      show sp - 19456#64 + 18144#64 = sp - 1312#64 by bv_omega,
      memRegion_split (sp - 1312#64) 8 1304 (by decide),
      show sp - 1312#64 + 8#64 = sp - 1304#64 by bv_omega,
      memRegion_split (sp - 1304#64) 8 1296 (by decide),
      show sp - 1304#64 + 8#64 = sp - 1296#64 by bv_omega,
      memRegion_split (sp - 1296#64) 8 1288 (by decide),
      show sp - 1296#64 + 8#64 = sp - 1288#64 by bv_omega,
      memRegion_split (sp - 1288#64) 8 1280 (by decide),
      show sp - 1288#64 + 8#64 = sp - 1280#64 by bv_omega,
      memRegion_split (sp - 1280#64) 8 1272 (by decide),
      show sp - 1280#64 + 8#64 = sp - 1272#64 by bv_omega,
      memRegion_split (sp - 1272#64) 4 1268 (by decide),
      show sp - 1272#64 + 4#64 = sp - 1268#64 by bv_omega,
      memRegion_split (sp - 1268#64) 4 1264 (by decide),
      show sp - 1268#64 + 4#64 = sp - 1264#64 by bv_omega,
      memRegion_split (sp - 1264#64) 24 1240 (by decide),
      show sp - 1264#64 + 24#64 = sp - 1240#64 by bv_omega,
      memRegion_split (sp - 1240#64) 1 1239 (by decide),
      show sp - 1240#64 + 1#64 = sp - 1239#64 by bv_omega,
      memRegion_split (sp - 1239#64) 7 1232 (by decide),
      show sp - 1239#64 + 7#64 = sp - 1232#64 by bv_omega,
      memRegion_split (sp - 1232#64) 24 1208 (by decide),
      show sp - 1232#64 + 24#64 = sp - 1208#64 by bv_omega,
      memRegion_split (sp - 1208#64) 8 1200 (by decide),
      show sp - 1208#64 + 8#64 = sp - 1200#64 by bv_omega,
      memRegion_split (sp - 1200#64) 336 864 (by decide),
      show sp - 1200#64 + 336#64 = sp - 864#64 by bv_omega,
      memRegion_split (sp - 864#64) 336 528 (by decide),
      show sp - 864#64 + 336#64 = sp - 528#64 by bv_omega,
      memRegion_split (sp - 528#64) 344 184 (by decide),
      show sp - 528#64 + 344#64 = sp - 184#64 by bv_omega,
      memRegion_split (sp - 184#64) 24 160 (by decide),
      show sp - 184#64 + 24#64 = sp - 160#64 by bv_omega,
      memRegion_split (sp - 160#64) 48 112 (by decide),
      show sp - 160#64 + 48#64 = sp - 112#64 by bv_omega,
      memRegion_split (sp - 112#64) 8 104 (by decide),
      show sp - 112#64 + 8#64 = sp - 104#64 by bv_omega,
      memRegion_split (sp - 104#64) 8 96 (by decide),
      show sp - 104#64 + 8#64 = sp - 96#64 by bv_omega,
      memRegion_split (sp - 96#64) 8 88 (by decide),
      show sp - 96#64 + 8#64 = sp - 88#64 by bv_omega,
      memRegion_split (sp - 88#64) 8 80 (by decide),
      show sp - 88#64 + 8#64 = sp - 80#64 by bv_omega,
      memRegion_split (sp - 80#64) 8 72 (by decide),
      show sp - 80#64 + 8#64 = sp - 72#64 by bv_omega,
      memRegion_split (sp - 72#64) 8 64 (by decide),
      show sp - 72#64 + 8#64 = sp - 64#64 by bv_omega,
      memRegion_split (sp - 64#64) 8 56 (by decide),
      show sp - 64#64 + 8#64 = sp - 56#64 by bv_omega,
      memRegion_split (sp - 56#64) 8 48 (by decide),
      show sp - 56#64 + 8#64 = sp - 48#64 by bv_omega,
      memRegion_split (sp - 48#64) 8 40 (by decide),
      show sp - 48#64 + 8#64 = sp - 40#64 by bv_omega,
      memRegion_split (sp - 40#64) 8 32 (by decide),
      show sp - 40#64 + 8#64 = sp - 32#64 by bv_omega,
      memRegion_split (sp - 32#64) 8 24 (by decide),
      show sp - 32#64 + 8#64 = sp - 24#64 by bv_omega,
      memRegion_split (sp - 24#64) 8 16 (by decide),
      show sp - 24#64 + 8#64 = sp - 16#64 by bv_omega,
      memRegion_split (sp - 16#64) 8 8 (by decide),
      show sp - 16#64 + 8#64 = sp - 8#64 by bv_omega,
      memRegion_8_eq_pointsTo64 (sp - 1312#64),
      memRegion_8_eq_pointsTo64 (sp - 1304#64),
      memRegion_8_eq_pointsTo64 (sp - 1296#64),
      memRegion_8_eq_pointsTo64 (sp - 1288#64),
      memRegion_8_eq_pointsTo64 (sp - 1280#64),
      memRegion_4_eq_pointsTo32 (sp - 1268#64),
      memRegion_1_eq_pointsTo8 (sp - 1240#64),
      memRegion_8_eq_pointsTo64 (sp - 1208#64),
      memRegion_8_eq_pointsTo64 (sp - 112#64),
      memRegion_8_eq_pointsTo64 (sp - 104#64),
      memRegion_8_eq_pointsTo64 (sp - 96#64),
      memRegion_8_eq_pointsTo64 (sp - 88#64),
      memRegion_8_eq_pointsTo64 (sp - 80#64),
      memRegion_8_eq_pointsTo64 (sp - 72#64),
      memRegion_8_eq_pointsTo64 (sp - 64#64),
      memRegion_8_eq_pointsTo64 (sp - 56#64),
      memRegion_8_eq_pointsTo64 (sp - 48#64),
      memRegion_8_eq_pointsTo64 (sp - 40#64),
      memRegion_8_eq_pointsTo64 (sp - 32#64),
      memRegion_8_eq_pointsTo64 (sp - 24#64),
      memRegion_8_eq_pointsTo64 (sp - 16#64),
      memRegion_8_eq_pointsTo64 (sp - 8#64)]

theorem stackAt_store_of_parts (sp : BitVec 64)
    (c_sp0 c_sp8 c_sp16 c_sp24 c_sp32 : BitVec 64) (c_sp44 : BitVec 32)
    (c_sp72 : BitVec 8) (c_sp104 : BitVec 64)
    (c_d9 c_d8 c_x29 c_x30 c_x28 c_x27 c_x26 c_x25 c_x24 c_x23 c_x22 c_x21 c_x20 c_x19 : BitVec 64) :
    (stackAt (sp - 1312#64) (storeSessionClosureStack - 1312) ∗
      ((sp - 1312#64) ↦₆₄ c_sp0) ∗
      ((sp - 1304#64) ↦₆₄ c_sp8) ∗
      ((sp - 1296#64) ↦₆₄ c_sp16) ∗
      ((sp - 1288#64) ↦₆₄ c_sp24) ∗
      ((sp - 1280#64) ↦₆₄ c_sp32) ∗
      memRegion (sp - 1272#64) 4 ∗
      ((sp - 1268#64) ↦₃₂ c_sp44) ∗
      memRegion (sp - 1264#64) 24 ∗
      ((sp - 1240#64) ↦₈ c_sp72) ∗
      memRegion (sp - 1239#64) 7 ∗
      memRegion (sp - 1232#64) 24 ∗
      ((sp - 1208#64) ↦₆₄ c_sp104) ∗
      memRegion (sp - 1200#64) 336 ∗
      memRegion (sp - 864#64) 336 ∗
      memRegion (sp - 528#64) 344 ∗
      memRegion (sp - 184#64) 24 ∗
      memRegion (sp - 160#64) 48 ∗
      ((sp - 112#64) ↦₆₄ c_d9) ∗
      ((sp - 104#64) ↦₆₄ c_d8) ∗
      ((sp - 96#64) ↦₆₄ c_x29) ∗
      ((sp - 88#64) ↦₆₄ c_x30) ∗
      ((sp - 80#64) ↦₆₄ c_x28) ∗
      ((sp - 72#64) ↦₆₄ c_x27) ∗
      ((sp - 64#64) ↦₆₄ c_x26) ∗
      ((sp - 56#64) ↦₆₄ c_x25) ∗
      ((sp - 48#64) ↦₆₄ c_x24) ∗
      ((sp - 40#64) ↦₆₄ c_x23) ∗
      ((sp - 32#64) ↦₆₄ c_x22) ∗
      ((sp - 24#64) ↦₆₄ c_x21) ∗
      ((sp - 16#64) ↦₆₄ c_x20) ∗
      ((sp - 8#64) ↦₆₄ c_x19)) ⊢
    stackAt sp storeSessionClosureStack := by
  rw [stackAt_store_eq sp]
  exact sepConj_mono_right (sepConj_mono (Entails.sepExists_intro c_sp0)
    (sepConj_mono (Entails.sepExists_intro c_sp8)
    (sepConj_mono (Entails.sepExists_intro c_sp16)
    (sepConj_mono (Entails.sepExists_intro c_sp24)
    (sepConj_mono (Entails.sepExists_intro c_sp32)
    (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro c_sp44)
    (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro c_sp72)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro c_sp104)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono (Entails.sepExists_intro c_d9)
    (sepConj_mono (Entails.sepExists_intro c_d8)
    (sepConj_mono (Entails.sepExists_intro c_x29)
    (sepConj_mono (Entails.sepExists_intro c_x30)
    (sepConj_mono (Entails.sepExists_intro c_x28)
    (sepConj_mono (Entails.sepExists_intro c_x27)
    (sepConj_mono (Entails.sepExists_intro c_x26)
    (sepConj_mono (Entails.sepExists_intro c_x25)
    (sepConj_mono (Entails.sepExists_intro c_x24)
    (sepConj_mono (Entails.sepExists_intro c_x23)
    (sepConj_mono (Entails.sepExists_intro c_x22)
    (sepConj_mono (Entails.sepExists_intro c_x21)
    (sepConj_mono (Entails.sepExists_intro c_x20)
      (Entails.sepExists_intro c_x19)))))))))))))))))))))))))))))))

theorem stackAt_store_sub_eq (sp' : BitVec 64) (n : Nat) (hn : n ≤ 18144) :
    stackAt sp' (storeSessionClosureStack - 1312) =
      memRegion (sp' - 18144#64) (18144 - n) ∗ stackAt sp' n := by
  have h1 : storeSessionClosureStack - 1312 = n + (18144 - n) := by
    change 2 ^ 14 + 3072 - 1312 = n + (18144 - n); omega
  have h2 : BitVec.ofNat 64 (n + (18144 - n)) = 18144#64 := by
    have : n + (18144 - n) = 18144 := by omega
    rw [this]
  rw [h1, ProofLib.stackAt_split_bottom sp' n (18144 - n) (by omega), h2]

theorem sret48_split_eq (sret : BitVec 64) :
    memRegion sret 48 =
      ∃∗ c0 : BitVec 64, (sret ↦₆₄ c0) ∗ memRegion (sret + 8#64) 40 := by
  rw [show (48 : Nat) = 8 + 40 from rfl,
      memRegion_split sret 8 40 (by decide),
      memRegion_8_eq_pointsTo64 sret]
  simp only [sepExists_sepConj_left]

theorem protocolAddressAt_eq_vecGhostAt_parts (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) :
    protocolAddressAt A g addr =
      vecGhostAt A g.name addr ∗ ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7 :=
  rfl

theorem vecU8_and_dev_entails_protocolAddressAt (A : RustAlloc) (sp : BitVec 64)
    (bs : List (BitVec 8)) (dev : BitVec 8) :
    (vecU8 A (sp - 1264#64) bs ∗ ((sp - 1240#64) ↦₈ dev) ∗ memRegion (sp - 1239#64) 7) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        protocolAddressAt A ⟨⟨cap, ptr, bs⟩, dev⟩ (sp - 1264#64) := by
  unfold vecU8
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e24 : sp - 1264#64 + 24#64 = sp - 1240#64 := by bv_omega
  have e25 : sp - 1264#64 + 25#64 = sp - 1239#64 := by bv_omega
  unfold protocolAddressAt vecGhostAt
  rw [e24, e25]
  exact Entails.of_eq (by ac_rfl)

theorem slot784_to_memRegion368 (sp cap : BitVec 64) (bs336 : List (BitVec 8))
    (h336 : bs336.length = 336) :
    (((sp - 528#64) ↦₆₄ cap) ∗ ((sp - 520#64) ↦ₛ bs336) ∗ memRegion (sp - 184#64) 24) ⊢
      memRegion (sp - 528#64) 368 := by
  have h344 :
      (((sp - 528#64) ↦₆₄ cap) ∗ ((sp - 520#64) ↦ₛ bs336)) ⊢ memRegion (sp - 528#64) 344 := by
    rw [show (344 : Nat) = 8 + 336 from rfl,
        memRegion_split (sp - 528#64) 8 336 (by decide),
        show sp - 528#64 + 8#64 = sp - 520#64 by bv_omega]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (h336 ▸ pointsToBytes_entails_memRegion (sp - 520#64) bs336)
  rw [show (368 : Nat) = 344 + 24 from rfl,
      memRegion_split (sp - 528#64) 344 24 (by decide),
      show sp - 528#64 + 344#64 = sp - 184#64 by bv_omega,
      ← sepConj_assoc]
  exact sepConj_mono_left h344

theorem slot80_full368_eq_bytes (sp cap : BitVec 64) (bs336 : List (BitVec 8)) :
    (((sp - 1232#64) ↦₆₄ 0#64) ∗ ((sp - 1224#64) ↦₆₄ 8#64) ∗
      ((sp - 1216#64) ↦₆₄ 0#64) ∗ ((sp - 1208#64) ↦₆₄ cap) ∗
      ((sp - 1200#64) ↦ₛ bs336)) =
    ((sp - 1232#64) ↦ₛ
      (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336))) := by
  have h := sessionRecord_full368_eq_bytes (sp - 1232#64) cap bs336
  have e1 : sp - 1232#64 + 8#64 = sp - 1224#64 := by bv_omega
  have e2 : sp - 1232#64 + 16#64 = sp - 1216#64 := by bv_omega
  have e3 : sp - 1232#64 + 24#64 = sp - 1208#64 := by bv_omega
  have e4 : sp - 1232#64 + 32#64 = sp - 1200#64 := by bv_omega
  rwa [e1, e2, e3, e4] at h

theorem slot784_full368_eq_bytes (sp cap : BitVec 64) (bs336 : List (BitVec 8)) :
    (((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗
      ((sp - 512#64) ↦₆₄ 0#64) ∗ ((sp - 504#64) ↦₆₄ cap) ∗
      ((sp - 496#64) ↦ₛ bs336)) =
    ((sp - 528#64) ↦ₛ
      (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336))) := by
  have h := sessionRecord_full368_eq_bytes (sp - 528#64) cap bs336
  have e1 : sp - 528#64 + 8#64 = sp - 520#64 := by bv_omega
  have e2 : sp - 528#64 + 16#64 = sp - 512#64 := by bv_omega
  have e3 : sp - 528#64 + 24#64 = sp - 504#64 := by bv_omega
  have e4 : sp - 528#64 + 32#64 = sp - 496#64 := by bv_omega
  rwa [e1, e2, e3, e4] at h

theorem bucket_full368_eq_bytes (ctrl : BitVec 64) (k : Nat) (cap : BitVec 64) (bs336 : List (BitVec 8)) :
    (((bucketAddr ctrl 400 k + 32#64) ↦₆₄ 0#64) ∗ ((bucketAddr ctrl 400 k + 40#64) ↦₆₄ 8#64) ∗
      ((bucketAddr ctrl 400 k + 48#64) ↦₆₄ 0#64) ∗ ((bucketAddr ctrl 400 k + 56#64) ↦₆₄ cap) ∗
      ((bucketAddr ctrl 400 k + 64#64) ↦ₛ bs336)) =
    ((bucketAddr ctrl 400 k + 32#64) ↦ₛ
      (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 cap ++ bs336))) := by
  have h := sessionRecord_full368_eq_bytes (bucketAddr ctrl 400 k + 32#64) cap bs336
  obtain ⟨e1, e2, e3, _⟩ := bucket_rec_off_eqs ctrl k
  have e4' : bucketAddr ctrl 400 k + 32#64 + 32#64 = bucketAddr ctrl 400 k + 64#64 := by bv_omega
  rwa [e1, e2, e3, e4'] at h

theorem slot80_restore_regions (sp : BitVec 64) (bs368 : List (BitVec 8)) (h368 : bs368.length = 368) :
    ((sp - 1232#64) ↦ₛ bs368) ⊢
      ∃∗ c104 : BitVec 64,
        memRegion (sp - 1232#64) 24 ∗ ((sp - 1208#64) ↦₆₄ c104) ∗ memRegion (sp - 1200#64) 336 := by
  have h1 := h368 ▸ pointsToBytes_entails_memRegion (sp - 1232#64) bs368
  refine Entails.trans h1 ?_
  rw [show (368 : Nat) = 24 + 344 from rfl,
      memRegion_split (sp - 1232#64) 24 344 (by decide),
      show sp - 1232#64 + 24#64 = sp - 1208#64 by bv_omega,
      show (344 : Nat) = 8 + 336 from rfl,
      memRegion_split (sp - 1208#64) 8 336 (by decide),
      show sp - 1208#64 + 8#64 = sp - 1200#64 by bv_omega,
      memRegion_8_eq_pointsTo64 (sp - 1208#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem slot784_dropped_restore_regions (sp : BitVec 64) :
    (((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗
      ((sp - 512#64) ↦₆₄ 0#64) ∗ memRegion (sp - 504#64) 344) ⊢
    memRegion (sp - 528#64) 344 ∗ memRegion (sp - 184#64) 24 := by
  have h24 :
      (((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗ ((sp - 512#64) ↦₆₄ 0#64)) ⊢
      memRegion (sp - 528#64) 24 := by
    rw [show (24 : Nat) = 8 + 16 from rfl,
        memRegion_split (sp - 528#64) 8 16 (by decide),
        show sp - 528#64 + 8#64 = sp - 520#64 by bv_omega,
        show (16 : Nat) = 8 + 8 from rfl,
        memRegion_split (sp - 520#64) 8 8 (by decide),
        show sp - 520#64 + 8#64 = sp - 512#64 by bv_omega]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have h368 :
      (((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗
        ((sp - 512#64) ↦₆₄ 0#64) ∗ memRegion (sp - 504#64) 344) ⊢
      memRegion (sp - 528#64) 368 := by
    have hassoc :
        (((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗
          ((sp - 512#64) ↦₆₄ 0#64) ∗ memRegion (sp - 504#64) 344) =
        ((((sp - 528#64) ↦₆₄ 0#64) ∗ ((sp - 520#64) ↦₆₄ 8#64) ∗
          ((sp - 512#64) ↦₆₄ 0#64)) ∗ memRegion (sp - 504#64) 344) := by ac_rfl
    rw [hassoc, show (368 : Nat) = 24 + 344 from rfl,
        memRegion_split (sp - 528#64) 24 344 (by decide),
        show sp - 528#64 + 24#64 = sp - 504#64 by bv_omega]
    exact sepConj_mono_left h24
  refine Entails.trans h368 ?_
  rw [show (368 : Nat) = 344 + 24 from rfl,
      memRegion_split (sp - 528#64) 344 24 (by decide),
      show sp - 528#64 + 344#64 = sp - 184#64 by bv_omega]
  exact Entails.refl _

theorem addrClone_to_dealloc_parts (A : RustAlloc) (sp : BitVec 64) (g : AddrGhost)
    (hlen36 : g.name.bytes.length = 36) :
    (((sp - 1256#64) ↦₆₄ g.name.ptr) ∗ ((sp - 1248#64) ↦₆₄ 36#64) ∗
      ((sp - 1240#64) ↦₈ g.device) ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
      addrRestAt A g (sp - 1264#64)) ⊢
    ⌜g.name.cap ≠ 0#64⌝ ∗
      ((sp - 1264#64) ↦₆₄ g.name.cap) ∗
      ((sp - 1256#64) ↦₆₄ g.name.ptr) ∗
      ((sp - 1248#64) ↦₆₄ 36#64) ∗
      ((sp - 1240#64) ↦₈ g.device) ∗
      memRegion (sp - 1239#64) 7 ∗
      A.live g.name.ptr g.name.cap.toNat 1 ∗
      memRegion g.name.ptr g.name.cap.toNat := by
  unfold addrRestAt
  rw [show sp - 1264#64 + 25#64 = sp - 1239#64 by bv_omega]
  have h1 :
      (((sp - 1256#64) ↦₆₄ g.name.ptr) ∗ ((sp - 1248#64) ↦₆₄ 36#64) ∗
        ((sp - 1240#64) ↦₈ g.device) ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          ((sp - 1264#64) ↦₆₄ g.name.cap) ∗
          A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length) ∗
          memRegion (sp - 1239#64) 7)) =
      (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (((sp - 1264#64) ↦₆₄ g.name.cap) ∗
          ((sp - 1256#64) ↦₆₄ g.name.ptr) ∗
          ((sp - 1248#64) ↦₆₄ 36#64) ∗
          ((sp - 1240#64) ↦₈ g.device) ∗
          memRegion (sp - 1239#64) 7 ∗
          A.live g.name.ptr g.name.cap.toNat 1 ∗
          ((g.name.ptr ↦ₛ g.name.bytes) ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)))) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; rintro ⟨hlen_le, _, _⟩
  have hcap_ne : g.name.cap ≠ 0#64 := by
    intro h0; rw [h0] at hlen_le; change g.name.bytes.length ≤ 0 at hlen_le; omega
  apply Entails.pure_right hcap_ne
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  have hsplit : g.name.cap.toNat = g.name.bytes.length + (g.name.cap.toNat - g.name.bytes.length) := by omega
  conv_rhs =>
    rw [hsplit, memRegion_split g.name.ptr g.name.bytes.length (g.name.cap.toNat - g.name.bytes.length) (by omega)]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion g.name.ptr g.name.bytes)

theorem slot48_restore_region24 (sp v48 v56 v64 : BitVec 64) :
    (((sp - 1264#64) ↦₆₄ v48) ∗ ((sp - 1256#64) ↦₆₄ v56) ∗ ((sp - 1248#64) ↦₆₄ v64)) ⊢
      memRegion (sp - 1264#64) 24 := by
  rw [show (24 : Nat) = 8 + 16 from rfl,
      memRegion_split (sp - 1264#64) 8 16 (by decide),
      show sp - 1264#64 + 8#64 = sp - 1256#64 by bv_omega,
      show (16 : Nat) = 8 + 8 from rfl,
      memRegion_split (sp - 1256#64) 8 8 (by decide),
      show sp - 1256#64 + 8#64 = sp - 1248#64 by bv_omega]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem wpp_call_stringClone {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (p out sp' : BitVec 64) (g : VecGhost)
    (hcall : subroutine_ok prog entry (stringCloneSpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = p) (hx8 : s.readReg64 .x8 = out)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' HashbrownBin.extHookStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWPp prog ret sf
        ((vecGhostAt A g p ∗ vecU8 A out g.bytes ∗ A.pool ∗ stackAt sp' HashbrownBin.extHookStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := (p, out, g))
    (φ := s.readReg64 .x0 = p ∧ s.readReg64 .x8 = out)
    (T := vecGhostAt A g p ∗ memRegion out 24 ∗ A.pool ∗ stackAt sp' HashbrownBin.extHookStack)
    hcall hpc hrun hsp hlr
    (by dsimp only [stringCloneSpec]; rw [hsp_eq])
    ⟨hx0, hx8⟩ hP
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ h => Satisfies.mono (sepConj_mono_left
      (allocPanic_frame_of_trace_eq (p, out, g) s0 s sf F htr)) h)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [stringCloneSpec]
  rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun htr_f => ?_
  simp only [sepConj_assoc] at hnext ⊢
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf (htr_f.trans htr)

theorem wpp_call_reserveRehash {prog : Program} {entry ret_pc ret : BitVec 64}
    {A : RustAlloc} {s0 s : Arm64.State} {P F : SepProp}
    {Q : Arm64.State → SepProp → Prop} {Fr : SepProp}
    (base mp rsPtr k0 k1 sp' : BitVec 64)
    (hcall : subroutine_ok prog entry (reserveRehashSessionEmptySpec A))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hx0 : s.readReg64 .x0 = mp) (hx1 : s.readReg64 .x1 = 1#64)
    (hx2 : s.readReg64 .x2 = rsPtr) (hx3 : s.readReg64 .x3 = 1#64)
    (hsp_eq : s.sp = sp') (htr : s.trace = s0.trace)
    (hP : P = (emptyTableAt base mp k0 k1 ∗ A.pool ∗ stackAt sp' reserveRehashStack) ∗ F)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp' → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0xffffffffffffffff#64 → sf.trace = s0.trace →
      SepWPp prog ret sf
        ((table4EmptyAt A sessionBucketStride mp k0 k1 ∗ A.pool ∗ stackAt sp' reserveRehashStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.call_frame (x := ⟨base, mp, rsPtr, k0, k1⟩)
    (φ := s.readReg64 .x0 = mp ∧ s.readReg64 .x1 = 1#64 ∧ s.readReg64 .x2 = rsPtr ∧ s.readReg64 .x3 = 1#64)
    (T := emptyTableAt base mp k0 k1 ∗ A.pool ∗ stackAt sp' reserveRehashStack)
    hcall hpc hrun hsp hlr
    (by dsimp only [reserveRehashSessionEmptySpec, reserveRehashEmptySpec]; rw [hsp_eq])
    ⟨hx0, hx1, hx2, hx3⟩ hP
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf _ h => Satisfies.mono (sepConj_mono_left
      (allocPanic_frame_of_trace_eq (⟨base, mp, rsPtr, k0, k1⟩ : ReserveRehashEmptyGhost) s0 s sf F htr)) h)
    fun sf hpcf hrunf hspf hcsf => ?_
  dsimp only [reserveRehashSessionEmptySpec, reserveRehashEmptySpec]
  rw [hsp_eq, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_f, htr_f⟩ => ?_
  simp only [sepConj_assoc] at hnext ⊢
  exact hnext sf hpcf hrunf (hspf.trans hsp_eq) hcsf hx0_f (htr_f.trans htr)

attribute [local irreducible] CanonSession

theorem pollUnitResultAt_of_parts (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ memRegion (sret + 8#64) 40) ⊢
      pollUnitResultAt sret :=
  Entails.refl _

theorem sessionRecordAt_some_any_prev_of_parts (A : RustAlloc) (r prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) :
    ((r ↦₆₄ prevCap) ∗ ((r + 8#64) ↦₆₄ prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
      vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] ∗
      sessionStateReprAt A (r + 24#64) G ss) ⊢
    sessionRecordAt A r ⟨prevCap, prevPtr, some G⟩ ⟨some ss⟩ := by
  rw [sessionRecordAt_some_any_prev_eq]
  exact Entails.refl _

theorem bucket_entry_of_full368_bytes (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (recG : SessionGhost) (ss : Session (List (BitVec 8)))
    (hcanon : CanonSession recG ss)
    (bs336 : List (BitVec 8))
    (hinl : SessionInline recG ss.state (unpack64 recG.localIk.cap ++ bs336)) :
    (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
      ((bucketAddr ctrl 400 k + 32#64) ↦ₛ
        (unpack64 0#64 ++ (unpack64 8#64 ++ unpack64 0#64 ++ unpack64 recG.localIk.cap ++ bs336))) ∗
      sessionAtHeap A recG ss) ⊢
    sessionBucketEntryAt A peerG recG ss (bucketAddr ctrl 400 k) := by
  rw [← bucket_full368_eq_bytes ctrl k recG.localIk.cap bs336]
  obtain ⟨_, _, _, hoff64⟩ := bucket_rec_off_eqs ctrl k
  rw [← hoff64]
  have h1 :
      (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
        (((bucketAddr ctrl 400 k + 32#64) ↦₆₄ 0#64) ∗
          ((bucketAddr ctrl 400 k + 40#64) ↦₆₄ 8#64) ∗
          ((bucketAddr ctrl 400 k + 48#64) ↦₆₄ 0#64) ∗
          ((bucketAddr ctrl 400 k + 56#64) ↦₆₄ recG.localIk.cap) ∗
          ((bucketAddr ctrl 400 k + 56#64 + 8#64) ↦ₛ bs336)) ∗
        sessionAtHeap A recG ss) =
      (protocolAddressAt A peerG (bucketAddr ctrl 400 k) ∗
        ((bucketAddr ctrl 400 k + 32#64) ↦₆₄ 0#64) ∗
        ((bucketAddr ctrl 400 k + 40#64) ↦₆₄ 8#64) ∗
        ((bucketAddr ctrl 400 k + 48#64) ↦₆₄ 0#64) ∗
        (((bucketAddr ctrl 400 k + 56#64) ↦₆₄ recG.localIk.cap) ∗
          ((bucketAddr ctrl 400 k + 56#64 + 8#64) ↦ₛ bs336) ∗
          sessionAtHeap A recG ss)) := by ac_rfl
  rw [h1]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sessionAt_pack_head_tail A (bucketAddr ctrl 400 k + 56#64) recG ss hinl))))) ?_
  exact bucket_entry_of_parts A ctrl k peerG recG ss hcanon

end CryptoVerification.E2E.InMem.HashbrownBin.SessionStoreFutures
