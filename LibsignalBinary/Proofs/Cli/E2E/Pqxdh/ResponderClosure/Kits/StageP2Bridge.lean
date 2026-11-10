/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5Defs

/-!
# Stage P2 Definitions and Arm 4–6 Bridge Helpers

Defines `stageP2V1CallStack`, `opkOkSkBytes?`, `mkP2AcceptKeysInput`, and spatial framing helpers
for Stage P2 Error Arms 1–6 (`p2ErrFrameAt`) and Substage P2.5/P2.6 boundaries.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_pointsToBytes_split_head (p : BitVec 64) (bs : List (BitVec 8)) (h : 0 < bs.length) :
    (p ↦ₛ bs) = (p ↦₈ bs.getD 0 0#8) ∗ ((p + 1#64) ↦ₛ bs.drop 1) := by
  cases bs with
  | nil => cases h
  | cons b tl =>
    change (p ↦ₛ ([b] ++ tl)) = (p ↦₈ b) ∗ ((p + 1#64) ↦ₛ tl)
    rw [pointsToBytes_append]
    simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton]

theorem p2_cells8_a90_to_cells6_2 (sp : BitVec 64) :
    cells (sp + 0xa90#64) 8 = cells (sp + 0xa90#64) 6 ∗ cells (sp + 0xac0#64) 2 := by
  rw [← ProofLib.memRegion_cells (sp + 0xa90#64) 8 (by decide),
      ← ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide),
      ← ProofLib.memRegion_cells (sp + 0xac0#64) 2 (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 48) (k := 16)
        (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]

theorem p2_a90_err123_to_288 (sp : BitVec 64) :
    cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗ memRegion (sp + 0xad1#64) 223 =
      memRegion (sp + 0xa90#64) 288 := by
  rw [← ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide),
      ← sepConj_assoc,
      ← ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 48) (k := 17)
          (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ← p2_memRegion_a90_288_split_65_223 sp]

theorem p2_a90_err45_to_288 (sp : BitVec 64) :
    cells (sp + 0xa90#64) 6 ∗ cells (sp + 0xac0#64) 2 ∗
      memRegion (sp + 0xad0#64) 1 ∗ memRegion (sp + 0xad1#64) 223 =
      memRegion (sp + 0xa90#64) 288 := by
  rw [← sepConj_assoc, ← p2_cells8_a90_to_cells6_2 sp,
      ← sepConj_assoc, ← p2_memRegion_a90_65_eq_cells8_1 sp,
      ← p2_memRegion_a90_288_split_65_223 sp]

theorem p2_a90_cells8_1_223_eq_288 (sp : BitVec 64) :
    cells (sp + 0xa90#64) 8 ∗ memRegion (sp + 0xad0#64) 1 ∗ memRegion (sp + 0xad1#64) 223 =
      memRegion (sp + 0xa90#64) 288 := by
  rw [← sepConj_assoc, ← p2_memRegion_a90_65_eq_cells8_1 sp,
      ← p2_memRegion_a90_288_split_65_223 sp]

theorem p2_memRegion_a90_288_to_cells6_240 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 288 =
      cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 240 := by
  rw [← ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide),
      ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 48) (k := 240)
        (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide)]

theorem p2_coro4f8_2cells_328_eq_344 (coroPtr : BitVec 64) :
    cells (coroPtr + 0x4f8#64) 2 ∗ memRegion (coroPtr + 0x508#64) 328 =
      memRegion (coroPtr + 0x4f8#64) 344 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x4f8#64) 2 (by decide),
      ← ProofLib.memRegion_split' (b := coroPtr + 0x4f8#64) (n := 16) (k := 328)
          (b' := coroPtr + 0x508#64) rfl (by bv_omega) (by decide)]

theorem p2BobSessRegIdsV1_length (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) (rId lId : BitVec 32) :
    (p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 rId lId).length
      = 344 := by
  unfold p2BobSessRegIdsV1
  rw [List.length_append, p2BobSessHead56Bv8_length, List.length_append,
      p2BobSessMid280V1_length, List.length_append, unpack32_length, unpack32_length]

theorem p2BobSession344Bv8V1_eq_regIds_zero (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    p2BobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 0#32 0#32 := by
  rw [p2BobSession344Bv8V1_eq_head56_mid280V1]
  have h0 : unpack64 0#64 = unpack32 0#32 ++ unpack32 0#32 := by decide
  rw [h0]
  rfl

theorem p2BobSession344Bv8V1_length (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (p2BobSession344Bv8V1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length
      = 344 := by
  rw [p2BobSession344Bv8V1_eq_regIds_zero]
  exact p2BobSessRegIdsV1_length p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
    0#32 0#32

theorem p2_memRegion_e0_368_split_24_344 (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0xe0#64) 368 =
      memRegion (coroPtr + 0xe0#64) 24 ∗ memRegion (coroPtr + 0xf8#64) 344 :=
  ProofLib.memRegion_split' (b := coroPtr + 0xe0#64) (n := 24) (k := 344)
    (b' := coroPtr + 0xf8#64) rfl (by bv_omega) (by decide)

/-- Full Stage P2 stack bound at SPQR V1 (`stageP2CallStack` plus `initialize_bob_session` V1 stack). -/
def stageP2V1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2CallStack spkKit kpkKit pkKit skit) (stageP2bStack + 0x700)

theorem p2_callStack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2CallStack spkKit kpkKit pkKit skit ≤
      stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_bobStack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2bStack + 0x700 ≤ stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_sub56Stack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack skit ≤ stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit)
    (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit)

theorem p2_pureStack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack ≤ stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure_le_stageP2 spkKit kpkKit pkKit skit)
    (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit)

theorem p2_allocHookStack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    allocHookStack ≤ stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit)
    (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit)

theorem p2_dropSs3Stack_le_v1CallStack {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    dropSessionStructureLocal2Stack ≤ stageP2V1CallStack spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_dropSs3Stack_le_stageP2 spkKit kpkKit pkKit skit)
    (p2_callStack_le_v1CallStack spkKit kpkKit pkKit skit)

/-- Full Stage P2 stack bound at SPQR V1 under 4K `memcpy` and 16K PQXDH/blackBox hooks. -/
def stageP2V1CallStack4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) : Nat :=
  max (stageP2CallStack4K spkKit kpkKit pkKit skit) (768 + Initiator.pqxdhEntryStackExt)

abbrev stageP2V1CallStackExt := @stageP2V1CallStack4K

theorem p2_callStack4K_le_v1CallStack4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2CallStack4K spkKit kpkKit pkKit skit ≤
      stageP2V1CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_max_left _ _

theorem p2_bobStack4K_le_v1CallStack4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    768 + Initiator.pqxdhEntryStackExt ≤ stageP2V1CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_max_right _ _

theorem p2_sub56Stack4K_le_v1CallStack4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2Sub56Stack4K skit ≤ stageP2V1CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_sub56_4K_le_stageP2_4K spkKit kpkKit pkKit skit)
    (p2_callStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit)

theorem p2_pureStack4K_le_v1CallStack4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2PureAndErrStack4K ≤ stageP2V1CallStack4K spkKit kpkKit pkKit skit :=
  Nat.le_trans (p2_pure4K_le_stageP2_4K spkKit kpkKit pkKit skit)
    (p2_callStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit)

theorem p2_v1CallStack_le_4K {A : RustAlloc} {b : BitVec 64}
    (spkKit : SignedPreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) :
    stageP2V1CallStack spkKit kpkKit pkKit skit ≤
      stageP2V1CallStack4K spkKit kpkKit pkKit skit :=
  Nat.max_le.mpr
    ⟨Nat.le_trans (p2_callStack_le_4K spkKit kpkKit pkKit skit)
      (p2_callStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit),
     Nat.le_trans (Nat.le_trans p2_stageP2bV1_le_pure p2_pure_le_pure4K)
      (p2_pureStack4K_le_v1CallStack4K spkKit kpkKit pkKit skit)⟩

theorem p2_memRegion_3c8_8_split_7_1 (sp : BitVec 64) :
    memRegion (sp + 0x3c8#64) 8 =
      memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3cf#64) 1 :=
  ProofLib.memRegion_split' (b := sp + 0x3c8#64) (n := 7) (k := 1)
    (b' := sp + 0x3cf#64) rfl (by bv_omega) (by decide)

theorem p2_pqsk_split_rejoin (p : BitVec 64) (bs : List (BitVec 8)) (h : 0 < bs.length) :
    (p ↦₈ bs.getD 0 0#8) ∗ ((p + 1#64) ↦ₛ bs.drop 1) = (p ↦ₛ bs) :=
  (p2_pointsToBytes_split_head p bs h).symm

/-- Convert wire `hdr.opkId? : Option UInt32` to `Option (BitVec 32)` for store-kit specs. -/
def hdrOpkIdBv? (hdr : HandshakeHdr) : Option (BitVec 32) :=
  hdr.opkId?.map UInt32.toBitVec

theorem hdrOpkIdBv?_isSome (hdr : HandshakeHdr) :
    (hdrOpkIdBv? hdr).isSome = hdr.opkId?.isSome := by
  unfold hdrOpkIdBv?
  cases hdr.opkId? <;> rfl

theorem hdrOpkIdBv?_of_some {hdr : HandshakeHdr} {u : UInt32} (h : hdr.opkId? = some u) :
    hdrOpkIdBv? hdr = some u.toBitVec := by
  simp [hdrOpkIdBv?, h]

theorem hdrOpkIdBv?_of_none {hdr : HandshakeHdr} (h : hdr.opkId? = none) :
    hdrOpkIdBv? hdr = none := by
  simp [hdrOpkIdBv?, h]

/-- Optional OPK secret-key bytes for `AcceptKeysInput` (`some (toU8 opkSkBytes)` when `opkId?`
is `some _`, `none` when `none`). -/
def opkOkSkBytes? : Option (BitVec 32) → List (BitVec 8) → Option SignalPqxdh.Bytes
  | some _, skB => some (toU8 skB)
  | none, _ => none

theorem opkOptTag8_eq_opkPresentTag (opkId? : Option (BitVec 32)) (skB : List (BitVec 8)) :
    opkOptTag8 opkId? = opkPresentTag (opkOkSkBytes? opkId? skB) := by
  cases opkId? <;> rfl

theorem opkOptTag32_eq_opkIdIsSomeWord (opkId? : Option (BitVec 32)) (skB : List (BitVec 8)) :
    opkOptTag32 opkId? = opkIdIsSomeWord (opkOkSkBytes? opkId? skB) := by
  cases opkId? <;> rfl

theorem opkOkSkBytes?_isSome (opkId? : Option (BitVec 32)) (skB : List (BitVec 8)) :
    opkId?.isSome = (opkOkSkBytes? opkId? skB).isSome := by
  cases opkId? <;> rfl

theorem hdr_opkId?_isSome_eq_opkOkSkBytes? (hdr : HandshakeHdr) (skB : List (BitVec 8)) :
    hdr.opkId?.isSome = (opkOkSkBytes? (hdrOpkIdBv? hdr) skB).isSome := by
  rw [← hdrOpkIdBv?_isSome hdr, opkOkSkBytes?_isSome]

theorem opkOkSkBytes?_eq_of_some {opkId? : Option (BitVec 32)} {skB : List (BitVec 8)}
    {opkSk : SignalPqxdh.Bytes} (h : opkOkSkBytes? opkId? skB = some opkSk) :
    skB = bytesToBv8 opkSk := by
  cases opkId? with
  | none => cases h
  | some _ =>
    cases h
    exact (bytesToBv8_toU8 skB).symm

/-- Construct `AcceptKeysInput` from wire `HandshakeHdr`, Bob's 32-byte identity keypair bytes
`(ikBSk, ikBPk)`, and the store-resolved SPK, Kyber1024, and optional OPK key bytes. -/
def mkP2AcceptKeysInput (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)) :
    AcceptKeysInput where
  ikBSk := ikBSk
  ikBPk := ikBPk
  spkBSk := toU8 (clampBv8List spkPrivBytes)
  spkBPk := toU8 spkPubBytes
  opkBSk? := opkOkSkBytes? (hdrOpkIdBv? hdr) opkSkBytes
  pqspkBSk := toU8 kyberPrivBytes
  pqspkBPk := toU8 kyberPubBytes
  trustedPeer := true
  replayOk := true
  hdr := hdr

theorem wellSized_mkP2AcceptKeysInput {hdr : HandshakeHdr} {ikBSk ikBPk : SignalPqxdh.Bytes}
    {spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkSkBytes : List (BitVec 8)}
    (hikBSk : ikBSk.length = 32) (hikBPk : ikBPk.length = 32)
    (hspkPub : spkPubBytes.length = 32) (hspkPriv : spkPrivBytes.length = 32)
    (hkyberPub : kyberPubBytes.length = 1568) (hkyberPriv : kyberPrivBytes.length = 3168)
    (hopkSk : opkSkBytes.length = 32)
    (hikAPk : hdr.ikAPk.length = 32) (hekAPk : hdr.ekAPk.length = 32)
    (hkemCt : hdr.kemCt.length = 1568) :
    WellSizedAcceptKeysInput
      (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes) := by
  refine ⟨hikBSk, hikBPk, ?_, ?_, ?_, ?_, ?_, hikAPk, hekAPk, hkemCt⟩
  · simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv]
  · simp [mkP2AcceptKeysInput, toU8, hspkPub]
  · intro sk hsk
    cases hop : hdrOpkIdBv? hdr with
    | none => simp [mkP2AcceptKeysInput, opkOkSkBytes?, hop] at hsk
    | some _ =>
      simp only [mkP2AcceptKeysInput, opkOkSkBytes?, hop, Option.some.injEq] at hsk
      subst hsk
      simp [toU8, hopkSk]
  · simp [mkP2AcceptKeysInput, toU8, hkyberPriv]
  · simp [mkP2AcceptKeysInput, toU8, hkyberPub]

theorem p2_bobParamsFieldsAt_err_weaken (coroPtr msgPtr skBuf ctBufPtr : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (hwell : WellSizedAcceptKeysInput inp) :
    bobParamsFieldsAt (coroPtr + 0x658#64) skBuf (msgPtr + 0x90#64) ctBufPtr
      (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ⊢
      ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
      memRegion skBuf 3168 ∗
      ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
      ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
      ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
      ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
      ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
      ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
      (ctBufPtr ↦₈ 8#8) ∗
      ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
      ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
      ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
      ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
      ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
  rw [← bobParamsFieldsAt_intro coroPtr msgPtr skBuf ctBufPtr inp ikBPk spkBPk]
  have hlen : (bytesToBv8 inp.pqspkBSk).length = 3168 := by
    simp [bytesToBv8, hwell.2.2.2.2.2.1]
  have hm := p2_pointsToBytes_entails_memRegion skBuf (bytesToBv8 inp.pqspkBSk) 3168 hlen
  rw [← p2_pqsk_split_rejoin skBuf (bytesToBv8 inp.pqspkBSk) (by omega)] at hm
  exact p2_entails_frame_v1 hm (by sep_focus) (Entails.of_eq (by ac_rfl))

theorem p2_sp3e0_arm4_to_368 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 72 ∗ memRegion (sp + 0x428#64) 272 ∗
      memRegion (sp + 0x538#64) 24 = memRegion (sp + 0x3e0#64) 368 := by
  rw [← sepConj_assoc,
      ← ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 72) (k := 272)
          (b' := sp + 0x428#64) rfl (by bv_omega) (by decide),
      ← p2_memRegion_3e0_split_344_24 sp]

theorem p2_bobSessRegIdsV1_entails_memRegion344 (p : BitVec 64)
    (p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) (rId lId : BitVec 32) :
    (p ↦ₛ p2BobSessRegIdsV1 p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 rId lId) ⊢
      memRegion p 344 :=
  p2_pointsToBytes_entails_memRegion p _ 344
    (p2BobSessRegIdsV1_length p1 p2 p3 p4 c5 p5 l5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 rId lId)

theorem p2_speWordsAt_entails_memRegion48 (p w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt p w0 w1 w2 w3 w4 w5 ⊢ memRegion p 48 := by
  dsimp only [speWordsAt]
  have h1 := sepConj_mono (pointsTo64_entails_memRegion p w0)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 8#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 16#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 24#64) w3)
    (sepConj_mono (pointsTo64_entails_memRegion (p + 32#64) w4)
      (pointsTo64_entails_memRegion (p + 40#64) w5)))))
  have hm :
      memRegion p 8 ∗ (memRegion (p + 8#64) 8 ∗ (memRegion (p + 16#64) 8 ∗
      (memRegion (p + 24#64) 8 ∗ (memRegion (p + 32#64) 8 ∗ memRegion (p + 40#64) 8)))) =
      memRegion p 48 := by
    rw [(ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 8)
          (b' := p + 40#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := p + 24#64) (n := 8) (k := 16)
          (b' := p + 32#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 24)
          (b' := p + 24#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 32)
          (b' := p + 16#64) rfl (by bv_omega) (by decide)).symm,
        (ProofLib.memRegion_split' (b := p) (n := 8) (k := 40)
          (b' := p + 8#64) rfl (by bv_omega) (by decide)).symm]
  exact hm ▸ h1

theorem p2_sp3e0_arm5_to_368 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      speWordsAt (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
      memRegion (sp + 0x418#64) 288 ∗ memRegion (sp + 0x538#64) 24 ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  have h1 := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x3e0#64) 0xffffffffffffffff#64)
    (sepConj_mono (p2_speWordsAt_entails_memRegion48 (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5)
      (Entails.refl (memRegion (sp + 0x418#64) 288 ∗ memRegion (sp + 0x538#64) 24)))
  have hm :
      memRegion (sp + 0x3e0#64) 8 ∗ (memRegion (sp + 0x3e8#64) 48 ∗
      (memRegion (sp + 0x418#64) 288 ∗ memRegion (sp + 0x538#64) 24)) =
      memRegion (sp + 0x3e0#64) 368 := by
    rw [← ProofLib.memRegion_split' (b := sp + 0x418#64) (n := 288) (k := 24)
          (b' := sp + 0x538#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 48) (k := 312)
          (b' := sp + 0x418#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 360)
          (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide)]
  exact hm ▸ h1

theorem p2_sp3e0_arm6_to_368 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt (sp + 0x3e0#64) w0 w1 w2 w3 w4 w5 ∗
      memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24 ⊢
      memRegion (sp + 0x3e0#64) 368 := by
  have h1 := sepConj_mono (p2_speWordsAt_entails_memRegion48 (sp + 0x3e0#64) w0 w1 w2 w3 w4 w5)
    (Entails.refl (memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24))
  have hm :
      memRegion (sp + 0x3e0#64) 48 ∗
      (memRegion (sp + 0x410#64) 296 ∗ memRegion (sp + 0x538#64) 24) =
      memRegion (sp + 0x3e0#64) 368 := by
    rw [← ProofLib.memRegion_split' (b := sp + 0x410#64) (n := 296) (k := 24)
          (b' := sp + 0x538#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 320)
          (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)]
  exact hm ▸ h1

theorem p2_ctBuf_split (ctBufPtr : BitVec 64) (kemCtBv8 : List (BitVec 8))
    (h : 0 < kemCtBv8.length) :
    (ctBufPtr ↦ₛ (8#8 :: kemCtBv8)) =
      (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr + 1#64) ↦₈ kemCtBv8.getD 0 0#8) ∗
        ((ctBufPtr + 2#64) ↦ₛ kemCtBv8.drop 1) := by
  change (ctBufPtr ↦ₛ ([8#8] ++ kemCtBv8)) = _
  rw [pointsToBytes_append]
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton]
  rw [p2_pointsToBytes_split_head (ctBufPtr + 1#64) kemCtBv8 h]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem p2_coro658_298_rejoin (coroPtr msgPtr pkBuf skBuf : BitVec 64)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes) (opkPkBytes opkSkBytes : List (BitVec 8))
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk : ikBPk.length = 32) (hspkBPk : spkBPk.length = 32)
    (hopkPk : opkPkBytes.length = 32) (hopkSk : opkSkBytes.length = 32)
    (hopk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) :
    ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
      ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
      ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
      ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
      ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
      ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
      ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
      ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
      opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
      opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
      ((coroPtr + 0x781#64) ↦₈ 0#8) ⊢
      memRegion (coroPtr + 0x658#64) 298 := by
  have hopk_rejoin :
      opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
        opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes =
      ((coroPtr + 0x761#64) ↦ₛ opkSkBytes) :=
    (opkSlot65_eq_optField (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes hopk_eq).symm
  rw [← sepConj_assoc (opkOptFieldAt _ _) (opkUnusedFieldAt _ _ _), hopk_rejoin]
  have h1 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x658#64) (bytesToBv8 ikBPk) 32
    (by simp [bytesToBv8, hikBPk])
  have h2 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x678#64) (bytesToBv8 inp.ikBSk) 32
    (by simp [bytesToBv8, hwell.1])
  have h3 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x698#64) (bytesToBv8 spkBPk) 32
    (by simp [bytesToBv8, hspkBPk])
  have h4 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x6b8#64) (bytesToBv8 inp.spkBSk) 32
    (by simp [bytesToBv8, hwell.2.2.1])
  have h5 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x6d8#64) (bytesToBv8 inp.hdr.ikAPk) 32
    (by simp [bytesToBv8, hwell.2.2.2.2.2.2.2.1])
  have h6 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x6f8#64) (bytesToBv8 inp.hdr.ekAPk) 32
    (by simp [bytesToBv8, hwell.2.2.2.2.2.2.2.2.1])
  have h7 := pointsTo64_entails_memRegion (coroPtr + 0x718#64) pkBuf
  have h8 := pointsTo64_entails_memRegion (coroPtr + 0x720#64) 0x620#64
  have h9 := pointsTo64_entails_memRegion (coroPtr + 0x728#64) skBuf
  have h10 := pointsTo64_entails_memRegion (coroPtr + 0x730#64) 0xc60#64
  have h11 := pointsTo64_entails_memRegion (coroPtr + 0x738#64) (msgPtr + 0x90#64)
  have h12 := pointsTo8_entails_memRegion (coroPtr + 0x740#64) (opkPresentTag inp.opkBSk?)
  have h13 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x741#64) opkPkBytes 32 hopkPk
  have h14 := p2_pointsToBytes_entails_memRegion (coroPtr + 0x761#64) opkSkBytes 32 hopkSk
  have h15 := pointsTo8_entails_memRegion (coroPtr + 0x781#64) 0#8
  have hm := sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4
    (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7 (sepConj_mono h8
    (sepConj_mono h9 (sepConj_mono h10 (sepConj_mono h11 (sepConj_mono h12
    (sepConj_mono h13 (sepConj_mono h14 h15)))))))))))))
  have heq :
      memRegion (coroPtr + 0x658#64) 32 ∗ (memRegion (coroPtr + 0x678#64) 32 ∗
      (memRegion (coroPtr + 0x698#64) 32 ∗ (memRegion (coroPtr + 0x6b8#64) 32 ∗
      (memRegion (coroPtr + 0x6d8#64) 32 ∗ (memRegion (coroPtr + 0x6f8#64) 32 ∗
      (memRegion (coroPtr + 0x718#64) 8 ∗ (memRegion (coroPtr + 0x720#64) 8 ∗
      (memRegion (coroPtr + 0x728#64) 8 ∗ (memRegion (coroPtr + 0x730#64) 8 ∗
      (memRegion (coroPtr + 0x738#64) 8 ∗ (memRegion (coroPtr + 0x740#64) 1 ∗
      (memRegion (coroPtr + 0x741#64) 32 ∗ (memRegion (coroPtr + 0x761#64) 32 ∗
        memRegion (coroPtr + 0x781#64) 1))))))))))))) =
      memRegion (coroPtr + 0x658#64) 298 := by
    rw [← ProofLib.memRegion_split' (b := coroPtr + 0x761#64) (n := 32) (k := 1)
          (b' := coroPtr + 0x781#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x741#64) (n := 32) (k := 33)
          (b' := coroPtr + 0x761#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x740#64) (n := 1) (k := 65)
          (b' := coroPtr + 0x741#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x738#64) (n := 8) (k := 66)
          (b' := coroPtr + 0x740#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x730#64) (n := 8) (k := 74)
          (b' := coroPtr + 0x738#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x728#64) (n := 8) (k := 82)
          (b' := coroPtr + 0x730#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x720#64) (n := 8) (k := 90)
          (b' := coroPtr + 0x728#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x718#64) (n := 8) (k := 98)
          (b' := coroPtr + 0x720#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x6f8#64) (n := 32) (k := 106)
          (b' := coroPtr + 0x718#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x6d8#64) (n := 32) (k := 138)
          (b' := coroPtr + 0x6f8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x6b8#64) (n := 32) (k := 170)
          (b' := coroPtr + 0x6d8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x698#64) (n := 32) (k := 202)
          (b' := coroPtr + 0x6b8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x678#64) (n := 32) (k := 234)
          (b' := coroPtr + 0x698#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x658#64) (n := 32) (k := 266)
          (b' := coroPtr + 0x678#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

theorem p2_words2_entails_cells2 (p u0 u1 : BitVec 64) :
    (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ⊢ cells p 2 := by
  have h : cells p 2 = (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  rw [h]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1 (Entails.refl _))

theorem p2_coro4f8_words2_328_entails_344 (coroPtr u0 u1 : BitVec 64) :
    ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1) ∗
      memRegion (coroPtr + 0x508#64) 328 ⊢ memRegion (coroPtr + 0x4f8#64) 344 := by
  rw [← p2_coro4f8_2cells_328_eq_344 coroPtr]
  have h := p2_words2_entails_cells2 (coroPtr + 0x4f8#64) u0 u1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [← sepConj_assoc]
  exact sepConj_mono_left h

theorem p2_coro788_words2_entails_16 (coroPtr u0 u1 : BitVec 64) :
    ((coroPtr + 0x788#64) ↦₆₄ u0) ∗ ((coroPtr + 0x790#64) ↦₆₄ u1) ⊢
      memRegion (coroPtr + 0x788#64) 16 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x788#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x790#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ u0) (pointsTo64_entails_memRegion _ u1)

theorem p2_coro398_bytes_words4_entails_96 (coroPtr : BitVec 64)
    (spkPub spkPriv : List (BitVec 8)) (u0 u1 u2 u3 : BitVec 64)
    (hpub : spkPub.length = 32) (hpriv : spkPriv.length = 32) :
    ((coroPtr + 0x398#64) ↦ₛ spkPub) ∗ ((coroPtr + 0x3b8#64) ↦ₛ spkPriv) ∗
      ((coroPtr + 0x3d8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u1) ∗
      ((coroPtr + 0x3e8#64) ↦₆₄ u2) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u3) ⊢
      memRegion (coroPtr + 0x398#64) 96 := by
  have hm := sepConj_mono (p2_pointsToBytes_entails_memRegion (coroPtr + 0x398#64) spkPub 32 hpub)
    (sepConj_mono (p2_pointsToBytes_entails_memRegion (coroPtr + 0x3b8#64) spkPriv 32 hpriv)
    (sepConj_mono (pointsTo64_entails_memRegion (coroPtr + 0x3d8#64) u0)
    (sepConj_mono (pointsTo64_entails_memRegion (coroPtr + 0x3e0#64) u1)
    (sepConj_mono (pointsTo64_entails_memRegion (coroPtr + 0x3e8#64) u2)
      (pointsTo64_entails_memRegion (coroPtr + 0x3f0#64) u3)))))
  have heq :
      memRegion (coroPtr + 0x398#64) 32 ∗ (memRegion (coroPtr + 0x3b8#64) 32 ∗
      (memRegion (coroPtr + 0x3d8#64) 8 ∗ (memRegion (coroPtr + 0x3e0#64) 8 ∗
      (memRegion (coroPtr + 0x3e8#64) 8 ∗ memRegion (coroPtr + 0x3f0#64) 8)))) =
      memRegion (coroPtr + 0x398#64) 96 := by
    rw [← ProofLib.memRegion_split' (b := coroPtr + 0x3e8#64) (n := 8) (k := 8)
          (b' := coroPtr + 0x3f0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x3e0#64) (n := 8) (k := 16)
          (b' := coroPtr + 0x3e8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x3d8#64) (n := 8) (k := 24)
          (b' := coroPtr + 0x3e0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x3b8#64) (n := 32) (k := 32)
          (b' := coroPtr + 0x3d8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x398#64) (n := 32) (k := 64)
          (b' := coroPtr + 0x3b8#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

theorem p2_coro4b0_byte_bytes_entails_65 (coroPtr : BitVec 64) (tag : BitVec 8)
    (pkB skB : List (BitVec 8)) (hpk : pkB.length = 32) (hsk : skB.length = 32) :
    ((coroPtr + 0x4b0#64) ↦₈ tag) ∗ ((coroPtr + 0x4b1#64) ↦ₛ pkB) ∗
      ((coroPtr + 0x4d1#64) ↦ₛ skB) ⊢ memRegion (coroPtr + 0x4b0#64) 65 := by
  have hm := sepConj_mono (pointsTo8_entails_memRegion (coroPtr + 0x4b0#64) tag)
    (sepConj_mono (p2_pointsToBytes_entails_memRegion (coroPtr + 0x4b1#64) pkB 32 hpk)
      (p2_pointsToBytes_entails_memRegion (coroPtr + 0x4d1#64) skB 32 hsk))
  have heq :
      memRegion (coroPtr + 0x4b0#64) 1 ∗
      (memRegion (coroPtr + 0x4b1#64) 32 ∗ memRegion (coroPtr + 0x4d1#64) 32) =
      memRegion (coroPtr + 0x4b0#64) 65 := by
    rw [← ProofLib.memRegion_split' (b := coroPtr + 0x4b1#64) (n := 32) (k := 32)
          (b' := coroPtr + 0x4d1#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x4b0#64) (n := 1) (k := 64)
          (b' := coroPtr + 0x4b1#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

theorem p2_sp80_11words_entails_88 (sp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64) :
    ((sp + 0x80#64) ↦₆₄ u0) ∗ ((sp + 0x88#64) ↦₆₄ u1) ∗ ((sp + 0x90#64) ↦₆₄ u2) ∗
      ((sp + 0x98#64) ↦₆₄ u3) ∗ ((sp + 0xa0#64) ↦₆₄ u4) ∗ ((sp + 0xa8#64) ↦₆₄ u5) ∗
      ((sp + 0xb0#64) ↦₆₄ u6) ∗ ((sp + 0xb8#64) ↦₆₄ u7) ∗ ((sp + 0xc0#64) ↦₆₄ u8) ∗
      ((sp + 0xc8#64) ↦₆₄ u9) ∗ ((sp + 0xd0#64) ↦₆₄ u10) ⊢
      memRegion (sp + 0x80#64) 88 := by
  have hm := sepConj_mono (pointsTo64_entails_memRegion (sp + 0x80#64) u0)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x88#64) u1)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x90#64) u2)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x98#64) u3)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xa0#64) u4)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xa8#64) u5)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xb0#64) u6)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xb8#64) u7)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xc0#64) u8)
    (sepConj_mono (pointsTo64_entails_memRegion (sp + 0xc8#64) u9)
      (pointsTo64_entails_memRegion (sp + 0xd0#64) u10))))))))))
  have heq :
      memRegion (sp + 0x80#64) 8 ∗ (memRegion (sp + 0x88#64) 8 ∗ (memRegion (sp + 0x90#64) 8 ∗
      (memRegion (sp + 0x98#64) 8 ∗ (memRegion (sp + 0xa0#64) 8 ∗ (memRegion (sp + 0xa8#64) 8 ∗
      (memRegion (sp + 0xb0#64) 8 ∗ (memRegion (sp + 0xb8#64) 8 ∗ (memRegion (sp + 0xc0#64) 8 ∗
      (memRegion (sp + 0xc8#64) 8 ∗ memRegion (sp + 0xd0#64) 8))))))))) =
      memRegion (sp + 0x80#64) 88 := by
    rw [← ProofLib.memRegion_split' (b := sp + 0xc8#64) (n := 8) (k := 8)
          (b' := sp + 0xd0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0xc0#64) (n := 8) (k := 16)
          (b' := sp + 0xc8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0xb8#64) (n := 8) (k := 24)
          (b' := sp + 0xc0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0xb0#64) (n := 8) (k := 32)
          (b' := sp + 0xb8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0xa8#64) (n := 8) (k := 40)
          (b' := sp + 0xb0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0xa0#64) (n := 8) (k := 48)
          (b' := sp + 0xa8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x98#64) (n := 8) (k := 56)
          (b' := sp + 0xa0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x90#64) (n := 8) (k := 64)
          (b' := sp + 0x98#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x88#64) (n := 8) (k := 72)
          (b' := sp + 0x90#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 0x80#64) (n := 8) (k := 80)
          (b' := sp + 0x88#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

theorem p2_sp80_24_split_words3 (sp : BitVec 64) :
    memRegion (sp + 0x80#64) 24 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ((sp + 0x80#64) ↦₆₄ u0) ∗ ((sp + 0x88#64) ↦₆₄ u1) ∗ ((sp + 0x90#64) ↦₆₄ u2) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x80#64) (n := 8) (k := 16)
        (b' := sp + 0x88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x88#64) (n := 8) (k := 8)
        (b' := sp + 0x90#64) rfl (by bv_omega) (by decide)]
  simp only [ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

theorem p2_sp3b0_48_split_8_40 (sp : BitVec 64) :
    memRegion (sp + 0x3b0#64) 48 =
      memRegion (sp + 0x3b0#64) 8 ∗
        memRegion (sp + 0x3b8#64) 8 ∗ memRegion (sp + 0x3c0#64) 8 ∗
        memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3cf#64) 1 ∗
        memRegion (sp + 0x3d0#64) 8 ∗ memRegion (sp + 0x3d8#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3b0#64) (n := 8) (k := 40)
        (b' := sp + 0x3b8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3b8#64) (n := 8) (k := 32)
        (b' := sp + 0x3c0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3c0#64) (n := 8) (k := 24)
        (b' := sp + 0x3c8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3c8#64) (n := 7) (k := 17)
        (b' := sp + 0x3cf#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3cf#64) (n := 1) (k := 16)
        (b' := sp + 0x3d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3d0#64) (n := 8) (k := 8)
        (b' := sp + 0x3d8#64) rfl (by bv_omega) (by decide)]

theorem p2_sp3b0_words6_entails_48 (sp u0 u1 u2 u3 u4 u5 : BitVec 64) :
    ((sp + 0x3b0#64) ↦₆₄ u0) ∗ ((sp + 0x3b8#64) ↦₆₄ u1) ∗ ((sp + 0x3c0#64) ↦₆₄ u2) ∗
      ((sp + 0x3c8#64) ↦₆₄ u3) ∗ ((sp + 0x3d0#64) ↦₆₄ u4) ∗ ((sp + 0x3d8#64) ↦₆₄ u5) ⊢
      memRegion (sp + 0x3b0#64) 48 := by
  have h := p2_speWordsAt_entails_memRegion48 (sp + 0x3b0#64) u0 u1 u2 u3 u4 u5
  dsimp only [speWordsAt] at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem p2_coro298_20_split (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x298#64) 20 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 32,
        ((coroPtr + 0x298#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x2a8#64) ↦₃₂ u2) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x298#64) (n := 8) (k := 12)
        (b' := coroPtr + 0x2a0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x2a0#64) (n := 8) (k := 4)
        (b' := coroPtr + 0x2a8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x298#64),
      ProofLib.memRegion_eight (coroPtr + 0x2a0#64),
      ProofLib.memRegion_four (coroPtr + 0x2a8#64)]
  simp only [sepConj_assoc, sepExists_sepConj_left]
  simp only [sepExists_sepConj_right, sepConj_assoc]

theorem p2_coro298_words_entails_20 (coroPtr u0 u1 : BitVec 64) (u2 : BitVec 32) :
    ((coroPtr + 0x298#64) ↦₆₄ u0) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u1) ∗
      ((coroPtr + 0x2a8#64) ↦₃₂ u2) ⊢ memRegion (coroPtr + 0x298#64) 20 := by
  rw [p2_coro298_20_split coroPtr]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.refl _)))

theorem p2_coro398_cells8_4_eq_96 (coroPtr : BitVec 64) :
    cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 =
      memRegion (coroPtr + 0x398#64) 96 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide),
      ← ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide),
      ← ProofLib.memRegion_split' (b := coroPtr + 0x398#64) (n := 64) (k := 32)
          (b' := coroPtr + 0x3d8#64) rfl (by bv_omega) (by decide)]

theorem p2_coro398_bytes_cells4_entails_96 (coroPtr : BitVec 64)
    (spkPub spkPriv : List (BitVec 8)) (hpub : spkPub.length = 32) (hpriv : spkPriv.length = 32) :
    ((coroPtr + 0x398#64) ↦ₛ spkPub) ∗ ((coroPtr + 0x3b8#64) ↦ₛ spkPriv) ∗
      cells (coroPtr + 0x3d8#64) 4 ⊢ memRegion (coroPtr + 0x398#64) 96 := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide)]
  have hm := sepConj_mono (p2_pointsToBytes_entails_memRegion (coroPtr + 0x398#64) spkPub 32 hpub)
    (sepConj_mono (p2_pointsToBytes_entails_memRegion (coroPtr + 0x3b8#64) spkPriv 32 hpriv)
      (Entails.refl (memRegion (coroPtr + 0x3d8#64) 32)))
  have heq :
      memRegion (coroPtr + 0x398#64) 32 ∗
      (memRegion (coroPtr + 0x3b8#64) 32 ∗ memRegion (coroPtr + 0x3d8#64) 32) =
      memRegion (coroPtr + 0x398#64) 96 := by
    rw [← ProofLib.memRegion_split' (b := coroPtr + 0x3b8#64) (n := 32) (k := 32)
          (b' := coroPtr + 0x3d8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := coroPtr + 0x398#64) (n := 32) (k := 64)
          (b' := coroPtr + 0x3b8#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

theorem p2_coro4b0_byte_64_entails_65 (coroPtr : BitVec 64) (b : BitVec 8) :
    ((coroPtr + 0x4b0#64) ↦₈ b) ∗ memRegion (coroPtr + 0x4b1#64) 64 ⊢
      memRegion (coroPtr + 0x4b0#64) 65 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x4b0#64) (n := 1) (k := 64)
        (b' := coroPtr + 0x4b1#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion (coroPtr + 0x4b0#64) b)

/-- Read-only `PreKeySignalMessage` fields accessed during Stage P2 (`+0x70..+0xf0` + `ctBufPtr`). -/
def p2MsgFieldsAt (msgPtr ctBufPtr : BitVec 64) (hdr : HandshakeHdr)
    (msgVerByte : BitVec 8) (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32) :
    SepProp :=
  ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((msgPtr + 0x78#64) ↦₃₂ opkOptTag32 (hdrOpkIdBv? hdr)) ∗
  ((msgPtr + 0x7c#64) ↦₃₂ opkIdWord) ∗
  ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
  ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
  ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
  ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 hdr.ekAPk) ∗
  ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 hdr.ikAPk) ∗
  ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
  ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
  ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
  (ctBufPtr ↦ₛ (8#8 :: bytesToBv8 hdr.kemCt))

/-- Coroutine Stage-P2 scratch regions at `+0x4f8..+0x7d8` preserved identically across all exits. -/
def p2CoroScratchTailAt (coroPtr : BitVec 64) : SepProp :=
  memRegion (coroPtr + 0x4f8#64) 344 ∗
  memRegion (coroPtr + 0x650#64) 8 ∗
  memRegion (coroPtr + 0x658#64) 298 ∗
  memRegion (coroPtr + 0x788#64) 16 ∗
  memRegion (coroPtr + 0x798#64) 64

/-- Common coroutine, stack, message, address, and allocator spatial frame delivered uniformly at
`s0.readReg64 .x30` on all 6 Stage-P2 error exits (Arms 1–6). -/
def p2ErrFrameAt (A : RustAlloc) (img : Obj.Image) (s0 : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt ∗
  memRegion (coroPtr + 0x488#64) 8 ∗
  memRegion (coroPtr + 0x4b0#64) 65 ∗
  ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  memRegion (sp + 0x80#64) 88 ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 48 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  logOff img ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
