/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBob
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty

/-!
# `SessionState` Byte-Layout and Parameter Bridge Lemmas for Stage P2.5 & P2.6

344-byte `SessionState` byte-layout splitting/folding lemmas (`bobSession280MidBv8`,
`bobSession344WithRegIdsBv8`), 32-byte word/byte equivalences, and `BobSignalProtocolParameters` /
`<IdentityKey>::is_same_account` bridges for `AssemblyP2b`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.InMem

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. `SessionState` and `stageP2_sub5` / `stageP2_sub6` Framing Helpers -/

open CryptoVerification.E2E.InMem
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.HashbrownBin
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchet.Getters

/-- Middle 280 bytes (`+0x38..+0x150`) of `bobSession344Bv8`. -/
def bobSession280MidBv8 (rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 0#64 ++
  Initiator.senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++ unpack32
    pad_f4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 c0 ++ unpack64 c1 ++ unpack64 c2 ++ unpack64 c3 ++ unpack64 c4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 d0 ++ unpack64 d1 ++ unpack64 d2 ++
  unpack64 4#64

@[simp]
theorem bobSession280MidBv8_length (p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length = 280 := by
  unfold bobSession280MidBv8 Initiator.senderChainBytes100
  simp only [List.length_append, unpack64_length, unpack32_length]

/-- 344-byte `SessionState` with `remoteRegId` at `+0x150` and `localRegId` at `+0x154`. -/
def bobSession344WithRegIdsBv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++
  bobSession280MidBv8 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
  unpack32 remoteRegId ++ unpack32 localRegId

@[simp]
theorem bobSession344WithRegIdsBv8_length (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      remoteRegId localRegId).length = 344 := by
  unfold bobSession344WithRegIdsBv8
  simp only [List.length_append, unpack64_length, unpack32_length, bobSession280MidBv8_length]

theorem bobSession344Bv8_eq_head56_mid280_zero (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        unpack64 0#64))))))) := by
  unfold bobSession344Bv8 bobHead144Bv8 bobTail96Bv8 bobSession280MidBv8
  simp only [List.append_assoc]

theorem bobSession344_split_56_288 (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (a ↦ₛ bobSession344Bv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) =
      (a ↦₆₄ 33#64) ∗
      ((a + 0x8#64) ↦₆₄ p1) ∗
      ((a + 0x10#64) ↦₆₄ 33#64) ∗
      ((a + 0x18#64) ↦₆₄ 33#64) ∗
      ((a + 0x20#64) ↦₆₄ p2) ∗
      ((a + 0x28#64) ↦₆₄ 33#64) ∗
      ((a + 0x30#64) ↦₆₄ 32#64) ∗
      ((a + 0x38#64) ↦ₛ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
        unpack64 0#64)) := by
  rw [bobSession344Bv8_eq_head56_mid280_zero]
  rw [pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bobSession288Rest_split_280_4_4 (a p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (a ↦ₛ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++ unpack64
      0#64)) =
      (a ↦ₛ bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
      ((a + 0x118#64) ↦₃₂ 0#32) ∗
      ((a + 0x11c#64) ↦₃₂ 0#32) := by
  have h0 : unpack64 0#64 = unpack32 0#32 ++ unpack32 0#32 := by rfl
  rw [h0, pointsToBytes_append, bobSession280MidBv8_length,
      pointsToBytes_append, unpack32_length,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bobSession344WithRegIds_fold (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (a ↦₆₄ 33#64) ∗
    ((a + 0x8#64) ↦₆₄ p1) ∗
    ((a + 0x10#64) ↦₆₄ 33#64) ∗
    ((a + 0x18#64) ↦₆₄ 33#64) ∗
    ((a + 0x20#64) ↦₆₄ p2) ∗
    ((a + 0x28#64) ↦₆₄ 33#64) ∗
    ((a + 0x30#64) ↦₆₄ 32#64) ∗
    ((a + 0x38#64) ↦ₛ bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    ((a + 0x150#64) ↦₃₂ remoteRegId) ∗
    ((a + 0x154#64) ↦₃₂ localRegId) =
      (a ↦ₛ bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId) := by
  have hfold :
      bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold bobSession344WithRegIdsBv8
    simp only [List.append_assoc]
  rw [hfold,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, bobSession280MidBv8_length,
      pointsToBytes_append, unpack32_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bobSession344WithRegIds_head_split (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (a ↦ₛ bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      remoteRegId localRegId) =
    (a ↦₆₄ 33#64) ∗
    ((a + 8#64) ↦ₛ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId))))))))) := by
  have hfold :
      bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold bobSession344WithRegIdsBv8
    simp only [List.append_assoc]
  rw [hfold, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]

theorem sp3e0_after_seg6a_entails (sp ss1 ss4 : BitVec 64) (ssRest : List (BitVec 8))
    (hssRest_len : ssRest.length = 288) :
    ((sp + 0x3e8#64) ↦₆₄ ss1) ∗ ((sp + 0x3f0#64) ↦₆₄ 33#64) ∗
    ((sp + 0x3f8#64) ↦₆₄ 33#64) ∗ ((sp + 0x400#64) ↦₆₄ ss4) ∗
    ((sp + 0x408#64) ↦₆₄ 33#64) ∗ ((sp + 0x410#64) ↦₆₄ 32#64) ∗
    ((sp + 0x418#64) ↦ₛ ssRest) ⊢
      (∃∗ u_3e8 : BitVec 32, ((sp + 0x3e8#64) ↦₃₂ u_3e8) ∗
        memRegion (sp + 0x3ec#64) 332) := by
  have h1 : ((sp + 0x3e8#64) ↦₆₄ ss1) ⊢
      (∃∗ u_3e8 : BitVec 32, ((sp + 0x3e8#64) ↦₃₂ u_3e8)) ∗ memRegion (sp + 0x3ec#64) 4 := by
    rw [← ProofLib.memRegion_four (sp + 0x3e8#64),
        ← ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 4)
            (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide)]
    exact pointsTo64_entails_memRegion _ _
  have hrest : ((sp + 0x418#64) ↦ₛ ssRest) ⊢ memRegion (sp + 0x418#64) 288 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x418#64) ssRest
    rwa [hssRest_len] at h
  refine Entails.trans (sepConj_mono h1
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) hrest)))))) ?_
  rw [sepConj_assoc, sepExists_sepConj_left,
      ← ProofLib.memRegion_split' (b := sp + 0x410#64) (n := 8) (k := 288)
        (b' := sp + 0x418#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296)
        (b' := sp + 0x410#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 328)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem sp3e0_after_seg6c_entails (sp v0 : BitVec 64) (v8 : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ v0) ∗ ((sp + 0x3e8#64) ↦₃₂ v8) ∗ memRegion (sp + 0x3ec#64) 332 ⊢
      memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336)
        (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 332)
        (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo32_entails_memRegion _ _))

theorem sp3f0_328_split_5words (sp : BitVec 64) :
    memRegion (sp + 0x3f0#64) 328 =
      (∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ((sp + 0x3f0#64) ↦₆₄ w2) ∗ ((sp + 0x3f8#64) ↦₆₄ w3) ∗
        ((sp + 0x400#64) ↦₆₄ w4) ∗ ((sp + 0x408#64) ↦₆₄ w5) ∗
        ((sp + 0x410#64) ↦₆₄ w6) ∗ memRegion (sp + 0x418#64) 288) := by
  have hc : memRegion (sp + 0x3f0#64) 40 = cells (sp + 0x3f0#64) 5 :=
    ProofLib.memRegion_cells (sp + 0x3f0#64) 5 (by decide)
  rw [ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 40) (k := 288)
        (b' := sp + 0x418#64) rfl (by bv_omega) (by decide), hc]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem cells6_250_split_for_seg6f (coroPtr : BitVec 64) :
    cells (coroPtr + 0x250#64) 6 ⊢
      ∃∗ u_250 : BitVec 64, ∃∗ u_258 : BitVec 64, ∃∗ u_260 : BitVec 64,
      ∃∗ u_268 : BitVec 32, ∃∗ u_26c : BitVec 32,
      ∃∗ u_270 : BitVec 64, ∃∗ u_278 : BitVec 64,
        ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
        ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
        ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗ ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
        ((coroPtr + 0x278#64) ↦₆₄ u_278) := by
  rw [← ProofLib.memRegion_cells (coroPtr + 0x250#64) 6 (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x250#64) (n := 8) (k := 40)
        (b' := coroPtr + 0x258#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x258#64) (n := 8) (k := 32)
        (b' := coroPtr + 0x260#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x260#64) (n := 8) (k := 24)
        (b' := coroPtr + 0x268#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x268#64) (n := 4) (k := 20)
        (b' := coroPtr + 0x26c#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x26c#64) (n := 4) (k := 16)
        (b' := coroPtr + 0x270#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x270#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x278#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x250#64),
      ProofLib.memRegion_eight (coroPtr + 0x258#64),
      ProofLib.memRegion_eight (coroPtr + 0x260#64),
      ProofLib.memRegion_four (coroPtr + 0x268#64),
      ProofLib.memRegion_four (coroPtr + 0x26c#64),
      ProofLib.memRegion_eight (coroPtr + 0x270#64),
      ProofLib.memRegion_eight (coroPtr + 0x278#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun x => Entails.sepExists_elim fun x_1 =>
    Entails.sepExists_elim fun x_2 => Entails.sepExists_elim fun x_3 =>
    Entails.sepExists_elim fun x_4 => Entails.sepExists_elim fun x_5 =>
    Entails.sepExists_elim fun x_6 => Entails.sepExists_right x_6
    (Entails.sepExists_right x_5 (Entails.sepExists_right x_4 (Entails.sepExists_right x_3
    (Entails.sepExists_right x_2 (Entails.sepExists_right x_1 (Entails.sepExists_right x
      (Entails.refl _)))))))

theorem memRegion_a90_288_split_cells6 (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 288 =
      cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 240 := by
  rw [ProofLib.memRegion_split' (b := sp + 0xa90#64) (n := 48) (k := 240)
        (b' := sp + 0xac0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide)]

/-! ## 2. 32-Byte Word/Byte Equivalence and `stageP2_sub5` Helpers -/

theorem exists_split_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (w0 w1 w2 w3 : BitVec 64),
      bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 := by
  have hw0 : (bs.take 8).length = 8 := by simp [h]
  have hw1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have hw2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have hw3 : (bs.drop 24).length = 8 := by simp [h]
  obtain ⟨w0, hw0_eq⟩ := exists_unpack64_of_length_8 hw0
  obtain ⟨w1, hw1_eq⟩ := exists_unpack64_of_length_8 hw1
  obtain ⟨w2, hw2_eq⟩ := exists_unpack64_of_length_8 hw2
  obtain ⟨w3, hw3_eq⟩ := exists_unpack64_of_length_8 hw3
  refine ⟨w0, w1, w2, w3, ?_⟩
  rw [← hw0_eq, ← hw1_eq, ← hw2_eq, ← hw3_eq]
  simp only [List.append_assoc]
  have s2 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
    have := List.take_append_drop 8 (bs.drop 16)
    rwa [List.drop_drop] at this
  have s1 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
    have := List.take_append_drop 8 (bs.drop 8)
    rwa [List.drop_drop] at this
  rw [s2, s1, List.take_append_drop]

theorem pointsToBytes_of_eq_unpack64_4 {bs : List (BitVec 8)} {u0 u1 u2 u3 : BitVec 64}
    (h : bs = unpack64 u0 ++ unpack64 u1 ++ unpack64 u2 ++ unpack64 u3) (a : BitVec 64) :
    (a ↦ₛ bs) = (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) := by
  rw [h]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion65_eq_byte_words8 (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
       ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗
        ((a + 0x01#64) ↦₆₄ u0) ∗ ((a + 0x09#64) ↦₆₄ u1) ∗
        ((a + 0x11#64) ↦₆₄ u2) ∗ ((a + 0x19#64) ↦₆₄ u3) ∗
        ((a + 0x21#64) ↦₆₄ u4) ∗ ((a + 0x29#64) ↦₆₄ u5) ∗
        ((a + 0x31#64) ↦₆₄ u6) ∗ ((a + 0x39#64) ↦₆₄ u7)) := by
  have hc : memRegion (a + 1#64) 64 = cells (a + 1#64) 8 :=
    ProofLib.memRegion_cells (a + 1#64) 8 (by decide)
  rw [show (65 : Nat) = 1 + 64 from rfl,
      memRegion_split a 1 64 (by decide),
      memRegion_one a, hc]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem pointsTo8_words8_entails_memRegion65
    (a ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗
    ((a + 0x01#64) ↦₆₄ ik0) ∗ ((a + 0x09#64) ↦₆₄ ik1) ∗
    ((a + 0x11#64) ↦₆₄ ik2) ∗ ((a + 0x19#64) ↦₆₄ ik3) ∗
    ((a + 0x21#64) ↦₆₄ ik4) ∗ ((a + 0x29#64) ↦₆₄ ik5) ∗
    ((a + 0x31#64) ↦₆₄ ik6) ∗ ((a + 0x39#64) ↦₆₄ ik7) ⊢
      memRegion a 65 := by
  rw [memRegion65_eq_byte_words8 a]
  refine Entails.sepExists_right ik0 (Entails.sepExists_right ik1 (Entails.sepExists_right ik2
    (Entails.sepExists_right ik3 (Entails.sepExists_right ik4 (Entails.sepExists_right ik5
    (Entails.sepExists_right ik6 (Entails.sepExists_right ik7 (Entails.sepExists_right b0
      (Entails.refl _)))))))))

theorem memRegion65_eq_words8_byte (a : BitVec 64) :
    memRegion a 65 =
      (∃∗ b64 : BitVec 8,
       ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        (a ↦₆₄ u0) ∗ ((a + 0x08#64) ↦₆₄ u1) ∗ ((a + 0x10#64) ↦₆₄ u2) ∗ ((a + 0x18#64) ↦₆₄ u3) ∗
        ((a + 0x20#64) ↦₆₄ u4) ∗ ((a + 0x28#64) ↦₆₄ u5) ∗ ((a + 0x30#64) ↦₆₄ u6) ∗
          ((a + 0x38#64) ↦₆₄ u7) ∗
        ((a + 0x40#64) ↦₈ b64)) := by
  have hc : memRegion a 64 = cells a 8 :=
    ProofLib.memRegion_cells a 8 (by decide)
  rw [show (65 : Nat) = 64 + 1 from rfl,
      memRegion_split a 64 1 (by decide),
      hc, memRegion_one (a + 64#64)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem words8_byte_entails_memRegion65
    (a u0 u1 u2 u3 u4 u5 u6 u7 : BitVec 64) (b64 : BitVec 8) :
    (a ↦₆₄ u0) ∗ ((a + 0x08#64) ↦₆₄ u1) ∗ ((a + 0x10#64) ↦₆₄ u2) ∗ ((a + 0x18#64) ↦₆₄ u3) ∗
    ((a + 0x20#64) ↦₆₄ u4) ∗ ((a + 0x28#64) ↦₆₄ u5) ∗ ((a + 0x30#64) ↦₆₄ u6) ∗
      ((a + 0x38#64) ↦₆₄ u7) ∗
    ((a + 0x40#64) ↦₈ b64) ⊢
      memRegion a 65 := by
  rw [memRegion65_eq_words8_byte a]
  refine Entails.sepExists_right b64 (Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3 (Entails.sepExists_right u4
    (Entails.sepExists_right u5 (Entails.sepExists_right u6 (Entails.sepExists_right u7
      (Entails.refl _)))))))))

theorem coro798_64_entails_unaligned (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x798#64) 64 ⊢
      ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
      ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
      ∃∗ cw0 : BitVec 64, ∃∗ cw1 : BitVec 64, ∃∗ cw2 : BitVec 64, ∃∗ cw3 : BitVec 64,
      ∃∗ cw4 : BitVec 64, ∃∗ cw5 : BitVec 64, ∃∗ cw6 : BitVec 64, ∃∗ c63 : BitVec 8,
        bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
        ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗ ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
        ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗ ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
        ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗ ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
        ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗ ((coroPtr + 0x7d7#64) ↦₈ c63) := by
  rw [ProofLib.memRegion_cells (coroPtr + 0x798#64) 8 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
    Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
    Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 =>
    Entails.sepExists_elim fun u6 => Entails.sepExists_elim fun u7 => ?_
  have hw := words8_eq_keyPair64UnalignedAt (coroPtr + 0x798#64) u0 u1 u2 u3 u4 u5 u6 u7
  unfold keyPair64UnalignedAt at hw
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hw
  rw [hw]
  exact Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
    (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.refl _)))))))))))))))

theorem identityKey_ne_of_bytes_ne {b1 b2 : Shared.Bytes}
    (h1 : (bytesToBv8 b1).length = 32) (h2 : (bytesToBv8 b2).length = 32)
    (hne : b1 ≠ b2) :
    (⟨⟨⟨bytesToBv8 b1, h1⟩⟩⟩ : IdentityKey) ≠ ⟨⟨⟨bytesToBv8 b2, h2⟩⟩⟩ := by
  intro heq
  apply hne
  have hlist : List.map UInt8.toBitVec b1 = List.map UInt8.toBitVec b2 := by
    simpa [bytesToBv8] using congrArg (fun k : IdentityKey => k.publicKey.bytes.toList) heq
  exact List.map_injective_iff.mpr (fun x y h => by cases x; cases y; cases h; rfl) hlist

theorem setWidth8_eq_zero_of_setWidth32 {w : BitVec 64} (h : w.setWidth 32 = 0#32) :
    w.setWidth 8 = 0#8 :=
  (_root_.BitVec.setWidth_setWidth_of_le w (_root_.Nat.le_add_left 8 24)).symm.trans
    ((congrArg (BitVec.setWidth 8) h).trans (_root_.BitVec.setWidth_zero 8 32))

theorem pqsk_entails_memRegion_3168 (pqskPtr : BitVec 64) (pqspkBSk : Shared.Bytes)
    (hlen : pqspkBSk.length = 3168) :
    (pqskPtr ↦₈ (bytesToBv8 pqspkBSk).getD 0 0#8) ∗
    ((pqskPtr + 1#64) ↦ₛ (bytesToBv8 pqspkBSk).drop 1) ⊢
      memRegion pqskPtr 3168 := by
  have h1 : ((pqskPtr + 1#64) ↦ₛ (bytesToBv8 pqspkBSk).drop 1) ⊢ memRegion (pqskPtr + 1#64) 3167 :=
    by
    have h := pointsToBytes_entails_memRegion (pqskPtr + 1#64) ((bytesToBv8 pqspkBSk).drop 1)
    have hlen2 : ((bytesToBv8 pqspkBSk).drop 1).length = 3167 := by
      simp [bytesToBv8, hlen]
    rwa [hlen2] at h
  rw [show (3168 : Nat) = 1 + 3167 from rfl,
      memRegion_split pqskPtr 1 3167 (by decide)]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _) h1

theorem memRegion7_eq_bytes7At (a : BitVec 64) :
    memRegion a 7 =
      (∃∗ b6 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b4 : BitVec 8, ∃∗ b3 : BitVec 8,
       ∃∗ b2 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8,
        bytes7At a b0 b1 b2 b3 b4 b5 b6) := by
  unfold bytes7At
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 6) (b' :=
    a + 1#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 1#64) (n := 1) (k := 5) (b' :=
        a + 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 2#64) (n := 1) (k := 4) (b' :=
        a + 3#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 3#64) (n := 1) (k := 3) (b' :=
        a + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 1) (k := 2) (b' :=
        a + 5#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 5#64) (n := 1) (k := 1) (b' :=
        a + 6#64) rfl (by bv_omega) (by decide),
      memRegion_one a, memRegion_one (a + 1#64), memRegion_one (a + 2#64),
      memRegion_one (a + 3#64), memRegion_one (a + 4#64), memRegion_one (a + 5#64),
      memRegion_one (a + 6#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem bytes7At_entails_memRegion7 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At a b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion a 7 := by
  rw [memRegion7_eq_bytes7At a]
  exact Entails.sepExists_right b6 (Entails.sepExists_right b5 (Entails.sepExists_right b4
    (Entails.sepExists_right b3 (Entails.sepExists_right b2 (Entails.sepExists_right b1
    (Entails.sepExists_right b0 (Entails.refl _)))))))

theorem inMemId16Box_entails_memRegion (futPtr self : BitVec 64) (st : BitVec 8) :
    (futPtr ↦₆₄ self) ∗ ((futPtr + 8#64) ↦₈ st) ∗ memRegion (futPtr + 9#64) 7 ⊢
      memRegion futPtr 16 := by
  rw [ProofLib.memRegion_split' (b := futPtr) (n := 8) (k := 8)
        (b' := futPtr + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := futPtr + 8#64) (n := 1) (k := 7)
        (b' := futPtr + 9#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo8_entails_memRegion _ _))

theorem sp3e0_344_split_65_279 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 344 =
      memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 279 :=
  ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 65) (k := 279)
    (b' := sp + 0x421#64) rfl (by bv_omega) (by decide)

theorem SepWPp.exists_elim_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {R : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog ret s (P x ∗ R) Q Qp) :
    SepWPp prog ret s ((∃∗ x, P x) ∗ R) Q Qp := by
  rw [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem SepWPp.cells_succ_elim {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {R : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWPp prog ret s (cells (a + 8#64) k ∗ (a ↦₆₄ v) ∗ R) Q Qp) :
    SepWPp prog ret s (cells a (k + 1) ∗ R) Q Qp := by
  rw [cells_succ, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun v => ?_
  rw [show ((a ↦₆₄ v) ∗ cells (a + 8#64) k) ∗ R = cells (a + 8#64) k ∗ (a ↦₆₄ v) ∗ R by ac_rfl]
  exact h v

theorem cells_succ_entails {a : BitVec 64} {k : Nat} {v : BitVec 64} {R : SepProp}
    (h : R ⊢ cells (a + 8#64) k) :
    (a ↦₆₄ v) ∗ R ⊢ cells a (k + 1) :=
  Entails.sepExists_right v (sepConj_mono_right h)

theorem cells_one_entails (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ cells a 1 := by
  rw [cells_succ]
  refine Entails.sepExists_right v ?_
  rw [cells_zero, sepConj_emp]
  exact Entails.refl _

theorem point8_keyPair64UnalignedAt_eq_words8_byte
    (tag b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 opk0 : BitVec 64)
    (hw : ∀ p : BitVec 64, (p ↦₈ tag) ∗ bytes7At (p + 1#64) b0 b1 b2 b3 b4 b5 b6 = (p ↦₆₄ opk0))
    (a : BitVec 64) :
    (a ↦₈ tag) ∗
    keyPair64UnalignedAt (a + 1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 =
      (a ↦₆₄ opk0) ∗ ((a + 0x08#64) ↦₆₄ w0) ∗ ((a + 0x10#64) ↦₆₄ w1) ∗ ((a + 0x18#64) ↦₆₄ w2) ∗
      ((a + 0x20#64) ↦₆₄ w3) ∗ ((a + 0x28#64) ↦₆₄ w4) ∗ ((a + 0x30#64) ↦₆₄ w5) ∗
        ((a + 0x38#64) ↦₆₄ w6) ∗
      ((a + 0x40#64) ↦₈ b63) := by
  unfold keyPair64UnalignedAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← sepConj_assoc]
  rw [hw a]

theorem sp3ec_332_split_for_seg6c (sp : BitVec 64) :
    memRegion (sp + 0x3ec#64) 332 =
      (∃∗ u_3f0 : BitVec 64, ∃∗ u_3f8 : BitVec 64,
       ∃∗ u_400 : BitVec 64, ∃∗ u_408 : BitVec 64, ∃∗ u_3ec : BitVec 32,
        ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗ ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
        ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗ ((sp + 0x400#64) ↦₆₄ u_400) ∗
        ((sp + 0x408#64) ↦₆₄ u_408) ∗ memRegion (sp + 0x410#64) 296) := by
  have hc : memRegion (sp + 0x3f0#64) 32 = cells (sp + 0x3f0#64) 4 :=
    ProofLib.memRegion_cells (sp + 0x3f0#64) 4 (by decide)
  rw [ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 328)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 32) (k := 296)
        (b' := sp + 0x410#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four (sp + 0x3ec#64), hc]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem sp3e0_after_seg6c_full_entails
    (sp v0 u_3f0 u_3f8 u_400 u_408 : BitVec 64) (v8 u_3ec : BitVec 32) :
    ((sp + 0x3e0#64) ↦₆₄ v0) ∗ ((sp + 0x3e8#64) ↦₃₂ v8) ∗
    ((sp + 0x3ec#64) ↦₃₂ u_3ec) ∗ ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
    ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗ ((sp + 0x400#64) ↦₆₄ u_400) ∗
    ((sp + 0x408#64) ↦₆₄ u_408) ∗ memRegion (sp + 0x410#64) 296 ⊢
      memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336)
        (b' := sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 4) (k := 332)
        (b' := sp + 0x3ec#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3ec#64) (n := 4) (k := 328)
        (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320)
        (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312)
        (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304)
        (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296)
        (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))

theorem stackAt_promote_state_eq (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackAt (sp - 96#64) (allocHookStack - 96) ∗
      cells (sp - 96#64) 8 ∗
      cells (sp - 32#64) 4 := by
  have h1 : stackAt sp allocHookStack =
      stackAt (sp - 32#64) (allocHookStack - 32) ∗ cells (sp - 32#64) 4 :=
    ProofLib.stackAt_split_cells sp (allocHookStack - 32) 4 (by decide)
  have h2 : stackAt (sp - 32#64) (allocHookStack - 32) =
      stackAt (sp - 32#64 - 64#64) (allocHookStack - 96) ∗ cells (sp - 32#64 - 64#64) 8 :=
    ProofLib.stackAt_split_cells (sp - 32#64) (allocHookStack - 96) 8 (by decide)
  have hsub : sp - 32#64 - 64#64 = sp - 96#64 := by bv_omega
  rw [hsub] at h2
  rw [h1, h2, sepConj_assoc]

theorem coro658_298_eq (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x658#64) 298 =
      cells (coroPtr + 0x658#64) 37 ∗
      (∃∗ c_780 : BitVec 8, ((coroPtr + 0x780#64) ↦₈ c_780)) ∗
      (∃∗ c_781 : BitVec 8, ((coroPtr + 0x781#64) ↦₈ c_781)) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x658#64) (n := 296) (k := 2)
        (b' := coroPtr + 0x780#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := coroPtr + 0x780#64) (n := 1) (k := 1)
        (b' := coroPtr + 0x781#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (coroPtr + 0x658#64) 37 (by decide),
      memRegion_one (coroPtr + 0x780#64),
      memRegion_one (coroPtr + 0x781#64)]

end CryptoVerification.E2E.Pqxdh.ResponderClosure
