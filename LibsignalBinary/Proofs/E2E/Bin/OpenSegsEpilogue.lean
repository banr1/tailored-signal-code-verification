/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddresses
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Epilogue Segment Proof for `libsignal_e2e::open` (`0x43ca0..0x43d08`)

Proves segment 8 (`open_seg_epilogue'`, `+0x268..+0x2d0`) of `libsignal_e2e::open`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.InMem

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel}

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32 ProofLib.reduceStateReadReg

/-! ## Segment 8: `open_seg_epilogue'` (`+0x268..+0x2d0`, 26 insns) -/

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb'_append_lo_u64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

@[local simp, local arm64_norm, local wp_norm]
private theorem extractLsb'_append_hi_u64 (lo hi : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi_lt; simp [hi_lt]

private def words29At (base : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
     w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64) : SepProp :=
  (base ↦₆₄ w0) ∗ ((base + 8#64) ↦₆₄ w1) ∗ ((base + 16#64) ↦₆₄ w2) ∗ ((base + 24#64) ↦₆₄ w3) ∗
  ((base + 32#64) ↦₆₄ w4) ∗ ((base + 40#64) ↦₆₄ w5) ∗ ((base + 48#64) ↦₆₄ w6) ∗ ((base + 56#64) ↦₆₄ w7) ∗
  ((base + 64#64) ↦₆₄ w8) ∗ ((base + 72#64) ↦₆₄ w9) ∗ ((base + 80#64) ↦₆₄ w10) ∗ ((base + 88#64) ↦₆₄ w11) ∗
  ((base + 96#64) ↦₆₄ w12) ∗ ((base + 104#64) ↦₆₄ w13) ∗ ((base + 112#64) ↦₆₄ w14) ∗ ((base + 120#64) ↦₆₄ w15) ∗
  ((base + 128#64) ↦₆₄ w16) ∗ ((base + 136#64) ↦₆₄ w17) ∗ ((base + 144#64) ↦₆₄ w18) ∗ ((base + 152#64) ↦₆₄ w19) ∗
  ((base + 160#64) ↦₆₄ w20) ∗ ((base + 168#64) ↦₆₄ w21) ∗ ((base + 176#64) ↦₆₄ w22) ∗ ((base + 184#64) ↦₆₄ w23) ∗
  ((base + 192#64) ↦₆₄ w24) ∗ ((base + 200#64) ↦₆₄ w25) ∗ ((base + 208#64) ↦₆₄ w26) ∗ ((base + 216#64) ↦₆₄ w27) ∗
  ((base + 224#64) ↦₆₄ w28)

private def openSavedRegsSpAt (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp + 912#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp + 920#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp + 928#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp + 936#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp + 944#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp + 952#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp + 960#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp + 968#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp + 976#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp + 984#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp + 992#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp + 1000#64) ↦₆₄ s0.readReg64 .x19)

private theorem openSavedRegsAt_eq_sp (s0 : State) (sp : BitVec 64) (hsp : sp = s0.sp - 0x3f0#64) :
    openSavedRegsAt s0 = openSavedRegsSpAt sp s0 := by
  subst hsp; unfold openSavedRegsAt openSavedRegsSpAt
  have h1 : s0.sp - 0x3f0#64 + 912#64 = s0.sp - 0x60#64 := by bv_lin
  have h2 : s0.sp - 0x3f0#64 + 920#64 = s0.sp - 0x58#64 := by bv_lin
  have h3 : s0.sp - 0x3f0#64 + 928#64 = s0.sp - 0x50#64 := by bv_lin
  have h4 : s0.sp - 0x3f0#64 + 936#64 = s0.sp - 0x48#64 := by bv_lin
  have h5 : s0.sp - 0x3f0#64 + 944#64 = s0.sp - 0x40#64 := by bv_lin
  have h6 : s0.sp - 0x3f0#64 + 952#64 = s0.sp - 0x38#64 := by bv_lin
  have h7 : s0.sp - 0x3f0#64 + 960#64 = s0.sp - 0x30#64 := by bv_lin
  have h8 : s0.sp - 0x3f0#64 + 968#64 = s0.sp - 0x28#64 := by bv_lin
  have h9 : s0.sp - 0x3f0#64 + 976#64 = s0.sp - 0x20#64 := by bv_lin
  have h10 : s0.sp - 0x3f0#64 + 984#64 = s0.sp - 0x18#64 := by bv_lin
  have h11 : s0.sp - 0x3f0#64 + 992#64 = s0.sp - 0x10#64 := by bv_lin
  have h12 : s0.sp - 0x3f0#64 + 1000#64 = s0.sp - 0x08#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem spAligned_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).spAligned = s.spAligned := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem sp_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg) :
    (s.writeVReg128 r v).readReg64 reg = s.readReg64 reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) (reg : Reg) :
    (s.writeVReg128 r v).readReg32 reg = s.readReg32 reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) (w : RegWidth) (reg : Reg) :
    (s.writeVReg128 r v).readReg w reg = s.readReg w reg := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).tpidrEl0 = s.tpidrEl0 := rfl
@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem trace_writeVReg128_3 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_writeReg32_gpr0 (s : State) (v : BitVec 32) :
    (s.writeReg32 (Reg.gpr 0#5) v).readReg64 (Reg.gpr 0#5) = v.zeroExtend 64 := rfl
@[local simp, local arm64_norm, local wp_norm]
private theorem readReg64_writeReg_w32_gpr0 (s : State) (v : BitVec 64) :
    (s.writeReg .W32 (Reg.gpr 0#5) v).readReg64 (Reg.gpr 0#5) = (v.truncate 32).zeroExtend 64 := rfl

private theorem pointsTo8_memRegion7_eq_words1 (addr : BitVec 64) (dev : BitVec 8) :
    ((addr + 24#64) ↦₈ dev) ∗ memRegion (addr + 25#64) 7 =
      ∃∗ pad : List (BitVec 8), ∃∗ w : BitVec 64,
        ⌜pad.length = 7 ∧ dev :: pad = unpack64 w⌝ ∗ ((addr + 24#64) ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (addr + 25#64) 7 (by decide), sepExists_sepConj_right]
  apply RawByteMove.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro pad; rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpad
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := dev :: pad) (by simp [hpad])
    have hcons : ((addr + 24#64) ↦₈ dev) ∗ ((addr + 25#64) ↦ₛ pad) = ((addr + 24#64) ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, BitVec.add_assoc]; rfl
    rw [hcons]
    exact Entails.sepExists_right pad (Entails.sepExists_right w (Entails.pure_right ⟨hpad, hw⟩ (Entails.refl _)))
  · apply Entails.sepExists_elim; intro pad; apply Entails.sepExists_elim; intro w
    apply Entails.pure_left; rintro ⟨hpad, hw⟩
    have hcons : ((addr + 24#64) ↦₈ dev) ∗ ((addr + 25#64) ↦ₛ pad) = ((addr + 24#64) ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, BitVec.add_assoc]; rfl
    rw [← hcons]; refine Entails.sepExists_right pad ?_
    rw [sepConj_pure_left_comm]; exact Entails.pure_right hpad (Entails.refl _)

private theorem pointsTo32_memRegion4_eq_words1 (addr : BitVec 64) (v : BitVec 32) :
    ((addr + 112#64) ↦₃₂ v) ∗ memRegion (addr + 116#64) 4 =
      ∃∗ pad : List (BitVec 8), ∃∗ w : BitVec 64,
        ⌜pad.length = 4 ∧ unpack32 v ++ pad = unpack64 w⌝ ∗ ((addr + 112#64) ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (addr + 116#64) 4 (by decide), sepExists_sepConj_right]
  apply RawByteMove.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro pad; rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpad
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 (bs := unpack32 v ++ pad) (by simp [hpad])
    have happ : ((addr + 112#64) ↦₃₂ v) ∗ ((addr + 116#64) ↦ₛ pad) = ((addr + 112#64) ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes, ← hw, pointsTo32_eq_pointsToBytes,
          pointsToBytes_append, unpack32_length, BitVec.add_assoc]; rfl
    rw [happ]
    exact Entails.sepExists_right pad (Entails.sepExists_right w (Entails.pure_right ⟨hpad, hw⟩ (Entails.refl _)))
  · apply Entails.sepExists_elim; intro pad; apply Entails.sepExists_elim; intro w
    apply Entails.pure_left; rintro ⟨hpad, hw⟩
    have happ : ((addr + 112#64) ↦₃₂ v) ∗ ((addr + 116#64) ↦ₛ pad) = ((addr + 112#64) ↦₆₄ w) := by
      rw [pointsTo64_eq_pointsToBytes, ← hw, pointsTo32_eq_pointsToBytes,
          pointsToBytes_append, unpack32_length, BitVec.add_assoc]; rfl
    rw [← happ]; refine Entails.sepExists_right pad ?_
    rw [sepConj_pure_left_comm]; exact Entails.pure_right hpad (Entails.refl _)

private theorem exists_keyPairBytes_words8 (role : Role) :
    ∃ w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64, ∀ a : BitVec 64,
      ((a + 48#64) ↦ₛ role.keyPairBytes) =
        ((a + 48#64) ↦₆₄ w20) ∗ ((a + 56#64) ↦₆₄ w21) ∗ ((a + 64#64) ↦₆₄ w22) ∗ ((a + 72#64) ↦₆₄ w23) ∗
        ((a + 80#64) ↦₆₄ w24) ∗ ((a + 88#64) ↦₆₄ w25) ∗ ((a + 96#64) ↦₆₄ w26) ∗ ((a + 104#64) ↦₆₄ w27) := by
  have hlen : role.keyPairBytes.length = 64 := by cases role <;> decide
  obtain ⟨w20, w21, w22, w23, _, h1⟩ := exists_unpack64_of_length_32 (bs := role.keyPairBytes.take 32) (by simp [hlen])
  obtain ⟨w24, w25, w26, w27, _, h2⟩ := exists_unpack64_of_length_32 (bs := role.keyPairBytes.drop 32) (by simp [hlen])
  refine ⟨w20, w21, w22, w23, w24, w25, w26, w27, fun a => ?_⟩
  rw [pointsToBytes_take_drop (a + 48#64) 32 role.keyPairBytes (by omega),
      h1 (a + 48#64), h2 (a + 48#64 + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private def table4SingleHeapAt (A : RustAlloc) (stride : Nat) (ctrl k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) : SepProp :=
  let cbs := InMem.HashbrownModel.singleCtrl4 k (InMem.HashbrownModel.h2Tag (InMem.SipHashModel.hashAddrBv k0 k1 peerName peerDev))
  ⌜k < 4 ∧ (ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧ 4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
    (([k] : List Nat).length = 4 → 2#64 = 0#64) ∧
    InMem.HashbrownModel.CtrlMirrorInv 3#64 cbs ∧ InMem.HashbrownModel.FullBucketsInv 3#64 cbs [k])⌝ ∗
  A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (InMem.HashbrownBin.tableAllocSize 4 stride) (asm% hashbrownTableAlign) ∗
  (ctrl ↦ₛ cbs) ∗
  arrayAt (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
    (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse

private theorem table4SingleAt_eq_words6 (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8) (entryAt : BitVec 64 → SepProp) :
    InMem.HashbrownBin.table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt =
      ∃∗ ctrl : BitVec 64,
        ((mp ↦₆₄ ctrl) ∗ ((mp + 8#64) ↦₆₄ 3#64) ∗ ((mp + 16#64) ↦₆₄ 2#64) ∗
         ((mp + 24#64) ↦₆₄ 1#64) ∗ ((mp + 32#64) ↦₆₄ k0) ∗ ((mp + 40#64) ↦₆₄ k1)) ∗
        table4SingleHeapAt A stride ctrl k0 k1 k peerName peerDev entryAt := by
  unfold InMem.HashbrownBin.table4SingleAt InMem.HashbrownBin.table4At table4SingleHeapAt
  rw [sepExists_sepConj_right]; apply RawByteMove.sepExists_congr; intro ctrl
  rw [← sepConj_assoc, ← RawByteMove.pure_and_eq_sepConj]
  simp only [List.length_singleton, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

private theorem protocolAddressAt_eq_words4 (A : RustAlloc) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A g a =
      ∃∗ pad : List (BitVec 8), ∃∗ w : BitVec 64,
        ((a ↦₆₄ g.name.cap) ∗ ((a + 8#64) ↦₆₄ g.name.ptr) ∗
         ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗ ((a + 24#64) ↦₆₄ w)) ∗
        (⌜pad.length = 7 ∧ g.device :: pad = unpack64 w⌝ ∗ RawByteMove.vecGhostHeap A g.name) := by
  unfold protocolAddressAt vecGhostAt RawByteMove.vecGhostHeap
  rw [vecU8At_eq_header_sep_buf, pointsTo8_memRegion7_eq_words1]; dsimp only [vecHeader]
  simp only [sepExists_sepConj_right]
  apply RawByteMove.sepExists_congr; intro pad; apply RawByteMove.sepExists_congr; intro w; ac_rfl

private theorem protocolAddressAt_reloc4 (A : RustAlloc) (g : AddrGhost) (a : BitVec 64)
    {m : Memory} {R : SepProp} (hm : m ⊨ protocolAddressAt A g a ∗ R) :
    ∃ (w0 w1 w2 w3 : BitVec 64) (H : SepProp),
      (m ⊨ ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        (((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗ ((dst + 24#64) ↦₆₄ w3)) ∗ H) ⊢
          protocolAddressAt A g dst) := by
  rw [protocolAddressAt_eq_words4 A g a, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨pad, hm⟩; rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨w, hm⟩
  refine ⟨g.name.cap, g.name.ptr, BitVec.ofNat 64 g.name.bytes.length, w,
    ⌜pad.length = 7 ∧ g.device :: pad = unpack64 w⌝ ∗ RawByteMove.vecGhostHeap A g.name,
    by ac_sat hm, fun dst => ?_⟩
  rw [protocolAddressAt_eq_words4 A g dst]
  exact Entails.sepExists_right pad (Entails.sepExists_right w (Entails.refl _))

private theorem inMemSessionStoreAt_reloc6 (A : RustAlloc) (img : Obj.Image)
    (a : BitVec 64) (peer : Role) (sess : Session (List (BitVec 8)))
    {m : Memory} {R : SepProp} (hm : m ⊨ inMemSessionStoreAt A img a peer (some sess) ∗ R) :
    ∃ (w8 w9 w10 w11 w12 w13 : BitVec 64) (H : SepProp),
      (m ⊨ ((a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w9) ∗ ((a + 16#64) ↦₆₄ w10) ∗
            ((a + 24#64) ↦₆₄ w11) ∗ ((a + 32#64) ↦₆₄ w12) ∗ ((a + 40#64) ↦₆₄ w13)) ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        (((dst ↦₆₄ w8) ∗ ((dst + 8#64) ↦₆₄ w9) ∗ ((dst + 16#64) ↦₆₄ w10) ∗
          ((dst + 24#64) ↦₆₄ w11) ∗ ((dst + 32#64) ↦₆₄ w12) ∗ ((dst + 40#64) ↦₆₄ w13)) ∗ H) ⊢
          inMemSessionStoreAt A img dst peer (some sess)) := by
  dsimp only [inMemSessionStoreAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨k0, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨k1, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨idx, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨gAddr, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨G, hm⟩
  rw [table4SingleAt_eq_words6, sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨ctrl, hm⟩
  refine ⟨ctrl, 3#64, 2#64, 1#64, k0, k1,
    ⌜gAddr.val = peer.addrVal ∧ BinCanonSession G sess⌝ ∗
      table4SingleHeapAt A InMem.HashbrownBin.sessionBucketStride ctrl k0 k1 idx peer.nameBytes 1#8
        (fun b => protocolAddressAt A gAddr b ∗
          sessionRecordAt A (b + asm64% InMem.HashbrownBin.sessionBucketValueOff) ⟨0#64, 8#64, some G⟩ ⟨some sess⟩),
    by ac_sat hm, fun dst => ?_⟩
  unfold inMemSessionStoreAt
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.sepExists_right idx
    (Entails.sepExists_right gAddr (Entails.sepExists_right G ?_))))
  rw [table4SingleAt_eq_words6, sepExists_sepConj_right]
  exact Entails.sepExists_right ctrl (Entails.of_eq (by ac_rfl))

private theorem inMemIdentityStoreAt_reloc15 (A : RustAlloc) (img : Obj.Image)
    (a : BitVec 64) (role : Role) (ik : IdentityKey)
    {m : Memory} {R : SepProp} (hm : m ⊨ inMemIdentityStoreAt A img a role (some ik) ∗ R) :
    ∃ (w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64) (H : SepProp),
      (m ⊨ (((a ↦₆₄ w14) ∗ ((a + 8#64) ↦₆₄ w15) ∗ ((a + 16#64) ↦₆₄ w16) ∗
             ((a + 24#64) ↦₆₄ w17) ∗ ((a + 32#64) ↦₆₄ w18) ∗ ((a + 40#64) ↦₆₄ w19)) ∗
            (((a + 48#64) ↦₆₄ w20) ∗ ((a + 56#64) ↦₆₄ w21) ∗ ((a + 64#64) ↦₆₄ w22) ∗ ((a + 72#64) ↦₆₄ w23) ∗
             ((a + 80#64) ↦₆₄ w24) ∗ ((a + 88#64) ↦₆₄ w25) ∗ ((a + 96#64) ↦₆₄ w26) ∗ ((a + 104#64) ↦₆₄ w27)) ∗
            ((a + 112#64) ↦₆₄ w28)) ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        ((((dst ↦₆₄ w14) ∗ ((dst + 8#64) ↦₆₄ w15) ∗ ((dst + 16#64) ↦₆₄ w16) ∗
           ((dst + 24#64) ↦₆₄ w17) ∗ ((dst + 32#64) ↦₆₄ w18) ∗ ((dst + 40#64) ↦₆₄ w19)) ∗
          (((dst + 48#64) ↦₆₄ w20) ∗ ((dst + 56#64) ↦₆₄ w21) ∗ ((dst + 64#64) ↦₆₄ w22) ∗ ((dst + 72#64) ↦₆₄ w23) ∗
           ((dst + 80#64) ↦₆₄ w24) ∗ ((dst + 88#64) ↦₆₄ w25) ∗ ((dst + 96#64) ↦₆₄ w26) ∗ ((dst + 104#64) ↦₆₄ w27)) ∗
          ((dst + 112#64) ↦₆₄ w28)) ∗ H) ⊢
          inMemIdentityStoreAt A img dst role (some ik)) := by
  obtain ⟨w20, w21, w22, w23, w24, w25, w26, w27, hkp⟩ := exists_keyPairBytes_words8 role
  dsimp only [inMemIdentityStoreAt] at hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨k0, hm⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨k1, hm⟩
  have hm1 : m ⊨ (((a + 112#64) ↦₃₂ 0#32) ∗ memRegion (a + 116#64) 4) ∗
      (((a + 48#64) ↦ₛ role.keyPairBytes) ∗
       (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost, ⌜gAddr.val = role.peer.addrVal⌝ ∗
         InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride a k0 k1 idx role.peer.nameBytes 1#8
           (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) ∗ R) := by ac_sat hm
  rw [pointsTo32_memRegion4_eq_words1 a 0#32, sepExists_sepConj_left, satisfies_sepExists] at hm1
  rcases hm1 with ⟨pad, hm1⟩; rw [sepExists_sepConj_left, satisfies_sepExists] at hm1; rcases hm1 with ⟨w28, hm1⟩
  have hm2 : m ⊨ (∃∗ idx : Nat, ∃∗ gAddr : AddrGhost, ⌜gAddr.val = role.peer.addrVal⌝ ∗
      InMem.HashbrownBin.table4SingleAt A InMem.HashbrownBin.identityBucketStride a k0 k1 idx role.peer.nameBytes 1#8
        (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList)) ∗
      ((⌜pad.length = 4 ∧ unpack32 0#32 ++ pad = unpack64 w28⌝ ∗ ((a + 112#64) ↦₆₄ w28)) ∗
       ((a + 48#64) ↦ₛ role.keyPairBytes) ∗ R) := by ac_sat hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2; rcases hm2 with ⟨idx, hm2⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2; rcases hm2 with ⟨gAddr, hm2⟩
  rw [table4SingleAt_eq_words6, sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at hm2
  rcases hm2 with ⟨ctrl, hm2⟩; rw [hkp a] at hm2
  refine ⟨ctrl, 3#64, 2#64, 1#64, k0, k1, w20, w21, w22, w23, w24, w25, w26, w27, w28,
    ⌜pad.length = 4 ∧ unpack32 0#32 ++ pad = unpack64 w28⌝ ∗ ⌜gAddr.val = role.peer.addrVal⌝ ∗
      table4SingleHeapAt A InMem.HashbrownBin.identityBucketStride ctrl k0 k1 idx role.peer.nameBytes 1#8
        (InMem.HashbrownBin.identityBucketEntryAt A gAddr ik.publicKey.bytes.toList),
    by ac_sat hm2, fun dst => ?_⟩
  unfold inMemIdentityStoreAt
  refine Entails.sepExists_right k0 (Entails.sepExists_right k1 ?_)
  rw [← sepConj_assoc ((dst + 112#64) ↦₃₂ 0#32), pointsTo32_memRegion4_eq_words1 dst 0#32, hkp dst]
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right pad ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; refine Entails.sepExists_right w28 ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; refine Entails.sepExists_right idx ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]; refine Entails.sepExists_right gAddr ?_
  rw [table4SingleAt_eq_words6, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  exact Entails.sepExists_right ctrl (Entails.of_eq (by ac_rfl))

private theorem callWords29_eq (ptr : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
     w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64) :
    ((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗ ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3)) ∗
    (((ptr + 0x20#64) ↦₆₄ w4) ∗ ((ptr + 0x20#64 + 8#64) ↦₆₄ w5) ∗
     ((ptr + 0x20#64 + 16#64) ↦₆₄ w6) ∗ ((ptr + 0x20#64 + 24#64) ↦₆₄ w7)) ∗
    (((ptr + 0x40#64) ↦₆₄ w8) ∗ ((ptr + 0x40#64 + 8#64) ↦₆₄ w9) ∗
     ((ptr + 0x40#64 + 16#64) ↦₆₄ w10) ∗ ((ptr + 0x40#64 + 24#64) ↦₆₄ w11) ∗
     ((ptr + 0x40#64 + 32#64) ↦₆₄ w12) ∗ ((ptr + 0x40#64 + 40#64) ↦₆₄ w13)) ∗
    ((((ptr + 0x70#64) ↦₆₄ w14) ∗ ((ptr + 0x70#64 + 8#64) ↦₆₄ w15) ∗
      ((ptr + 0x70#64 + 16#64) ↦₆₄ w16) ∗ ((ptr + 0x70#64 + 24#64) ↦₆₄ w17) ∗
      ((ptr + 0x70#64 + 32#64) ↦₆₄ w18) ∗ ((ptr + 0x70#64 + 40#64) ↦₆₄ w19)) ∗
     (((ptr + 0x70#64 + 48#64) ↦₆₄ w20) ∗ ((ptr + 0x70#64 + 56#64) ↦₆₄ w21) ∗
      ((ptr + 0x70#64 + 64#64) ↦₆₄ w22) ∗ ((ptr + 0x70#64 + 72#64) ↦₆₄ w23) ∗
      ((ptr + 0x70#64 + 80#64) ↦₆₄ w24) ∗ ((ptr + 0x70#64 + 88#64) ↦₆₄ w25) ∗
      ((ptr + 0x70#64 + 96#64) ↦₆₄ w26) ∗ ((ptr + 0x70#64 + 104#64) ↦₆₄ w27)) ∗
     ((ptr + 0x70#64 + 112#64) ↦₆₄ w28)) =
    words29At ptr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
      w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 := by
  unfold words29At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem openSeam268_decomp_words29 (A : RustAlloc) (img : Obj.Image) (ptr : BitVec 64)
    (role : Role) (sess : Session (List (BitVec 8))) {m : Memory} {R : SepProp}
    (hm : m ⊨ ((∃∗ gMe : AddrGhost, ∃∗ gPeer : AddrGhost,
        ⌜gMe.val = role.addrVal ∧ gPeer.val = role.peer.addrVal⌝ ∗
          protocolAddressAt A gMe ptr ∗ protocolAddressAt A gPeer (ptr + 0x20#64)) ∗
      inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some sess) ∗
      inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey)) ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
       w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64) (H : SepProp),
      (m ⊨ words29At ptr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
             w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 ∗ H ∗ R) ∧
      (∀ dst : BitVec 64,
        (words29At dst w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
           w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 ∗ H) ⊢
          callAt A img dst role sess) := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨gMe, hm⟩
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm; rcases hm with ⟨gPeer, hm⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm; rcases hm with ⟨⟨hMe, hPeer⟩, hm⟩
  have hMeLen : gMe.name.bytes.length = 36 := by injection hMe with h1 _; rw [h1]; exact role_nameBytes_length role
  have hPeerLen : gPeer.name.bytes.length = 36 := by injection hPeer with h1 _; rw [h1]; exact role_nameBytes_length role.peer
  obtain ⟨w0, w1, w2, w3, H1, hm, hF1⟩ := protocolAddressAt_reloc4 A gMe ptr hm
  have hm_p2 : m ⊨ protocolAddressAt A gPeer (ptr + 0x20#64) ∗
      (((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗ ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3)) ∗
       H1 ∗ inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some sess) ∗
       inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗ R) := by ac_sat hm
  obtain ⟨w4, w5, w6, w7, H2, hm, hF2⟩ := protocolAddressAt_reloc4 A gPeer (ptr + 0x20#64) hm_p2
  have hm_s : m ⊨ inMemSessionStoreAt A img (ptr + 0x40#64) role.peer (some sess) ∗
      (((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗ ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3)) ∗
       (((ptr + 0x20#64) ↦₆₄ w4) ∗ ((ptr + 0x20#64 + 8#64) ↦₆₄ w5) ∗
        ((ptr + 0x20#64 + 16#64) ↦₆₄ w6) ∗ ((ptr + 0x20#64 + 24#64) ↦₆₄ w7)) ∗
       H1 ∗ H2 ∗ inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗ R) := by ac_sat hm
  obtain ⟨w8, w9, w10, w11, w12, w13, H3, hm, hF3⟩ :=
    inMemSessionStoreAt_reloc6 A img (ptr + 0x40#64) role.peer sess hm_s
  have hm_i : m ⊨ inMemIdentityStoreAt A img (ptr + 0x70#64) role (some role.peer.idKey) ∗
      (((ptr ↦₆₄ w0) ∗ ((ptr + 8#64) ↦₆₄ w1) ∗ ((ptr + 16#64) ↦₆₄ w2) ∗ ((ptr + 24#64) ↦₆₄ w3)) ∗
       (((ptr + 0x20#64) ↦₆₄ w4) ∗ ((ptr + 0x20#64 + 8#64) ↦₆₄ w5) ∗
        ((ptr + 0x20#64 + 16#64) ↦₆₄ w6) ∗ ((ptr + 0x20#64 + 24#64) ↦₆₄ w7)) ∗
       (((ptr + 0x40#64) ↦₆₄ w8) ∗ ((ptr + 0x40#64 + 8#64) ↦₆₄ w9) ∗
        ((ptr + 0x40#64 + 16#64) ↦₆₄ w10) ∗ ((ptr + 0x40#64 + 24#64) ↦₆₄ w11) ∗
        ((ptr + 0x40#64 + 32#64) ↦₆₄ w12) ∗ ((ptr + 0x40#64 + 40#64) ↦₆₄ w13)) ∗
       H1 ∗ H2 ∗ H3 ∗ R) := by ac_sat hm
  obtain ⟨w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, H4, hm, hF4⟩ :=
    inMemIdentityStoreAt_reloc15 A img (ptr + 0x70#64) role role.peer.idKey hm_i
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28,
    H1 ∗ H2 ∗ H3 ∗ H4, ?_, fun dst => ?_⟩
  · rw [← callWords29_eq]; ac_sat hm
  · unfold callAt
    refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
    apply Entails.pure_right ⟨hMe, hPeer, hMeLen, hPeerLen⟩
    rw [← callWords29_eq]
    refine Entails.trans ?_ (sepConj_mono (hF1 dst) (sepConj_mono (hF2 (dst + 0x20#64))
      (sepConj_mono (hF3 (dst + 0x40#64)) (hF4 (dst + 0x70#64)))))
    exact Entails.of_eq (by ac_rfl)

private theorem words29At_entails_memRegion (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
     w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : BitVec 64) :
    words29At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
      w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 ⊢ memRegion a 232 := by
  rw [show (232 : Nat) = 8 * 29 by rfl, ProofLib.memRegion_cells a 29 (by decide)]
  unfold words29At
  simp only [ProofLib.cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5
    (Entails.sepExists_right w6 (Entails.sepExists_right w7 (Entails.sepExists_right w8
    (Entails.sepExists_right w9 (Entails.sepExists_right w10 (Entails.sepExists_right w11
    (Entails.sepExists_right w12 (Entails.sepExists_right w13 (Entails.sepExists_right w14
    (Entails.sepExists_right w15 (Entails.sepExists_right w16 (Entails.sepExists_right w17
    (Entails.sepExists_right w18 (Entails.sepExists_right w19 (Entails.sepExists_right w20
    (Entails.sepExists_right w21 (Entails.sepExists_right w22 (Entails.sepExists_right w23
    (Entails.sepExists_right w24 (Entails.sepExists_right w25 (Entails.sepExists_right w26
    (Entails.sepExists_right w27 (Entails.sepExists_right w28 (Entails.refl _)))))))))))))))))))))))))))))

private theorem memRegion_232_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 232 ∗ R) :
    ∃ o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14
      o15 o16 o17 o18 o19 o20 o21 o22 o23 o24 o25 o26 o27 o28 : BitVec 64,
      m ⊨ words29At a o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14
            o15 o16 o17 o18 o19 o20 o21 o22 o23 o24 o25 o26 o27 o28 ∗ R := by
  rw [show (232 : Nat) = 8 * 29 by rfl, ProofLib.memRegion_cells a 29 (by decide)] at hm
  simp only [ProofLib.cells, words29At, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd, satisfies_sepExists] at hm ⊢
  exact hm

private theorem memRegion_open_0x390_join (sp : BitVec 64) :
    memRegion sp 0x170 ∗ memRegion (sp + 0x170#64) 232 ∗ memRegion (sp + 0x258#64) 0x138 =
      memRegion sp 0x390 := by
  rw [← memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x258#64)
        (N := 0x220) (n := 232) (k := 0x138) (by decide) (by bv_lin) (by decide),
      ← memRegion_split' (b := sp) (b' := sp + 0x170#64)
        (N := 0x390) (n := 0x170) (k := 0x220) (by decide) (by bv_lin) (by decide)]

variable (C : Crypto) (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (ctl : BitVec 64)
  (abs : String → Option (State → State))

end CryptoVerification.E2E.Bin
