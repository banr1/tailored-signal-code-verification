/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.OpenEmptyPrefix
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddresses
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.StoreNew.Proof

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux
open ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
open CryptoVerification.E2E.InMem

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")


/-! ## Segment 2 Composition (`+0x0bc..+0x1b8`) -/

theorem stackAt_160_eq_cells_8_12 (sp : BitVec 64) :
    stackAt sp 160 = cells (sp - 160#64) 8 ∗ cells (sp - 96#64) 12 := by
  dsimp only [stackAt]
  rw [memRegion_split' (b := sp - 160#64) (b' := sp - 96#64)
        (N := 160) (n := 64) (k := 96) (by decide) (by bv_lin) (by decide),
      ProofLib.memRegion_cells (sp - 160#64) 8 (by decide),
      ProofLib.memRegion_cells (sp - 96#64) 12 (by decide)]

theorem memRegion_32_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ d0 d1 d2 d3 : BitVec 64,
      m ⊨ ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3)) ∗ R := by
  rw [memRegion_32_four_64 a] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at hm ⊢
  rcases hm with ⟨d3, d2, d1, d0, hm⟩
  exact ⟨d0, d1, d2, d3, hm⟩

theorem memRegion_64_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 64 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 64,
      m ⊨ ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ∗
            ((a + 32#64) ↦₆₄ d4) ∗ ((a + 40#64) ↦₆₄ d5) ∗ ((a + 48#64) ↦₆₄ d6) ∗ ((a + 56#64)
              ↦₆₄ d7)) ∗ R := by
  rw [memRegion_split' (b := a) (b' := a + 32#64)
    (N := 64) (n := 32) (k := 32) (by decide) rfl (by decide),
      sepConj_assoc] at hm
  obtain ⟨d0, d1, d2, d3, hm1⟩ := memRegion_32_elim a hm
  have hm2 : m ⊨ memRegion (a + 32#64) 32 ∗
      (((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3)) ∗ R) := by
    ac_sat hm1
  obtain ⟨d4, d5, d6, d7, hm3⟩ := memRegion_32_elim (a + 32#64) hm2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm3
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, by ac_sat hm3⟩

theorem exists_words8_of_length_64 {bs : List (BitVec 8)} (hlen : bs.length = 64) :
    ∃ k0 k1 k2 k3 k4 k5 k6 k7 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ k0) ∗ ((a + 8#64) ↦₆₄ k1) ∗ ((a + 16#64) ↦₆₄ k2) ∗ ((a + 24#64) ↦₆₄ k3) ∗
        ((a + 32#64) ↦₆₄ k4) ∗ ((a + 40#64) ↦₆₄ k5) ∗ ((a + 48#64) ↦₆₄ k6) ∗ ((a + 56#64) ↦₆₄
          k7) := by
  obtain ⟨k0, k1, k2, k3, _, h1⟩ := exists_unpack64_of_length_32 (bs := bs.take 32) (by simp [hlen])
  obtain ⟨k4, k5, k6, k7, _, h2⟩ := exists_unpack64_of_length_32 (bs := bs.drop 32) (by simp [hlen])
  refine ⟨k0, k1, k2, k3, k4, k5, k6, k7, fun a => ?_⟩
  rw [pointsToBytes_take_drop a 32 bs (by omega), h1 a, h2 (a + 32#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem memRegion_32_addr_elim (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 32 ∗ R) :
    ∃ (m0 m1 m2 : BitVec 64) (mb : BitVec 8),
      m ⊨ ((a ↦₆₄ m0) ∗ ((a + 8#64) ↦₆₄ m1) ∗ ((a + 16#64) ↦₆₄ m2) ∗
            ((a + 24#64) ↦₈ mb) ∗ memRegion (a + 25#64) 7) ∗ R := by
  rw [memRegion_split' (b := a) (b' := a + 8#64)
    (N := 32) (n := 8) (k := 24) (by decide) rfl (by decide),
      memRegion_split' (b := a + 8#64) (b' := a + 16#64)
        (N := 24) (n := 8) (k := 16) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := a + 16#64) (b' := a + 24#64)
        (N := 16) (n := 8) (k := 8) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := a + 24#64) (b' := a + 25#64)
        (N := 8) (n := 1) (k := 7) (by decide) (by bv_lin) (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_one (a + 24#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc] at hm ⊢
  rcases hm with ⟨mb, m2, m1, m0, hm⟩
  exact ⟨m0, m1, m2, mb, hm⟩

theorem memRegion_openP_0x450_split (sp : BitVec 64) :
    memRegion sp 0x450 =
      memRegion sp 8 ∗
      memRegion (sp + 0x008#64) 32 ∗
      memRegion (sp + 0x028#64) 32 ∗
      memRegion (sp + 0x048#64) 48 ∗
      memRegion (sp + 0x078#64) 120 ∗
      memRegion (sp + 240#64) 32 ∗
      memRegion (sp + 272#64) 336 ∗
      memRegion (sp + 608#64) 65 ∗
      memRegion (sp + 673#64) 367 ∗
      memRegion (sp + 1040#64) 64 := by
  rw [memRegion_split' (b := sp) (b' := sp + 0x008#64)
    (N := 0x450) (n := 8) (k := 1096) (by decide) rfl (by decide),
      memRegion_split' (b := sp + 0x008#64) (b' := sp + 0x028#64)
        (N := 1096) (n := 32) (k := 1064) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x028#64) (b' := sp + 0x048#64)
        (N := 1064) (n := 32) (k := 1032) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x048#64) (b' := sp + 0x078#64)
        (N := 1032) (n := 48) (k := 984) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 0x078#64) (b' := sp + 240#64)
        (N := 984) (n := 120) (k := 864) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 240#64) (b' := sp + 272#64)
        (N := 864) (n := 32) (k := 832) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 272#64) (b' := sp + 608#64)
        (N := 832) (n := 336) (k := 496) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 608#64) (b' := sp + 673#64)
        (N := 496) (n := 65) (k := 431) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 673#64) (b' := sp + 1040#64)
        (N := 431) (n := 367) (k := 64) (by decide) (by bv_lin) (by decide)]

theorem memRegion_openP_0x0f0_join (sp : BitVec 64) (bs32 bs64_1 bs64_2 : List (BitVec 8))
    (b0 : BitVec 8) (h32 : bs32.length = 32) (h64_1 : bs64_1.length = 64) (h64_2 : bs64_2.length =
      64) :
    (((sp + 240#64) ↦ₛ bs32) ∗
     memRegion (sp + 272#64) 336 ∗
     ((sp + 608#64) ↦₈ b0) ∗ ((sp + 609#64) ↦ₛ bs64_1) ∗
     memRegion (sp + 673#64) 367 ∗
     ((sp + 1040#64) ↦ₛ bs64_2)) ⊢
      memRegion (sp + 0x0f0#64) 0x360 := by
  have he1 : ((sp + 240#64) ↦ₛ bs32) ⊢ memRegion (sp + 240#64) 32 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 240#64) bs32; rwa [h32] at h
  have he2 : (((sp + 608#64) ↦₈ b0) ∗ ((sp + 609#64) ↦ₛ bs64_1)) ⊢ memRegion (sp + 608#64) 65 := by
    have h1 := pointsTo8_entails_memRegion (sp + 608#64) b0
    have h2 : ((sp + 609#64) ↦ₛ bs64_1) ⊢ memRegion (sp + 609#64) 64 := by
      have h := ProofLib.pointsToBytes_entails_memRegion (sp + 609#64) bs64_1; rwa [h64_1] at h
    rw [memRegion_split' (b := sp + 608#64) (b' := sp + 609#64)
      (N := 65) (n := 1) (k := 64) (by decide) (by bv_lin) (by decide)]
    exact sepConj_mono h1 h2
  have he3 : ((sp + 1040#64) ↦ₛ bs64_2) ⊢ memRegion (sp + 1040#64) 64 := by
    have h := ProofLib.pointsToBytes_entails_memRegion (sp + 1040#64) bs64_2; rwa [h64_2] at h
  change _ ⊢ memRegion (sp + 240#64) 864
  rw [memRegion_split' (b := sp + 240#64) (b' := sp + 272#64)
    (N := 864) (n := 32) (k := 832) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 272#64) (b' := sp + 608#64)
        (N := 832) (n := 336) (k := 496) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 608#64) (b' := sp + 673#64)
        (N := 496) (n := 65) (k := 431) (by decide) (by bv_lin) (by decide),
      memRegion_split' (b := sp + 673#64) (b' := sp + 1040#64)
        (N := 431) (n := 367) (k := 64) (by decide) (by bv_lin) (by decide)]
  refine sepConj_mono he1 (sepConj_mono (Entails.refl _) ?_)
  rw [← sepConj_assoc ((sp + 608#64) ↦₈ b0)]
  exact sepConj_mono he2 (sepConj_mono (Entails.refl _) he3)

theorem protocolAddressAt_of_addr_write (A : RustAlloc) (r : Role) (ptr a : BitVec 64)
    (hptr : ptr ≠ 0#64) :
    ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
     ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
     (ptr ↦ₛ r.nameBytes) ∗ A.live ptr 36 1) ⊢
      protocolAddressAt A ⟨⟨36#64, ptr, r.nameBytes⟩, 1#8⟩ a := by
  have hlen : r.nameBytes.length = 36 := role_nameBytes_length r
  have hcap_ne : (36#64 : BitVec 64) ≠ 0#64 := by decide
  unfold protocolAddressAt vecGhostAt vecU8At RustHeap.vecHeader
  simp only [hlen, hcap_ne, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜36 ≤ 36 ∧ 36 < 9223372036854775808 ∧ ptr ≠ 0#64⌝ ∗
      ((a ↦₆₄ 36#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 36#64) ∗
       ((a + 24#64) ↦₈ 1#8) ∗ memRegion (a + 25#64) 7 ∗
       (ptr ↦ₛ r.nameBytes) ∗ A.live ptr 36 1) = _ by ac_rfl))
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

theorem callEmptyAtP_of_parts (A : RustAlloc) (img : Obj.Image) (sp meBuf peerBuf : BitVec 64)
    (role : Role) (kpBytes : List (BitVec 8)) (regId : BitVec 32)
    (hme : meBuf ≠ 0#64) (hpeer : peerBuf ≠ 0#64) :
    ((((sp + 0x008#64) ↦₆₄ 36#64) ∗ ((sp + 0x010#64) ↦₆₄ meBuf) ∗
      ((sp + 0x018#64) ↦₆₄ 36#64) ∗ ((sp + 0x020#64) ↦₈ 1#8) ∗
      memRegion (sp + 0x021#64) 7 ∗ (meBuf ↦ₛ role.nameBytes) ∗ A.live meBuf 36 1) ∗
     (((sp + 0x028#64) ↦₆₄ 36#64) ∗ ((sp + 0x030#64) ↦₆₄ peerBuf) ∗
      ((sp + 0x038#64) ↦₆₄ 36#64) ∗ ((sp + 0x040#64) ↦₈ 1#8) ∗
      memRegion (sp + 0x041#64) 7 ∗ (peerBuf ↦ₛ role.peer.nameBytes) ∗ A.live peerBuf 36 1) ∗
     inMemSessionStoreAt A img (sp + 0x048#64) role.peer none ∗
     inMemIdentityStoreAtP A img (sp + 0x078#64) role kpBytes regId none) ⊢
      callEmptyAtP A img (sp + 0x008#64) role kpBytes regId := by
  let gMe : AddrGhost := ⟨⟨36#64, meBuf, role.nameBytes⟩, 1#8⟩
  let gPeer : AddrGhost := ⟨⟨36#64, peerBuf, role.peer.nameBytes⟩, 1#8⟩
  have hMeVal : gMe.val = role.addrVal := by cases role <;> rfl
  have hPeerVal : gPeer.val = role.peer.addrVal := by cases role <;> rfl
  have hMeLen : gMe.name.bytes.length = 36 := role_nameBytes_length role
  have hPeerLen : gPeer.name.bytes.length = 36 := role_nameBytes_length role.peer
  have h1 := protocolAddressAt_of_addr_write A role meBuf (sp + 0x008#64) hme
  have h2 := protocolAddressAt_of_addr_write A role.peer peerBuf (sp + 0x028#64) hpeer
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2
  unfold callEmptyAtP
  refine Entails.sepExists_right gMe (Entails.sepExists_right gPeer ?_)
  refine Entails.pure_right ⟨hMeVal, hPeerVal, hMeLen, hPeerLen⟩ ?_
  have h28 : (sp + 0x008#64) + 0x20#64 = sp + 0x028#64 := by bv_lin
  have h48 : (sp + 0x008#64) + 0x40#64 = sp + 0x048#64 := by bv_lin
  have h78 : (sp + 0x008#64) + 0x70#64 = sp + 0x078#64 := by bv_lin
  rw [h28, h48, h78]
  exact sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))

def sessionStoreNewFrozenSpecP (img : Obj.Image) :
    Spec (BitVec 64 × Option (BitVec 64 × BitVec 64)) where
  pre := fun (out, st) s =>
    ⌜img.FrozenLoaded s ∧ s.readReg64 .x8 = out⌝ ∗
      memRegion out 48 ∗ tlsKeysAt (s.tpidrEl0 + tlsKeysTpoff) st ∗
        stackAt s.sp (0x20 + extHookStack)
  post := fun (out, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64,
        emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
          tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ∗
      stackAt s0.sp (0x20 + extHookStack)

def identityStoreNewInitAnyFrozenSpecP (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 32 × BitVec 64 × BitVec 64) where
  pre := fun (out, kpPtr, keyPairBytes, regId, k0, k1) s =>
    ⌜img.FrozenLoaded s ∧ s.readReg64 .x8 = out ∧ s.readReg64 .x0 = kpPtr ∧
      s.readReg32 .x1 = regId ∧ keyPairBytes.length = 64⌝ ∗
      memRegion out 120 ∗ (kpPtr ↦ₛ keyPairBytes) ∗
      tlsKeysInitAt (s.tpidrEl0 + tlsKeysTpoff) k0 k1 ∗ stackAt s.sp 0x30
  post := fun (out, kpPtr, keyPairBytes, regId, k0, k1) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
      emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 keyPairBytes regId ∗
      tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1 ∗
      (kpPtr ↦ₛ keyPairBytes) ∗ stackAt s0.sp 0x30

theorem sessionStore_new_frozen_okP (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (uuidParse : UuidParser) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr inMemSessionStoreNewName)
        (sessionStoreNewFrozenSpecP img) := by
  refine subroutine_ok_intro fun ⟨out, st⟩ R s0 hpc hrun hpre hsp => ?_
  simp only [sessionStoreNewFrozenSpecP, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx8⟩, hpre⟩; have hro := StoreNew.storeNewRoDataAt_intro himg hF hpre
  cases st with
  | none =>
    dsimp only [tlsKeysAt, StoreNew.tlsKeysAt, tlsKeysUninitAt, StoreNew.tlsKeysUninitAt] at hro
    have hro' : s0.mem ⊨ (∃∗ k0Old : BitVec 64, ∃∗ k1Old : BitVec 64, ∃∗ tag : BitVec 8,
        ⌜tag ≠ 1#8⌝ ∗ tlsKeysRawAt (s0.tpidrEl0 + tlsKeysTpoff) k0Old k1Old tag) ∗
        (StoreNew.storeNewRoDataAt img.base tlsKeysTpoff (img.base + emptyCtrlOff) ∗
         memRegion out 48 ∗ stackAt s0.sp (0x20 + extHookStack) ∗ R) := by ac_sat hro
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨k0Old, hro'⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨k1Old, hro'⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hro'; rcases hro' with ⟨tag, hro'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hro'; rcases hro' with ⟨htag, hro'⟩
    refine reaches_of_ghost (StoreNew.sessionStore_new_uninit_base_ok img.base C ctl abs
      (base_aligned_of_loads himg) hRk)
      ⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0Old, k1Old,
        tag⟩ emp hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [StoreNew.sessionStoreNewUninitBaseSpec, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj]
      exact ⟨⟨hx8, htag⟩, by ac_sat hro'⟩
    · simp only [StoreNew.sessionStoreNewUninitBaseSpec, sessionStoreNewFrozenSpecP, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩; exact ⟨htr, Satisfies.drop_left hpost⟩
  | some ks =>
    rcases ks with ⟨k0, k1⟩; dsimp only [tlsKeysAt, StoreNew.tlsKeysAt] at hro
    have hstk := StoreNew.stackAt_sessionStoreNew_frame_split s0.sp; rw [hstk] at hro
    refine reaches_of_ghost (StoreNew.sessionStore_new_init_base_ok img.base C ctl abs
      (base_aligned_of_loads himg))
      ⟨out, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩ (stackAt (s0.sp - 32#64) extHookStack)
      hpc hrun hsp ?_ (fun sf _ hpost => ?_)
    · simp only [StoreNew.sessionStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx8, by ac_sat hro⟩
    · simp only [StoreNew.sessionStoreNewInitBaseSpec, sessionStoreNewFrozenSpecP, hstk,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, _⟩, hpost⟩
      have hpost' := Satisfies.drop_left hpost; refine ⟨htr, ?_⟩
      have hex : (emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ∗
        tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0 + 1#64) k1) ⊢
          ∃∗ k0' : BitVec 64, ∃∗ k1' : BitVec 64,
            emptyHashMapAt (img.base + emptyCtrlOff) out k0' k1' ∗
            tlsKeysInitAt (s0.tpidrEl0 + tlsKeysTpoff) (k0' + 1#64) k1' :=
        Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))
      exact Arm64.Satisfies.mono (sepConj_mono_left hex) (by ac_sat hpost')

theorem identityStore_new_init_any_frozen_okP (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (uuidParse : UuidParser) (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr inMemIdentityStoreNewName)
        (identityStoreNewInitAnyFrozenSpecP img) := by
  refine subroutine_ok_refine (StoreNew.identityStore_new_init_base_ok img.base C ctl abs
    (base_aligned_of_loads himg))
    fun ⟨out, kpPtr, keyPairBytes, regId, k0, k1⟩ R s0 hpre => ?_
  simp only [identityStoreNewInitAnyFrozenSpecP, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx8, hx0, hx1, hlen⟩, hpre⟩
  have hro := StoreNew.storeNewRoDataAt_intro himg hF hpre
  refine ⟨⟨out, kpPtr, keyPairBytes, regId, tlsKeysTpoff, img.base + emptyCtrlOff, k0, k1⟩, ?_,
    fun sf hpost => ?_⟩
  · simp only [StoreNew.identityStoreNewInitBaseSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hlen⟩, by simpa only [sepConj_assoc] using hro⟩
  · simp only [StoreNew.identityStoreNewInitBaseSpec, identityStoreNewInitAnyFrozenSpecP,
    sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hpure, hpost⟩; exact ⟨hpure, Satisfies.drop_left hpost⟩

theorem emptyHashMapAt_entails_inMemSessionStoreAtP
    (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (peer : Role) (k0 k1 : BitVec 64) :
    emptyHashMapAt (img.base + emptyCtrlOff) out k0 k1 ⊢ inMemSessionStoreAt A img out peer
      none := by
  dsimp only [inMemSessionStoreAt]
  exact Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.refl _))

theorem emptyIdentityKeyStoreAt_entails_inMemIdentityStoreAtP
    (A : RustAlloc) (img : Obj.Image) (out : BitVec 64) (role : Role)
    (keyPairBytes : List (BitVec 8)) (regId : BitVec 32) (k0 k1 : BitVec 64)
    (hlen : keyPairBytes.length = 64) :
    emptyIdentityKeyStoreAt (img.base + emptyCtrlOff) out k0 k1 keyPairBytes regId ⊢
      inMemIdentityStoreAtP A img out role keyPairBytes regId none := by
  dsimp only [inMemIdentityStoreAtP, emptyIdentityKeyStoreAt, StoreNew.emptyIdentityKeyStoreAt]
  exact Entails.pure_right hlen
    (Entails.sepExists_right k0 (Entails.sepExists_right k1 (Entails.of_eq (by ac_rfl))))

def OpenSeam1b8P (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (img : Obj.Image) (abs : String → Option (State → State))
    (outPtr mePtr statePtr stateLenBv : BitVec 64)
    (meBytes : List (BitVec 8)) (role : Role)
    (F_rest R : SepProp) (s0 s : State) : Prop :=
  s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr openPqxdhName + 0x1b8#64 ∧
    s.status = .Running ∧ s.spAligned = true ∧
    s0.spAligned = true ∧ openPqxdhStack ≤ s0.sp.toNat ∧
    s.sp = s0.sp - 0x4b0#64 ∧
    s.tpidrEl0 = s0.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s.mem ∧
    s.trace = s0.trace ∧
    s.readReg64 .x19 = outPtr ∧
    s.readReg64 .x20 = stateLenBv ∧
    s.readReg64 .x21 = statePtr ∧
    s.readReg64 .x24 = s.sp + 0x008#64 ∧
    s.readReg64 .x25 = s.sp + 0x260#64 ∧
    OpenX27VPreserved s s0 ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    meBytes.length = 36 ∧
    img.FrozenLoaded s ∧
    (s.mem ⊨
      callEmptyAtP A img (s.sp + 0x008#64) role
        (meKeyPairBytes C.pubKey meBytes) (meRegId meBytes) ∗
      memRegion s.sp 8 ∗ memRegion (s.sp + 0x0f0#64) 0x360 ∗
      openSavedRegsAtP s0 ∗
      memRegion outPtr 232 ∗ (mePtr ↦ₛ meBytes) ∗
      (∃∗ tlsCur, tlsKeysAt (s0.tpidrEl0 + tlsKeysTpoff) tlsCur) ∗
      A.pool ∗ memRegion (s0.sp - openPqxdhStack) (openPqxdhStack - 0x4b0) ∗
      F_rest ∗ R ∗ anyHeap)

/-! ## Epilogue and `openEmpty_subroutine_ok` -/

theorem memRegion_openP_0x450_epilogue_join (sp : BitVec 64) :
    memRegion sp 8 ∗ memRegion (sp + 0x008#64) 232 ∗ memRegion (sp + 0x0f0#64) 0x360 =
      memRegion sp 0x450 := by
  rw [← memRegion_split' (b := sp + 0x008#64) (b' := sp + 0x0f0#64)
        (N := 1096) (n := 232) (k := 0x360) (by decide) (by bv_lin) (by decide),
      ← memRegion_split' (b := sp) (b' := sp + 0x008#64)
        (N := 0x450) (n := 8) (k := 1096) (by decide) rfl (by decide)]

theorem who_ne_of_ofWho_none {who : BitVec 32} (h : Role.ofWho who = none) :
    who ≠ 0#32 ∧ who ≠ 1#32 := by
  unfold Role.ofWho at h
  split_ifs at h with h0 h1
  exact ⟨h0, h1⟩

end CryptoVerification.E2E.Pqxdh.WireEntries
