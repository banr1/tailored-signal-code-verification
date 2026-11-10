/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.Common
public import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.Specs
public import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.DecodesGet
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

/-!
# `InMemIdentityKeyStore::get_identity::{closure#0}` (`0x07658`)

Proves `getIdentitySingle_ok'` on a 1-item `InMemIdentityKeyStore`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

namespace GetIdentity

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : Arm64.State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : Arm64.State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  Arm64.State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : Arm64.State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem sepWP_exists_elim {α : Sort _} {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : α → SepProp} {post : Arm64.State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post :=
  HashOne.sepWP_exists_elim h

theorem sepWP_pure_left_elim {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q : SepProp} {post : Arm64.State → SepProp → Prop}
    (h : P → SepWP prog pc s Q post) :
    SepWP prog pc s (⌜P⌝ ∗ Q) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hp, hm⟩ := hm
  exact h hp R hm

theorem stackAt_getIdentity_eq (sp : BitVec 64) :
    stackAt sp getIdentityClosureStack =
      stackAt (sp - 0xa0#64) (getIdentityClosureStack - 160) ∗
      memRegion (sp - 0xa0#64) 8 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64,
       ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c18 : BitVec 64,
        ((sp - 0x98#64) ↦₆₄ c0) ∗ ((sp - 0x90#64) ↦₆₄ c1) ∗
        ((sp - 0x88#64) ↦₆₄ c2) ∗ ((sp - 0x80#64) ↦₆₄ c3) ∗
        ((sp - 0x78#64) ↦₆₄ c4) ∗ ((sp - 0x70#64) ↦₆₄ c5) ∗
        ((sp - 0x68#64) ↦₆₄ c6) ∗ ((sp - 0x60#64) ↦₆₄ c7) ∗
        ((sp - 0x58#64) ↦₆₄ c8) ∗ ((sp - 0x50#64) ↦₆₄ c9) ∗
        ((sp - 0x48#64) ↦₆₄ c10) ∗ ((sp - 0x40#64) ↦₆₄ c11) ∗
        ((sp - 0x38#64) ↦₆₄ c12) ∗ ((sp - 0x30#64) ↦₆₄ c13) ∗
        ((sp - 0x28#64) ↦₆₄ c14) ∗ ((sp - 0x20#64) ↦₆₄ c15) ∗
        ((sp - 0x18#64) ↦₆₄ c16) ∗ ((sp - 0x10#64) ↦₆₄ c17) ∗
        ((sp - 0x08#64) ↦₆₄ c18)) := by
  simp only [stackAt, getIdentityClosureStack, HashbrownBin.extHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 256))
        (n := 2 ^ 14 + 256 - 160) (k := 160)
        (b' := sp - 0xa0#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 152)
        (b' := sp - 0x98#64) (by decide) (by bv_omega) (by decide)]
  change memRegion (sp - 16640#64) 16480 ∗
    (memRegion (sp - 0xa0#64) 8 ∗ memRegion (sp - 0x98#64) (8 * 19)) = _
  rw [memRegion_cells (sp - 0x98#64) 19 (by decide)]
  have hc19 : cells (sp - 0x98#64) 19 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64,
       ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64, ∃∗ c18 : BitVec 64,
        ((sp - 0x98#64) ↦₆₄ c0) ∗ ((sp - 0x90#64) ↦₆₄ c1) ∗
        ((sp - 0x88#64) ↦₆₄ c2) ∗ ((sp - 0x80#64) ↦₆₄ c3) ∗
        ((sp - 0x78#64) ↦₆₄ c4) ∗ ((sp - 0x70#64) ↦₆₄ c5) ∗
        ((sp - 0x68#64) ↦₆₄ c6) ∗ ((sp - 0x60#64) ↦₆₄ c7) ∗
        ((sp - 0x58#64) ↦₆₄ c8) ∗ ((sp - 0x50#64) ↦₆₄ c9) ∗
        ((sp - 0x48#64) ↦₆₄ c10) ∗ ((sp - 0x40#64) ↦₆₄ c11) ∗
        ((sp - 0x38#64) ↦₆₄ c12) ∗ ((sp - 0x30#64) ↦₆₄ c13) ∗
        ((sp - 0x28#64) ↦₆₄ c14) ∗ ((sp - 0x20#64) ↦₆₄ c15) ∗
        ((sp - 0x18#64) ↦₆₄ c16) ∗ ((sp - 0x10#64) ↦₆₄ c17) ∗
        ((sp - 0x08#64) ↦₆₄ c18)) := by
    cells_unfold
  rw [hc19]
  have hsub : sp - 16640#64 = sp - 160#64 - 16480#64 := by bv_lin
  rw [hsub]
  ac_rfl

theorem stackAt_getIdentity_sub_eq (sp : BitVec 64) :
    stackAt sp (getIdentityClosureStack - 160) =
      memRegion (sp - 16480#64) 16368 ∗ stackAt sp hashOneAddrStack := by
  simp only [stackAt, getIdentityClosureStack, HashbrownBin.extHookStack, hashOneAddrStack]
  change memRegion (sp - 16480#64) (16368 + 112) =
    memRegion (sp - 16480#64) 16368 ∗ memRegion (sp - 112#64) 112
  exact ProofLib.memRegion_split' (b := sp - 16480#64)
    (n := 16368) (k := 112) (b' := sp - 112#64) rfl (by bv_omega) (by decide)

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWP prog pc s F post) :
    SepWP prog pc s Q post := by
  rw [heq]
  exact sepWP_pure_left_elim h

theorem table4SingleAt_eq (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) :
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt =
      ⌜k < 4⌝ ∗
      ∃∗ ctrl : BitVec 64,
        ⌜ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
          4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
          ([k].length = 4 → 2#64 = 0#64) ∧
          CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
          FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]⌝ ∗
        (mp ↦₆₄ ctrl) ∗
        ((mp + 8#64) ↦₆₄ 3#64) ∗
        ((mp + 16#64) ↦₆₄ 2#64) ∗
        ((mp + 24#64) ↦₆₄ 1#64) ∗
        ((mp + 32#64) ↦₆₄ k0) ∗
        ((mp + 40#64) ↦₆₄ k1) ∗
        A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
        (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
        arrayAt
          (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
          (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse := by
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_lin
  dsimp only [table4SingleAt, table4At]
  simp only [hadd]
  rfl

def addrRestAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
  (addr ↦₆₄ g.name.cap) ∗
  A.live g.name.ptr g.name.cap.toNat 1 ∗
  memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
    (g.name.cap.toNat - g.name.bytes.length) ∗
  memRegion (addr + 25#64) 7

theorem protocolAddressAt_eq_of_len36 (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64)
    (hlen36 : g.name.bytes.length = 36) :
    protocolAddressAt A g addr =
      ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
      ((addr + 16#64) ↦₆₄ 36#64) ∗
      ((addr + 24#64) ↦₈ g.device) ∗
      (g.name.ptr ↦ₛ g.name.bytes) ∗
      addrRestAt A g addr := by
  have hvec :
      vecGhostAt A g.name addr =
        ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
        (addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ 36#64) ∗
        (g.name.ptr ↦ₛ g.name.bytes) ∗
        A.live g.name.ptr g.name.cap.toNat 1 ∗
        memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
          (g.name.cap.toNat - g.name.bytes.length) := by
    unfold vecGhostAt vecU8At vecHeader
    have h1 :
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) ⊢
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) := by
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      simp only [hne, ↓reduceIte, hlen36] at hlen ⊢
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      have hcomm :
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 36)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 36)
                (g.name.cap.toNat - 36))) =
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ 36#64) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 36)
              (g.name.cap.toNat - 36)) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    have h2 :
        (⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
          (addr + 16#64) ↦₆₄ 36#64 ∗
          g.name.ptr ↦ₛ g.name.bytes ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
          memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
            (g.name.cap.toNat - g.name.bytes.length)) ⊢
        ((addr ↦₆₄ g.name.cap ∗ (addr + 8#64) ↦₆₄ g.name.ptr ∗
            (addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
          ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0⌝ ∗
          if g.name.cap = 0 then emp
          else A.live g.name.ptr g.name.cap.toNat 1 ∗ g.name.ptr ↦ₛ g.name.bytes ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 g.name.bytes.length)
              (g.name.cap.toNat - g.name.bytes.length)) := by
      apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
      have hne : g.name.cap ≠ 0 := by
        intro h0; rw [h0] at hlen; change g.name.bytes.length ≤ 0 at hlen; omega
      rw [sepConj_pure_left_comm]
      apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
      simp only [hne, ↓reduceIte, hlen36]
      have hcomm :
          ((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ 36#64) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗ A.live g.name.ptr g.name.cap.toNat 1 ∗
            memRegion (g.name.ptr + BitVec.ofNat 64 36)
              (g.name.cap.toNat - 36)) =
          (((addr ↦₆₄ g.name.cap) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 36)) ∗
            (A.live g.name.ptr g.name.cap.toNat 1 ∗ (g.name.ptr ↦ₛ g.name.bytes) ∗
              memRegion (g.name.ptr + BitVec.ofNat 64 36)
                (g.name.cap.toNat - 36))) := by ac_rfl
      rw [hcomm]; exact Entails.refl _
    exact ProofLib.sepProp_eq_of_entails h1 h2
  unfold protocolAddressAt addrRestAt
  rw [hvec]
  ac_rfl

theorem sret48_split_eq (sret : BitVec 64) :
    memRegion sret 48 =
      (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) ∗
      (∃∗ s_8 : BitVec 8, (sret + 8#64) ↦₈ s_8) ∗
      (∃∗ s_9 : BitVec 64, ∃∗ s_17 : BitVec 64,
       ∃∗ s_25 : BitVec 64, ∃∗ s_33 : BitVec 64,
        ((sret + 9#64) ↦₆₄ s_9) ∗ ((sret + 17#64) ↦₆₄ s_17) ∗
        ((sret + 25#64) ↦₆₄ s_25) ∗ ((sret + 33#64) ↦₆₄ s_33)) ∗
      memRegion (sret + 41#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 8) (k := 40) (b' := sret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sret + 8#64) (n := 1) (k := 39) (b' := sret + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sret + 9#64) (n := 32) (k := 7) (b' := sret + 41#64) rfl (by bv_omega) (by decide)]
  change memRegion sret (8 * 1) ∗ (memRegion (sret + 8#64) 1 ∗ (memRegion (sret + 9#64) (8 * 4) ∗ memRegion (sret + 41#64) 7)) = _
  rw [memRegion_cells sret 1 (by decide), memRegion_cells (sret + 9#64) 4 (by decide)]
  have hc1 : cells sret 1 = (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) := by
    simp [cells]
  have hc4 : cells (sret + 9#64) 4 =
      (∃∗ s_9 : BitVec 64, ∃∗ s_17 : BitVec 64, ∃∗ s_25 : BitVec 64, ∃∗ s_33 : BitVec 64,
        ((sret + 9#64) ↦₆₄ s_9) ∗ ((sret + 17#64) ↦₆₄ s_17) ∗
        ((sret + 25#64) ↦₆₄ s_25) ∗ ((sret + 33#64) ↦₆₄ s_33)) := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc]
    ac_rfl
  have hm1 : memRegion (sret + 8#64) 1 = (∃∗ s_8 : BitVec 8, (sret + 8#64) ↦₈ s_8) :=
    memRegion_one (sret + 8#64)
  rw [hc1, hc4, hm1]

theorem pointsToBytes_32_eq_cells (a : BitVec 64) (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    (a ↦ₛ bs) =
      (a ↦₆₄ loadGroupAt bs 0) ∗
      ((a + 8#64) ↦₆₄ loadGroupAt bs 8) ∗
      ((a + 16#64) ↦₆₄ loadGroupAt bs 16) ∗
      ((a + 24#64) ↦₆₄ loadGroupAt bs 24) := by
  have h0 : 0 + 8 ≤ bs.length := by omega
  have h8 : 8 + 8 ≤ bs.length := by omega
  have h16 : 16 + 8 ≤ bs.length := by omega
  have h24 : 24 + 8 ≤ bs.length := by omega
  have hd8 : (bs.drop 8).length = 24 := by simp [List.length_drop, hlen]
  have hd16 : (bs.drop 16).length = 16 := by simp [List.length_drop, hlen]
  have hd24 : (bs.drop 24).length = 8 := by simp [List.length_drop, hlen]
  rw [pointsToBytes_take_drop a 8 bs (by omega),
      pointsToBytes_take_drop (a + 8#64) 8 (bs.drop 8) (by omega),
      List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64) 8 (bs.drop 16) (by omega),
      List.drop_drop,
      pointsToBytes_take_drop (a + 8#64 + 8#64 + 8#64) 8 (bs.drop 24) (by omega),
      List.drop_drop]
  have hdrop32 : bs.drop 32 = [] := List.drop_eq_nil_of_le (by omega)
  have h0_eq := pointsToBytes_take8_eq_pointsTo64 a bs 0 h0
  simp only [List.drop_zero] at h0_eq
  have h8_eq := pointsToBytes_take8_eq_pointsTo64 (a + 8#64) bs 8 h8
  have h16_eq := pointsToBytes_take8_eq_pointsTo64 (a + 16#64) bs 16 h16
  have h24_eq := pointsToBytes_take8_eq_pointsTo64 (a + 24#64) bs 24 h24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_lin
  simp only [Nat.reduceAdd, ha16, ha24, hdrop32, pointsToBytes_nil, sepConj_emp]
  rw [h0_eq, h8_eq, h16_eq, h24_eq,
      ← loadGroupAt_eq_pack64 bs 0 h0,
      ← loadGroupAt_eq_pack64 bs 8 h8,
      ← loadGroupAt_eq_pack64 bs 16 h16,
      ← loadGroupAt_eq_pack64 bs 24 h24]

theorem entails_sepExists_intro {α : Sort _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) :=
  Entails.sepExists_right a h

theorem pollOptIdentityKeyResultAt_none_of_cells (sret s_9 s_17 s_25 s_33 : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ 0#8) ∗
      ((sret + 9#64) ↦₆₄ s_9) ∗ ((sret + 17#64) ↦₆₄ s_17) ∗
      ((sret + 25#64) ↦₆₄ s_25) ∗ ((sret + 33#64) ↦₆₄ s_33) ∗
      memRegion (sret + 41#64) 7) ⊢
    pollOptIdentityKeyResultAt sret none := by
  unfold pollOptIdentityKeyResultAt
  rw [ProofLib.memRegion_split' (b := sret + 9#64) (n := 32) (k := 7) (b' := sret + 41#64) rfl (by bv_omega) (by decide)]
  change _ ⊢ (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ 0#8) ∗
    (memRegion (sret + 9#64) (8 * 4) ∗ memRegion (sret + 41#64) 7)
  rw [memRegion_cells (sret + 9#64) 4 (by decide)]
  have hc4 : cells (sret + 9#64) 4 =
      (∃∗ s_9 : BitVec 64, ∃∗ s_17 : BitVec 64, ∃∗ s_25 : BitVec 64, ∃∗ s_33 : BitVec 64,
        ((sret + 9#64) ↦₆₄ s_9) ∗ ((sret + 17#64) ↦₆₄ s_17) ∗
        ((sret + 25#64) ↦₆₄ s_25) ∗ ((sret + 33#64) ↦₆₄ s_33)) := by
    simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc]
    ac_rfl
  rw [hc4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact entails_sepExists_intro s_9 (entails_sepExists_intro s_17 (entails_sepExists_intro s_25
    (entails_sepExists_intro s_33 (Entails.of_eq (by ac_rfl)))))

theorem stackAt_getIdentity_of_parts (sp : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 : BitVec 64) :
    (stackAt (sp - 0xa0#64) (getIdentityClosureStack - 160) ∗
      memRegion (sp - 0xa0#64) 8 ∗
      ((sp - 0x98#64) ↦₆₄ c0) ∗ ((sp - 0x90#64) ↦₆₄ c1) ∗
      ((sp - 0x88#64) ↦₆₄ c2) ∗ ((sp - 0x80#64) ↦₆₄ c3) ∗
      ((sp - 0x78#64) ↦₆₄ c4) ∗ ((sp - 0x70#64) ↦₆₄ c5) ∗
      ((sp - 0x68#64) ↦₆₄ c6) ∗ ((sp - 0x60#64) ↦₆₄ c7) ∗
      ((sp - 0x58#64) ↦₆₄ c8) ∗ ((sp - 0x50#64) ↦₆₄ c9) ∗
      ((sp - 0x48#64) ↦₆₄ c10) ∗ ((sp - 0x40#64) ↦₆₄ c11) ∗
      ((sp - 0x38#64) ↦₆₄ c12) ∗ ((sp - 0x30#64) ↦₆₄ c13) ∗
      ((sp - 0x28#64) ↦₆₄ c14) ∗ ((sp - 0x20#64) ↦₆₄ c15) ∗
      ((sp - 0x18#64) ↦₆₄ c16) ∗ ((sp - 0x10#64) ↦₆₄ c17) ∗
      ((sp - 0x08#64) ↦₆₄ c18)) ⊢
    stackAt sp getIdentityClosureStack := by
  rw [stackAt_getIdentity_eq sp]
  simp only [sepExists_sepConj_right]
  exact entails_sepExists_intro c0 (entails_sepExists_intro c1 (entails_sepExists_intro c2
    (entails_sepExists_intro c3 (entails_sepExists_intro c4 (entails_sepExists_intro c5
    (entails_sepExists_intro c6 (entails_sepExists_intro c7 (entails_sepExists_intro c8
    (entails_sepExists_intro c9 (entails_sepExists_intro c10 (entails_sepExists_intro c11
    (entails_sepExists_intro c12 (entails_sepExists_intro c13 (entails_sepExists_intro c14
    (entails_sepExists_intro c15 (entails_sepExists_intro c16 (entails_sepExists_intro c17
    (entails_sepExists_intro c18 (Entails.of_eq (by ac_rfl))))))))))))))))))))

theorem table4SingleAt_of_parts (A : RustAlloc) (stride : Nat) (mp k0 k1 : BitVec 64)
    (k : Nat) (hk : k < 4) (peerName : List (BitVec 8)) (peerDev : BitVec 8)
    (entryAt : BitVec 64 → SepProp) (ctrl : BitVec 64)
    (hctrl : ctrl ≠ 0#64 ∧ ctrl.toNat % 8 = 0 ∧
      4 * stride ≤ ctrl.toNat ∧ ctrl.toNat + 12 < 2 ^ 64 ∧
      ([k].length = 4 → 2#64 = 0#64) ∧
      CtrlMirrorInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∧
      FullBucketsInv 3#64 (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) [k]) :
    ((mp ↦₆₄ ctrl) ∗
      ((mp + 8#64) ↦₆₄ 3#64) ∗
      ((mp + 16#64) ↦₆₄ 2#64) ∗
      ((mp + 24#64) ↦₆₄ 1#64) ∗
      ((mp + 32#64) ↦₆₄ k0) ∗
      ((mp + 40#64) ↦₆₄ k1) ∗
      A.live (ctrl - BitVec.ofNat 64 (4 * stride)) (tableAllocSize 4 stride) 8 ∗
      (ctrl ↦ₛ singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev))) ∗
      arrayAt
        (fun i a => if i ∈ [k] then entryAt a else memRegion a stride) stride
        (ctrl - BitVec.ofNat 64 (4 * stride)) (List.range 4).reverse) ⊢
    table4SingleAt A stride mp k0 k1 k peerName peerDev entryAt := by
  rw [table4SingleAt_eq]
  apply Entails.pure_right hk
  refine entails_sepExists_intro ctrl ?_
  exact Entails.pure_right hctrl (Entails.refl _)

theorem pollOptIdentityKeyResultAt_some_of_cells (sret : BitVec 64) (keyBytes : List (BitVec 8))
    (hlen : keyBytes.length = 32) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ 1#8) ∗
      ((sret + 9#64) ↦₆₄ loadGroupAt keyBytes 0) ∗
      ((sret + 17#64) ↦₆₄ loadGroupAt keyBytes 8) ∗
      ((sret + 25#64) ↦₆₄ loadGroupAt keyBytes 16) ∗
      ((sret + 33#64) ↦₆₄ loadGroupAt keyBytes 24) ∗
      memRegion (sret + 41#64) 7) ⊢
    pollOptIdentityKeyResultAt sret (some keyBytes) := by
  unfold pollOptIdentityKeyResultAt
  apply Entails.pure_right hlen
  rw [pointsToBytes_32_eq_cells (sret + 9#64) keyBytes hlen]
  simp only [BitVec.add_assoc]
  exact Entails.of_eq (by ac_rfl)

theorem dup8_lane (h : BitVec 64) :
    let v := (0#128 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56)
    (v >>> 0 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 8 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 16 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 24 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 32 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 40 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 48 &&& 255#128 = (h2Tag h).zeroExtend 128) ∧
    (v >>> 56 &&& 255#128 = (h2Tag h).zeroExtend 128) := by
  dsimp only [h2Tag]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem groupByte_lane (w : BitVec 64) :
    (BitVec.zeroExtend 128 w >>> 0 &&& 255#128 = (groupByte w 0).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 8 &&& 255#128 = (groupByte w 1).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 16 &&& 255#128 = (groupByte w 2).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 24 &&& 255#128 = (groupByte w 3).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 32 &&& 255#128 = (groupByte w 4).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 40 &&& 255#128 = (groupByte w 5).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 48 &&& 255#128 = (groupByte w 6).zeroExtend 128) ∧
    (BitVec.zeroExtend 128 w >>> 56 &&& 255#128 = (groupByte w 7).zeroExtend 128) := by
  dsimp only [groupByte]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem zeroExtend128_beq_8 (a b : BitVec 8) :
    (a.zeroExtend 128 == b.zeroExtend 128) = (a == b) := by
  by_cases hab : a = b
  · subst hab; simp
  · have hne : a.zeroExtend 128 ≠ b.zeroExtend 128 := by
      intro h; apply hab; bv_omega
    simp [hab, hne]

theorem truncate64_pack8_ite_and_mask (p0 p1 p2 p3 p4 p5 p6 p7 : Bool) :
    BitVec.truncate 64
      (0#128 |||
        ((if p0 = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if p1 = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if p2 = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if p3 = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if p4 = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if p5 = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if p6 = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if p7 = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    packGroupWord
      (if p0 = true then 255#8 else 0#8)
      (if p1 = true then 255#8 else 0#8)
      (if p2 = true then 255#8 else 0#8)
      (if p3 = true then 255#8 else 0#8)
      (if p4 = true then 255#8 else 0#8)
      (if p5 = true then 255#8 else 0#8)
      (if p6 = true then 255#8 else 0#8)
      (if p7 = true then 255#8 else 0#8) &&&
      bitmaskIterMask := by
  cases p0 <;> cases p1 <;> cases p2 <;> cases p3 <;>
  cases p4 <;> cases p5 <;> cases p6 <;> cases p7 <;> rfl

theorem rawMatchTagMask_eq_findGroupIterMask (cbs : List (BitVec 8)) (pos : Nat) (h : BitVec 64) :
    BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 0 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 0 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 8 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 8 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 16 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 16 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 24 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 24 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 32 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 32 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 40 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 40 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 48 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 48 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> 56 &&& 255#128 ==
              (0#128 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 0 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 8 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 16 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 24 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 32 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 40 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 48 |||
                (BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 &&& 255#128) <<< 56) >>> 56 &&& 255#128) = true
          then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h) := by
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ := dup8_lane h
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := groupByte_lane (loadGroupAt cbs pos)
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
      hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7]
  simp only [zeroExtend128_beq_8]
  exact truncate64_pack8_ite_and_mask _ _ _ _ _ _ _ _

theorem ite_forInStep_yield {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep α)) else pure (ForInStep.yield b)) =
    pure (ForInStep.yield (if c then a else b)) := by
  by_cases h : c <;> simp [h]

theorem forIn_range8_yield {α : Type} (init : α) (g : Nat → α → α) :
    Id.run (do
      let __s ← forIn [:8] init (fun i __s => pure (ForInStep.yield (g i __s)))
      pure __s) =
    (let c0 := g 0 init
     let c1 := g 1 c0
     let c2 := g 2 c1
     let c3 := g 3 c2
     let c4 := g 4 c3
     let c5 := g 5 c4
     let c6 := g 6 c5
     g 7 c6) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

theorem evalUmaxv8_unfold (vn : BitVec 128) :
    Id.run (do
      let __s ←
        forIn [:8] 0#128 fun i __s =>
          if BitVec.ult __s ((vn >>> (i * 8)) &&& 255#128) = true then
            pure (ForInStep.yield ((vn >>> (i * 8)) &&& 255#128))
          else pure (ForInStep.yield __s)
      pure __s) =
    (let c0 := if BitVec.ult 0#128 ((vn >>> 0) &&& 255#128) = true then (vn >>> 0) &&& 255#128 else 0#128
     let c1 := if BitVec.ult c0 ((vn >>> 8) &&& 255#128) = true then (vn >>> 8) &&& 255#128 else c0
     let c2 := if BitVec.ult c1 ((vn >>> 16) &&& 255#128) = true then (vn >>> 16) &&& 255#128 else c1
     let c3 := if BitVec.ult c2 ((vn >>> 24) &&& 255#128) = true then (vn >>> 24) &&& 255#128 else c2
     let c4 := if BitVec.ult c3 ((vn >>> 32) &&& 255#128) = true then (vn >>> 32) &&& 255#128 else c3
     let c5 := if BitVec.ult c4 ((vn >>> 40) &&& 255#128) = true then (vn >>> 40) &&& 255#128 else c4
     let c6 := if BitVec.ult c5 ((vn >>> 48) &&& 255#128) = true then (vn >>> 48) &&& 255#128 else c5
     if BitVec.ult c6 ((vn >>> 56) &&& 255#128) = true then (vn >>> 56) &&& 255#128 else c6) := by
  simp only [ite_forInStep_yield]
  exact forIn_range8_yield 0#128 (fun i __s =>
    if BitVec.ult __s ((vn >>> (i * 8)) &&& 255#128) = true then
      (vn >>> (i * 8)) &&& 255#128
    else __s)

theorem packGroupWord_lanes (x0 x1 x2 x3 x4 x5 x6 x7 : BitVec 8) :
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 0 &&& 255#128 = x0.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 8 &&& 255#128 = x1.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 16 &&& 255#128 = x2.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 24 &&& 255#128 = x3.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 32 &&& 255#128 = x4.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 40 &&& 255#128 = x5.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 48 &&& 255#128 = x6.zeroExtend 128) ∧
    (BitVec.zeroExtend 128 (packGroupWord x0 x1 x2 x3 x4 x5 x6 x7) >>> 56 &&& 255#128 = x7.zeroExtend 128) := by
  dsimp only [packGroupWord]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem evalUmaxv_matchEmpty_mkCtrl4_raw (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (hpos : pos < 4) :
    Id.run (do
      let __s ←
        forIn [:8] 0#128 fun i __s =>
          if
            BitVec.ult __s
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
          then
            pure (ForInStep.yield
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
          else pure (ForInStep.yield __s)
      pure __s) = 255#128 := by
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b0 b1 b2 b3 emptyTag emptyTag emptyTag emptyTag
    rw [loadGroupAt_mkCtrl4_0, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b1 b2 b3 emptyTag emptyTag emptyTag emptyTag b0
    rw [loadGroupAt_mkCtrl4_1, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b2 b3 emptyTag emptyTag emptyTag emptyTag b0 b1
    rw [loadGroupAt_mkCtrl4_2, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)
  · obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
      packGroupWord_lanes b3 emptyTag emptyTag emptyTag emptyTag b0 b1 b2
    rw [loadGroupAt_mkCtrl4_3, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7]
    dsimp only [emptyTag]
    by_cases h0 : b0.zeroExtend 128 = 255#128 <;>
    by_cases h1 : b1.zeroExtend 128 = 255#128 <;>
    by_cases h2 : b2.zeroExtend 128 = 255#128 <;>
    by_cases h3 : b3.zeroExtend 128 = 255#128 <;>
    simp only [h0, h1, h2, h3, ↓reduceIte] <;>
    (rw [evalUmaxv8_unfold]; rfl)

theorem evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero
    (b0 b1 b2 b3 : BitVec 8) (pos : Nat) (hpos : pos < 4) :
    (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (Id.run (do
          let __s ←
            forIn [:8] 0#128 fun i __s =>
              if
                BitVec.ult __s
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
              then
                pure (ForInStep.yield
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (mkCtrl4 b0 b1 b2 b3) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
              else pure (ForInStep.yield __s)
          pure __s)))).getLsbD (OfNat.ofNat 0) = true := by
  rw [evalUmaxv_matchEmpty_mkCtrl4_raw b0 b1 b2 b3 pos hpos]
  decide

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3) &&&
      3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_clearLowestBit_laneBit (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) &&& (laneBit (laneOfBucket4 pos k) + bv% (2 ^ 64 - 1)) = 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem laneBit_laneOfBucket4_ne_zero (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    laneBit (laneOfBucket4 pos k) ≠ 0#64 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem findGroupIterMask_singleCtrl4_eq_zero_imp_ne
    (k0 k1 : BitVec 64) (k : Nat) (hk : k < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask0 :
      findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat
        (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    ¬(qName = peerName ∧ qDev = peerDev) := by
  rintro ⟨rfl, rfl⟩
  have hpos : (hashAddrBv k0 k1 qName qDev &&& 3#64).toNat < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 qName qDev)
  rw [findGroupIterMask_singleCtrl4 k _ hk hpos] at hmask0
  simp only [beq_self_eq_true, ↓reduceIte] at hmask0
  exact laneBit_laneOfBucket4_ne_zero k _ hk hpos hmask0

theorem findGroupIterMask_singleCtrl4_ne_zero_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne :
      ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
      pos (h2Tag (hashAddrBv k0 k1 qName qDev)) =
      laneBit (laneOfBucket4 pos k) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne ⊢
  split at hmask_ne
  · rename_i heq
    simp [heq]
  · exfalso
    exact hmask_ne rfl

theorem findGroupIterMask_singleCtrl4_ne_zero_tag_eq
    (k0 k1 : BitVec 64) (k pos : Nat) (hk : k < 4) (hpos : pos < 4)
    (peerName qName : List (BitVec 8)) (peerDev qDev : BitVec 8)
    (hmask_ne :
      ¬findGroupIterMask (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerName peerDev)))
        pos (h2Tag (hashAddrBv k0 k1 qName qDev)) = 0#64) :
    h2Tag (hashAddrBv k0 k1 peerName peerDev) = h2Tag (hashAddrBv k0 k1 qName qDev) := by
  rw [findGroupIterMask_singleCtrl4 k pos hk hpos] at hmask_ne
  split at hmask_ne
  · rename_i heq
    exact eq_of_beq heq
  · exfalso
    exact hmask_ne rfl

theorem stackAt_getIdentity_ext_eq (sp : BitVec 64) :
    stackAt sp (getIdentityClosureStack - 160) =
      memRegion (sp - 16480#64) 96 ∗ stackAt sp extHookStack := by
  simp only [stackAt, getIdentityClosureStack, HashbrownBin.extHookStack]
  change memRegion (sp - 16480#64) (96 + 16384) =
    memRegion (sp - 16480#64) 96 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16480#64)
    (n := 96) (k := 16384) (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

theorem stackAt_getIdentity_ext_restore (sp sp' : BitVec 64)
    (h : sp' = bv% (2 ^ 64 - 160) + sp) :
    memRegion (sp - 160#64 - 16480#64) 96 ∗ stackAt sp' extHookStack ⊢
      stackAt (sp - 160#64) (getIdentityClosureStack - 160) := by
  have hsp : sp' = sp - 160#64 := by rw [h]; bv_lin
  rw [hsp, ← stackAt_getIdentity_ext_eq (sp - 160#64)]
  exact Entails.refl _

theorem sub_shl6_eq_bucketAddr_add_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - (BitVec.ofNat 64 k <<< 6) = bucketAddr ctrl 64 k + 64#64 := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

theorem bucketArray_getIdentity_eq (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (peerKeyBytes : List (BitVec 8))
    (hk : k < 4) (hlen_name : peerG.name.bytes.length = 36) (hlen_key : peerKeyBytes.length = 32) :
    arrayAt
      (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a identityBucketStride)
      identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
    ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ peerG.name.ptr) ∗
    ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 k + 24#64) ↦₈ peerG.device) ∗
    (peerG.name.ptr ↦ₛ peerG.name.bytes) ∗
    ((bucketAddr ctrl 64 k + 32#64) ↦₆₄ loadGroupAt peerKeyBytes 0) ∗
    ((bucketAddr ctrl 64 k + 40#64) ↦₆₄ loadGroupAt peerKeyBytes 8) ∗
    ((bucketAddr ctrl 64 k + 48#64) ↦₆₄ loadGroupAt peerKeyBytes 16) ∗
    ((bucketAddr ctrl 64 k + 56#64) ↦₆₄ loadGroupAt peerKeyBytes 24) ∗
    addrRestAt A peerG (bucketAddr ctrl 64 k) ∗
    singleBucketRestAt 64 ctrl k := by
  change arrayAt
    (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a 64)
    64 (ctrl - BitVec.ofNat 64 (4 * 64)) (List.range 4).reverse = _
  rw [arrayAt_single_split_64 ctrl k hk (identityBucketEntryAt A peerG peerKeyBytes)]
  unfold identityBucketEntryAt
  rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 64 k) hlen_name,
      pointsToBytes_32_eq_cells (bucketAddr ctrl 64 k + 32#64) peerKeyBytes hlen_key]
  have h40 : (32#64 : BitVec 64) + 8#64 = 40#64 := rfl
  have h48 : (32#64 : BitVec 64) + 16#64 = 48#64 := rfl
  have h56 : (32#64 : BitVec 64) + 24#64 = 56#64 := rfl
  simp only [hlen_key, pure_true, emp_sepConj, BitVec.add_assoc, h40, h48, h56]
  ac_rfl

theorem step_ldpSimd64_sp' {prog : Program} {target_pc : BitVec 64}
    {s s' : Arm64.State} {P : SepProp} {post : Arm64.State → SepProp → Prop}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {off ea ea2 v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 (.Offset .sp off)))
    (hsp : checkRegSPAligned s .sp = true)
    (hea : s.sp + off = ea)
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((s.writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2 (v2.zeroExtend 128)).setPC (pc + 4#64)) = s')
    (hnext : SepWP prog target_pc s' P post) :
    SepWP prog target_pc s P post :=
  step_ldpSimd64 (wb := none) hpc hrun hfetch
    (by simp [checkAddrSPAligned, AddrMode.baseReg, hsp])
    (by simp [evalAddrMode, Arm64.State.readReg64, hea])
    hea2 hload1 hload2 hexec hnext

theorem eval_clearLowestBit_laneBit_sub (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (laneBit (laneOfBucket4 pos k) - 1#64) &&& laneBit (laneOfBucket4 pos k) = 0#64 := by
  have h := eval_clearLowestBit_laneBit k pos hk hpos
  have hsub : laneBit (laneOfBucket4 pos k) - 1#64 =
      laneBit (laneOfBucket4 pos k) + bv% (2 ^ 64 - 1) := by bv_lin
  rw [hsub, BitVec.and_comm]
  exact h

theorem bitVec128_lowByte_eq_of_truncate64 (v128 : BitVec 128) (w64 : BitVec 64)
    (hw : v128.truncate 64 = w64) :
    (v128 >>> 0 &&& 255#128 = w64.zeroExtend 128 >>> 0 &&& 255#128) ∧
    (v128 >>> 8 &&& 255#128 = w64.zeroExtend 128 >>> 8 &&& 255#128) ∧
    (v128 >>> 16 &&& 255#128 = w64.zeroExtend 128 >>> 16 &&& 255#128) ∧
    (v128 >>> 24 &&& 255#128 = w64.zeroExtend 128 >>> 24 &&& 255#128) ∧
    (v128 >>> 32 &&& 255#128 = w64.zeroExtend 128 >>> 32 &&& 255#128) ∧
    (v128 >>> 40 &&& 255#128 = w64.zeroExtend 128 >>> 40 &&& 255#128) ∧
    (v128 >>> 48 &&& 255#128 = w64.zeroExtend 128 >>> 48 &&& 255#128) ∧
    (v128 >>> 56 &&& 255#128 = w64.zeroExtend 128 >>> 56 &&& 255#128) := by
  subst hw
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice,
          by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem ne_of_cbnz_bcmp {w : BitVec 32} {P Q : Prop}
    (hiff : (w = 0#32) ↔ P)
    (hcbnz : ¬BitVec.zeroExtend 64 w = 0#64) :
    ¬(P ∧ Q) := by
  intro ⟨hp, _⟩
  apply hcbnz
  have hw : w = 0#32 := hiff.mpr hp
  subst hw; rfl

theorem eq_of_not_cbnz_bcmp {w : BitVec 32} {P : Prop}
    (hiff : (w = 0#32) ↔ P)
    (hcbnz : BitVec.zeroExtend 64 w = 0#64) :
    P := by
  have hw : w = 0#32 := by bv_omega
  exact hiff.mp hw

theorem dev_eq_of_zeroExtend {d1 d2 : BitVec 8}
    (h : BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) :
    d1 = d2 := by
  bv_omega

theorem dev_ne_of_not_zeroExtend {P : Prop} {d1 d2 : BitVec 8}
    (h : ¬BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) :
    ¬(P ∧ d1 = d2) := by
  rintro ⟨_, rfl⟩
  exact h rfl

theorem readVReg128_eq_of_vregs_eq {s1 : Arm64.State} {vregs0 : VRegFile} (idx : BitVec 5)
    (hv : s1.vregs = vregs0) :
    s1.readVReg128 idx = vregs0.read idx := by
  rw [Arm64.State.readVReg128, hv]

set_option maxHeartbeats 800000 in
theorem getIdentitySingle_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName)
      (getIdentitySingleSpec A) := by
  have hHash : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr getIdentityClosureName + 0xfffffffffffff750#64)
      (hashOneAddr36Spec A) := by
    have h := hashOneAddr36_ok_at_getIdentityClosure b ext A
    have hsub :
        (RebasedProg b ext).fnAddr getIdentityClosureName + 0xfffffffffffff750#64 =
        (SipHashBin.RebasedProg b ext).fnAddr SipHashBin.getIdentityClosureName - 0x08b0#64 := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hBcmp := bcmp_ok_at_getIdentity b hHooks
  simp only [getIdentitySingleSpec]
  have hfn : libsignalSessionCode.fnOff getIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}") :=
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}")) 372
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hHash hBcmp ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr getIdentityClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, mp, k0, k1, k, peerG, peerKeyBytes, qAddrPtr, qG⟩ := x
  dsimp only [GetIdentitySingleGhost.futPtr, GetIdentitySingleGhost.sret,
    GetIdentitySingleGhost.mp, GetIdentitySingleGhost.k0, GetIdentitySingleGhost.k1,
    GetIdentitySingleGhost.k, GetIdentitySingleGhost.peerG,
    GetIdentitySingleGhost.peerKeyBytes, GetIdentitySingleGhost.qAddrPtr,
    GetIdentitySingleGhost.qG] at *
  wp_conv_pre => rw [table4SingleAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro ctrl
  wp_conv_pre => rw [sret48_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  wp_conv_pre => rw [stackAt_getIdentity_eq s0.sp]
  simp only [sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  refine sepWP_extract_pure (P := k < 4) (by sep_focus) fun hk => ?_
  refine sepWP_extract_pure (by sep_focus) ?_
  rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
  wp_steps
  wp_conv_pre => rw [stackAt_getIdentity_sub_eq (s0.sp - 160#64)]
  wp_apply
  refine SepWP.fold (Entails.of_eq (stackAt_getIdentity_sub_eq (s0.sp - 160#64)).symm) (by sep_focus) ?_
  wp_conv_pre => rw [protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)]
  wp_steps
  let pos := (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64).toNat
  have hpos_lt : pos < 4 :=
    probePos_3_toNat_lt (hashAddrBv k0 k1 qG.name.bytes qG.device)
  have hpos_bv : BitVec.ofNat 64 pos = hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64 := by
    simp [pos]
  have hcbs_len : (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))).length = 12 := by
    simp [singleCtrl4, mkCtrl4]
  have hcbs_split := pointsToBytes_ctrl12_split_at ctrl
    (singleCtrl4 k (h2Tag (hashAddrBv k0 k1 peerG.name.bytes peerG.device))) hcbs_len pos hpos_lt
  rw [hpos_bv] at hcbs_split
  refine SepWP.fold (Entails.of_eq hcbs_split) (by sep_focus) ?_
  refine step_ldrSimd64 (ea := ctrl + (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64)) (wb := none)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_assumption)
    rfl (by simp [evalAddrMode, extendVal, arm64_norm, *])
    (by wp_sep_access_fast) (by wp_norm_lhs) ?_
  wp_conv_pre => rw [← hcbs_split]
  wp_steps
  rw [rawMatchTagMask_eq_findGroupIterMask]
  wp_if hmask
  · wp_steps
    wp_if hemp
    · wp_steps
      have h_ite : (if qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device then some peerKeyBytes else none) = none := by
        simp [findGroupIterMask_singleCtrl4_eq_zero_imp_ne k0 k1 k hk
          peerG.name.bytes qG.name.bytes peerG.device qG.device hmask]
      rw [h_ite]
      refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
        (by sep_focus) ?_
      refine SepWP.fold (pollOptIdentityKeyResultAt_none_of_cells sret _ _ _ _)
        (by sep_focus) ?_
      refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
        peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
        ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_getIdentity_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      wp_done
    · exfalso
      dsimp only [singleCtrl4] at hemp
      exact hemp (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)
  · have hmask_eq := findGroupIterMask_singleCtrl4_ne_zero_eq k0 k1 k pos hk hpos_lt
      peerG.name.bytes qG.name.bytes peerG.device qG.device hmask
    rw [hmask_eq]
    refine SepWP.fold (Entails.of_eq (bucketArray_getIdentity_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)))
      (by sep_focus) ?_
    wp_steps
    rw [← hpos_bv, eval_probeBucket_singleCtrl4 k pos hk hpos_lt,
        sub_shl6_eq_bucketAddr_add_64 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [stackAt_getIdentity_ext_eq (s0.sp - 160#64)]
    wp_apply
    refine SepWP.fold (stackAt_getIdentity_ext_restore s0.sp _ (by assumption)) (by sep_focus) ?_
    wp_steps
    wp_if hcbnz
    · wp_steps
      wp_if hloop
      · exfalso
        exact hloop (eval_clearLowestBit_laneBit_sub k pos hk hpos_lt)
      · wp_steps
        wp_if hemp2
        · wp_steps
          have hne_key : ¬(qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device) :=
            ne_of_cbnz_bcmp (by assumption) hcbnz
          have h_ite : (if qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device then some peerKeyBytes else none) = none := by
            simp [hne_key]
          rw [h_ite]
          refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (bucketArray_getIdentity_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (pollOptIdentityKeyResultAt_none_of_cells sret _ _ _ _)
            (by sep_focus) ?_
          refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
            peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
            ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_getIdentity_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by sep_focus) ?_
          wp_done
        · exfalso
          rw [readVReg128_eq_of_vregs_eq 9#5 (by assumption)] at hemp2
          dsimp only [Arm64.State.writeVReg128, Arm64.State.writeReg64, Arm64.State.setPC,
            Arm64.State.setPState, Arm64.State.setMem, VRegFile.read, VRegFile.write,
            singleCtrl4, arm64_norm] at hemp2
          exact hemp2 (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)
    · wp_steps
      wp_if hdev
      · wp_steps
        have heq_key : qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device :=
          ⟨eq_of_not_cbnz_bcmp (by assumption) hcbnz, dev_eq_of_zeroExtend hdev⟩
        have h_ite : (if qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device then some peerKeyBytes else none) = some peerKeyBytes := by
          simp [heq_key]
        rw [h_ite]
        refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (bucketArray_getIdentity_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
          (by sep_focus) ?_
        refine SepWP.fold (pollOptIdentityKeyResultAt_some_of_cells sret peerKeyBytes (by assumption))
          (by sep_focus) ?_
        refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
          peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
          ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_getIdentity_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus) ?_
        wp_done
      · wp_steps
        wp_if hloop
        · exfalso
          exact hloop (eval_clearLowestBit_laneBit_sub k pos hk hpos_lt)
        · wp_steps
          wp_if hemp2
          · wp_steps
            have hne_key : ¬(qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device) :=
              dev_ne_of_not_zeroExtend hdev
            have h_ite : (if qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device then some peerKeyBytes else none) = none := by
              simp [hne_key]
            rw [h_ite]
            refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (bucketArray_getIdentity_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (pollOptIdentityKeyResultAt_none_of_cells sret _ _ _ _)
              (by sep_focus) ?_
            refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
              peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
              ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
              (by sep_focus) ?_
            refine SepWP.fold (stackAt_getIdentity_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by sep_focus) ?_
            wp_done
          · exfalso
            rw [readVReg128_eq_of_vregs_eq 9#5 (by assumption)] at hemp2
            dsimp only [Arm64.State.writeVReg128, Arm64.State.writeReg64, Arm64.State.setPC,
              Arm64.State.setPState, Arm64.State.setMem, VRegFile.read, VRegFile.write,
              singleCtrl4, arm64_norm] at hemp2
            exact hemp2 (evalUmaxv_matchEmpty_mkCtrl4_getLsbD_zero _ _ _ _ pos hpos_lt)

end GetIdentity

end CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
