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
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.DecodesIsTrusted
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.HashOne
import LibsignalBinary.Proofs.E2E.InMem.SipHashBin.Skeleton
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply

/-!
# `InMemIdentityKeyStore::is_trusted_identity::{closure#0}` (`0x079c4`)

Proves `isTrustedIdentitySingle_ok'` on a 1-item `InMemIdentityKeyStore`.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.E2E.InMem.HashbrownModel
open CryptoVerification.E2E.InMem.SipHashModel
open CryptoVerification.E2E.InMem.SipHashBin
open CryptoVerification.E2E.InMem.HashbrownBin

namespace IsTrusted

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

theorem sepWP_extract_pure {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P : Prop} {Q F : SepProp} {post : Arm64.State → SepProp → Prop}
    (heq : Q = ⌜P⌝ ∗ F)
    (h : P → SepWP prog pc s F post) :
    SepWP prog pc s Q post := by
  rw [heq]
  exact sepWP_pure_left_elim h

theorem entails_sepExists_intro {α : Sort _} {P : SepProp} {Q : α → SepProp} (a : α)
    (h : P ⊢ Q a) : P ⊢ (∃∗ x, Q x) :=
  Entails.sepExists_right a h

/-! ## Stack Frame, `sret`, and `table4SingleAt` Splitting -/

theorem stackAt_isTrusted_eq (sp : BitVec 64) :
    stackAt sp isTrustedIdentityClosureStack =
      stackAt (sp - 0x80#64) (isTrustedIdentityClosureStack - 128) ∗
      memRegion (sp - 0x80#64) 8 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64,
        ((sp - 0x78#64) ↦₆₄ c0) ∗ ((sp - 0x70#64) ↦₆₄ c1) ∗
        ((sp - 0x68#64) ↦₆₄ c2) ∗ ((sp - 0x60#64) ↦₆₄ c3) ∗
        ((sp - 0x58#64) ↦₆₄ c4) ∗ ((sp - 0x50#64) ↦₆₄ c5) ∗
        ((sp - 0x48#64) ↦₆₄ c6) ∗ ((sp - 0x40#64) ↦₆₄ c7) ∗
        ((sp - 0x38#64) ↦₆₄ c8) ∗ ((sp - 0x30#64) ↦₆₄ c9) ∗
        ((sp - 0x28#64) ↦₆₄ c10) ∗ ((sp - 0x20#64) ↦₆₄ c11) ∗
        ((sp - 0x18#64) ↦₆₄ c12) ∗ ((sp - 0x10#64) ↦₆₄ c13) ∗
        ((sp - 0x08#64) ↦₆₄ c14)) := by
  simp only [stackAt, isTrustedIdentityClosureStack, HashbrownBin.extHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 256))
        (n := 2 ^ 14 + 256 - 128) (k := 128)
        (b' := sp - 0x80#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x80#64) (n := 8) (k := 120)
        (b' := sp - 0x78#64) (by decide) (by bv_omega) (by decide)]
  change memRegion (sp - 16640#64) 16512 ∗
    (memRegion (sp - 0x80#64) 8 ∗ memRegion (sp - 0x78#64) (8 * 15)) = _
  rw [memRegion_cells (sp - 0x78#64) 15 (by decide)]
  have hc15 : cells (sp - 0x78#64) 15 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64,
        ((sp - 0x78#64) ↦₆₄ c0) ∗ ((sp - 0x70#64) ↦₆₄ c1) ∗
        ((sp - 0x68#64) ↦₆₄ c2) ∗ ((sp - 0x60#64) ↦₆₄ c3) ∗
        ((sp - 0x58#64) ↦₆₄ c4) ∗ ((sp - 0x50#64) ↦₆₄ c5) ∗
        ((sp - 0x48#64) ↦₆₄ c6) ∗ ((sp - 0x40#64) ↦₆₄ c7) ∗
        ((sp - 0x38#64) ↦₆₄ c8) ∗ ((sp - 0x30#64) ↦₆₄ c9) ∗
        ((sp - 0x28#64) ↦₆₄ c10) ∗ ((sp - 0x20#64) ↦₆₄ c11) ∗
        ((sp - 0x18#64) ↦₆₄ c12) ∗ ((sp - 0x10#64) ↦₆₄ c13) ∗
        ((sp - 0x08#64) ↦₆₄ c14)) := by
    cells_unfold
  rw [hc15]
  have hsub : sp - 16640#64 = sp - 128#64 - 16512#64 := by bv_omega
  rw [hsub]
  ac_rfl

theorem stackAt_isTrusted_of_parts (sp : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : BitVec 64) :
    (stackAt (sp - 0x80#64) (isTrustedIdentityClosureStack - 128) ∗
      memRegion (sp - 0x80#64) 8 ∗
      ((sp - 0x78#64) ↦₆₄ c0) ∗ ((sp - 0x70#64) ↦₆₄ c1) ∗
      ((sp - 0x68#64) ↦₆₄ c2) ∗ ((sp - 0x60#64) ↦₆₄ c3) ∗
      ((sp - 0x58#64) ↦₆₄ c4) ∗ ((sp - 0x50#64) ↦₆₄ c5) ∗
      ((sp - 0x48#64) ↦₆₄ c6) ∗ ((sp - 0x40#64) ↦₆₄ c7) ∗
      ((sp - 0x38#64) ↦₆₄ c8) ∗ ((sp - 0x30#64) ↦₆₄ c9) ∗
      ((sp - 0x28#64) ↦₆₄ c10) ∗ ((sp - 0x20#64) ↦₆₄ c11) ∗
      ((sp - 0x18#64) ↦₆₄ c12) ∗ ((sp - 0x10#64) ↦₆₄ c13) ∗
      ((sp - 0x08#64) ↦₆₄ c14)) ⊢
    stackAt sp isTrustedIdentityClosureStack := by
  rw [stackAt_isTrusted_eq sp]
  simp only [sepExists_sepConj_right]
  exact entails_sepExists_intro c0 (entails_sepExists_intro c1 (entails_sepExists_intro c2
    (entails_sepExists_intro c3 (entails_sepExists_intro c4 (entails_sepExists_intro c5
    (entails_sepExists_intro c6 (entails_sepExists_intro c7 (entails_sepExists_intro c8
    (entails_sepExists_intro c9 (entails_sepExists_intro c10 (entails_sepExists_intro c11
    (entails_sepExists_intro c12 (entails_sepExists_intro c13
    (entails_sepExists_intro c14 (Entails.of_eq (by ac_rfl))))))))))))))))

theorem stackAt_isTrusted_sub_eq (sp : BitVec 64) :
    stackAt sp (isTrustedIdentityClosureStack - 128) =
      memRegion (sp - 16512#64) 16400 ∗ stackAt sp hashOneAddrStack := by
  simp only [stackAt, isTrustedIdentityClosureStack, HashbrownBin.extHookStack, hashOneAddrStack]
  change memRegion (sp - 16512#64) (16400 + 112) =
    memRegion (sp - 16512#64) 16400 ∗ memRegion (sp - 112#64) 112
  exact ProofLib.memRegion_split' (b := sp - 16512#64)
    (n := 16400) (k := 112) (b' := sp - 112#64) rfl (by bv_omega) (by decide)

theorem stackAt_isTrusted_ext_eq (sp : BitVec 64) :
    stackAt sp (isTrustedIdentityClosureStack - 128) =
      memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack := by
  simp only [stackAt, isTrustedIdentityClosureStack, HashbrownBin.extHookStack]
  change memRegion (sp - 16512#64) (128 + 16384) =
    memRegion (sp - 16512#64) 128 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16512#64)
    (n := 128) (k := 16384) (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

theorem stackAt_isTrusted_ext_restore (sp sp' : BitVec 64)
    (h : sp' = bv% (2 ^ 64 - 128) + sp) :
    memRegion (sp - 128#64 - 16512#64) 128 ∗ stackAt sp' extHookStack ⊢
      stackAt (sp - 128#64) (isTrustedIdentityClosureStack - 128) := by
  have hsp : sp' = sp - 128#64 := by rw [h]; bv_omega
  rw [hsp, ← stackAt_isTrusted_ext_eq (sp - 128#64)]
  exact Entails.refl _

theorem sret48_isTrusted_split_eq (sret : BitVec 64) :
    memRegion sret 48 =
      (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) ∗
      (∃∗ s_8 : BitVec 8, (sret + 8#64) ↦₈ s_8) ∗
      memRegion (sret + 9#64) 39 := by
  rw [ProofLib.memRegion_split' (b := sret) (n := 8) (k := 40) (b' := sret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sret + 8#64) (n := 1) (k := 39) (b' := sret + 9#64) rfl (by bv_omega) (by decide)]
  change memRegion sret (8 * 1) ∗ (memRegion (sret + 8#64) 1 ∗ memRegion (sret + 9#64) 39) = _
  rw [memRegion_cells sret 1 (by decide)]
  have hc1 : cells sret 1 = (∃∗ s_0 : BitVec 64, sret ↦₆₄ s_0) := by
    simp [cells]
  have hm1 : memRegion (sret + 8#64) 1 = (∃∗ s_8 : BitVec 8, (sret + 8#64) ↦₈ s_8) :=
    memRegion_one (sret + 8#64)
  rw [hc1, hm1]

theorem pollBoolResultAt_of_cells (sret : BitVec 64) (b : Bool) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sret + 8#64) ↦₈ (if b then 1#8 else 0#8)) ∗
      memRegion (sret + 9#64) 39) ⊢
    pollBoolResultAt sret b :=
  Entails.refl _

theorem pollBoolResultAt_true_of_cells (sret : BitVec 64) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sret + 8#64) ↦₈ 1#8) ∗
      memRegion (sret + 9#64) 39) ⊢
    pollBoolResultAt sret true :=
  Entails.refl _

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
  have hadd : mp + 32#64 + 8#64 = mp + 40#64 := by bv_omega
  dsimp only [table4SingleAt, table4At]
  simp only [hadd]
  rfl

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

theorem sub_shl6_eq_bucketAddr_add_64 (ctrl : BitVec 64) (k : Nat) (hk : k < 4) :
    ctrl - (BitVec.ofNat 64 k <<< 6) = bucketAddr ctrl 64 k + 64#64 := by
  unfold bucketAddr
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> bv_omega

theorem bucketArray_isTrusted_eq (A : RustAlloc) (ctrl : BitVec 64) (k : Nat)
    (peerG : AddrGhost) (peerKeyBytes : List (BitVec 8))
    (hk : k < 4) (hlen_name : peerG.name.bytes.length = 36) (hlen_key : peerKeyBytes.length = 32) :
    arrayAt
      (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a identityBucketStride)
      identityBucketStride (ctrl - BitVec.ofNat 64 (4 * identityBucketStride)) (List.range 4).reverse =
    ((bucketAddr ctrl 64 k + 8#64) ↦₆₄ peerG.name.ptr) ∗
    ((bucketAddr ctrl 64 k + 16#64) ↦₆₄ 36#64) ∗
    ((bucketAddr ctrl 64 k + 24#64) ↦₈ peerG.device) ∗
    (peerG.name.ptr ↦ₛ peerG.name.bytes) ∗
    ((bucketAddr ctrl 64 k + 32#64) ↦ₛ peerKeyBytes) ∗
    addrRestAt A peerG (bucketAddr ctrl 64 k) ∗
    singleBucketRestAt 64 ctrl k := by
  change arrayAt
    (fun i a => if i ∈ [k] then identityBucketEntryAt A peerG peerKeyBytes a else memRegion a 64)
    64 (ctrl - BitVec.ofNat 64 (4 * 64)) (List.range 4).reverse = _
  rw [arrayAt_single_split_64 ctrl k hk (identityBucketEntryAt A peerG peerKeyBytes)]
  unfold identityBucketEntryAt
  rw [protocolAddressAt_eq_of_len36 A peerG (bucketAddr ctrl 64 k) hlen_name]
  simp only [hlen_key, pure_true, emp_sepConj]
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

/-! ## `<PublicKey as PartialEq>::eq` (`0x3ebf0`) on 32-Byte Slices -/

private theorem memRegion_16_eq_stackFrameFor_eq (sp : BitVec 64) :
    memRegion (sp - 16#64) 16 =
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp := by
  rw [show (16 : Nat) = 8 * 2 by rfl, memRegion_cells (sp - 16#64) 2 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3ecd4, reduceStackFrameAt]

private theorem memRegion_48_eq_stackFrameFor_ct_eq (sp : BitVec 64) :
    memRegion (sp - 48#64) 48 =
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp := by
  rw [show (48 : Nat) = 8 * 6 by rfl, memRegion_cells (sp - 48#64) 6 (by decide)]
  cells_unfold
  simp only [stackFrameFor, libsignalSessionCode_frameBytes_0x3eda8, reduceStackFrameAt]

private theorem stackAt_extHookStack_split_publicKeyEq (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 16320 ∗
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48 := by
  simp only [stackAt, HashbrownBin.extHookStack]
  have h64 : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
  rw [h64,
      show BitVec.ofNat 64 (2 ^ 14) = 16384#64 from rfl,
      show (2 ^ 14 : Nat) = 16384 from rfl,
      ProofLib.memRegion_split' (b := sp - 16384#64) (n := 16320) (k := 64)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
        (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
  ac_rfl

structure PublicKeyEqSliceCall where
  p1 : BitVec 64
  bs1 : List (BitVec 8)
  p2 : BitVec 64
  bs2 : List (BitVec 8)
  sp : BitVec 64

def publicKeyEqSliceSpec : Spec PublicKeyEqSliceCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p1 ∧ s.readReg64 .x1 = x.p2 ∧ s.sp = x.sp ∧
      x.bs1.length = 32 ∧ x.bs2.length = 32⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗
    stackAt x.sp extHookStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = (if x.bs1 = x.bs2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
    (x.p1 ↦ₛ x.bs1) ∗ (x.p2 ↦ₛ x.bs2) ∗
    stackAt x.sp extHookStack

theorem publicKeyEqSlice_ok_at_isTrustedIdentity (b : BitVec 64) {A : RustAlloc} {ext : HookMap}
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"))
      publicKeyEqSliceSpec := by
  refine subroutine_ok_map (publicKeyEq_ok_at_isTrustedIdentity b hHooks) ?_
  rintro ⟨p1, bs1, p2, bs2, sp⟩ R s0 hpre
  simp only [publicKeyEqSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hsp, hlen1, hlen2⟩, hmem⟩
  let pk1 : PublicKey := ⟨⟨bs1, hlen1⟩⟩
  let pk2 : PublicKey := ⟨⟨bs2, hlen2⟩⟩
  have hpk1 : pk1.bytes.toList = bs1 := rfl
  have hpk2 : pk2.bytes.toList = bs2 := rfl
  rw [stackAt_extHookStack_split_publicKeyEq sp] at hmem
  refine ⟨(p1, pk1, p2, pk2, sp), memRegion (sp - 16384#64) 16320 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64),
      hpk1, hpk2, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hsp⟩, ?_⟩
    convert hmem using 1; ac_rfl
  · simp only [CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64),
      hpk1, hpk2, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hret, htr⟩, hpost⟩
    rw [← CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_ite_toList_eq pk1 pk2] at hret
    change sf.readReg64 .x0 = (if bs1 = bs2 then 1#64 else 0#64) at hret
    simp only [publicKeyEqSliceSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hret, htr⟩, ?_⟩
    rw [stackAt_extHookStack_split_publicKeyEq sp]
    convert hpost using 1; ac_rfl

/-! ## NEON Group and Probe Lemmas -/

private theorem zext128_shr_and_255_eq_groupByte (w : BitVec 64) (i : Nat) :
    BitVec.zeroExtend 128 w >>> (i * 8) &&& 255#128 = (groupByte w i).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hw : w.toNat < 2 ^ 64 := w.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
      groupByte, BitVec.toNat_setWidth]
  change ((w.toNat % 2 ^ 128) >>> (i * 8)) &&& (2 ^ 8 - 1) =
    ((w.toNat >>> (8 * i)) % 256) % 2 ^ 128
  have hmod1 : w.toNat % 2 ^ 128 = w.toNat := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (w.toNat >>> (8 * i)) % 256 % 2 ^ 128 = (w.toNat >>> (8 * i)) % 256 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod1, hmod2, Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm i 8]

private theorem zext128_shr57_and_255_eq_h2Tag (h : BitVec 64) :
    BitVec.zeroExtend 128 (h >>> 57) &&& 255#128 = (h2Tag h).zeroExtend 128 := by
  apply BitVec.eq_of_toNat_eq
  have hh : (h >>> 57).toNat < 128 := by
    rw [BitVec.toNat_ushiftRight]
    have := h.isLt
    omega
  rw [BitVec.toNat_and, BitVec.toNat_setWidth,
      h2Tag, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth]
  change ((h >>> 57).toNat % 2 ^ 128) &&& (2 ^ 8 - 1) =
    (((h >>> 57).toNat % 256) &&& (2 ^ 7 - 1)) % 2 ^ 128
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  omega

private abbrev dupTag128 (qtag : BitVec 8) : BitVec 128 :=
  0#128 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 0 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 8 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 16 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 24 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 32 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 40 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 48 |||
    (qtag.zeroExtend 128 &&& 255#128) <<< 56

private theorem dupTag128_lane_0 (qtag : BitVec 8) :
    dupTag128 qtag >>> 0 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_8 (qtag : BitVec 8) :
    dupTag128 qtag >>> 8 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_16 (qtag : BitVec 8) :
    dupTag128 qtag >>> 16 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_24 (qtag : BitVec 8) :
    dupTag128 qtag >>> 24 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_32 (qtag : BitVec 8) :
    dupTag128 qtag >>> 32 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_40 (qtag : BitVec 8) :
    dupTag128 qtag >>> 40 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_48 (qtag : BitVec 8) :
    dupTag128 qtag >>> 48 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel
private theorem dupTag128_lane_56 (qtag : BitVec 8) :
    dupTag128 qtag >>> 56 &&& 255#128 = qtag.zeroExtend 128 := by revert qtag; decide +kernel

private theorem beq_zext128_eq (a b : BitVec 8) :
    (a.zeroExtend 128 == b.zeroExtend 128) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : a.zeroExtend 128 ≠ b.zeroExtend 128 := by
      intro heq
      apply h
      apply BitVec.eq_of_toNat_eq
      have hnat := congrArg BitVec.toNat heq
      rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hnat
      have ha := a.isLt
      have hb := b.isLt
      omega
    simp [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

private theorem truncate64_or (x y : BitVec 128) :
    BitVec.truncate 64 (x ||| y) = BitVec.truncate 64 x ||| BitVec.truncate 64 y :=
  BitVec.setWidth_or

private theorem truncate64_cmeq_0 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 0) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 := by cases c <;> rfl
private theorem truncate64_cmeq_8 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 8) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 8 := by cases c <;> rfl
private theorem truncate64_cmeq_16 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 16) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 16 := by cases c <;> rfl
private theorem truncate64_cmeq_24 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 24) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 24 := by cases c <;> rfl
private theorem truncate64_cmeq_32 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 32) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 32 := by cases c <;> rfl
private theorem truncate64_cmeq_40 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 40) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 40 := by cases c <;> rfl
private theorem truncate64_cmeq_48 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 48) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 48 := by cases c <;> rfl
private theorem truncate64_cmeq_56 (c : Bool) :
    BitVec.truncate 64 (((if c = true then 255#128 else 0#128) &&& 255#128) <<< 56) =
      (if c then 0xff#8 else 0x00#8).zeroExtend 64 <<< 56 := by cases c <;> rfl

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
  rw [zext128_shr57_and_255_eq_h2Tag h]
  change BitVec.truncate 64
      (0#128 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (0 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 0 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 0 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (1 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 8 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 8 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (2 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 16 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 16 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (3 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 24 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 24 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (4 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 32 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 32 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (5 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 40 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 40 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (6 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 48 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 48 |||
        ((if (BitVec.zeroExtend 128 (loadGroupAt cbs pos) >>> (7 * 8) &&& 255#128 == dupTag128 (h2Tag h) >>> 56 &&& 255#128) = true then 255#128 else 0#128) &&& 255#128) <<< 56) &&&
      9259542123273814144#64 =
    findGroupIterMask cbs pos (h2Tag h)
  rw [zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 0,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 1,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 2,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 3,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 4,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 5,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 6,
      zext128_shr_and_255_eq_groupByte (loadGroupAt cbs pos) 7,
      dupTag128_lane_0, dupTag128_lane_8, dupTag128_lane_16, dupTag128_lane_24,
      dupTag128_lane_32, dupTag128_lane_40, dupTag128_lane_48, dupTag128_lane_56]
  simp only [beq_zext128_eq, truncate64_or,
    truncate64_cmeq_0, truncate64_cmeq_8, truncate64_cmeq_16, truncate64_cmeq_24,
    truncate64_cmeq_32, truncate64_cmeq_40, truncate64_cmeq_48, truncate64_cmeq_56,
    BitVec.zero_or]
  rfl

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

theorem evalUmaxv_matchEmpty_singleCtrl4_raw
    (k : Nat) (tag : BitVec 8) (pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    Id.run (do
      let __s ←
        forIn [:8] 0#128 fun i __s =>
          if
            BitVec.ult __s
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
          then
            pure (ForInStep.yield
              (((0#128 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
          else pure (ForInStep.yield __s)
      pure __s) = 255#128 := by
  rw [evalUmaxv8_unfold]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  · revert tag; decide +kernel

theorem evalUmaxv_matchEmpty_singleCtrl4_getLsbD_zero
    (k : Nat) (tag : BitVec 8) (pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.zeroExtend 64
      (BitVec.truncate 32
        (Id.run (do
          let __s ←
            forIn [:8] 0#128 fun i __s =>
              if
                BitVec.ult __s
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128) = true
              then
                pure (ForInStep.yield
                  (((0#128 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 0 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 0 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 8 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 8 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 16 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 16 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 24 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 24 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 32 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 32 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 40 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 40 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 48 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 48 |||
                    ((if BitVec.zeroExtend 128 (loadGroupAt (singleCtrl4 k tag) pos) >>> 56 &&& 255#128 = 255#128 then 255#128 else 0#128) &&& 255#128) <<< 56) >>> (i * 8)) &&& 255#128))
              else pure (ForInStep.yield __s)
          pure __s)))).getLsbD (OfNat.ofNat 0) = true := by
  rw [evalUmaxv_matchEmpty_singleCtrl4_raw k tag pos hk hpos]
  decide

theorem eval_probeBucket_singleCtrl4 (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (BitVec.ofNat 64 pos +
      (laneBit (laneOfBucket4 pos k)).reverse.clz >>> 3) &&&
      3#64 = BitVec.ofNat 64 k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : pos = 0 ∨ pos = 1 ∨ pos = 2 ∨ pos = 3) with rfl | rfl | rfl | rfl <;>
  decide +kernel

theorem eval_clearLowestBit_laneBit_sub (k pos : Nat) (hk : k < 4) (hpos : pos < 4) :
    (laneBit (laneOfBucket4 pos k) - 1#64) &&& laneBit (laneOfBucket4 pos k) = 0#64 := by
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
  have hw : w = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    have hnat : (BitVec.zeroExtend 64 w).toNat = 0 := by rw [hcbnz]; rfl
    rw [BitVec.toNat_setWidth] at hnat
    have hlt := w.isLt
    change w.toNat = 0
    omega
  exact hiff.mp hw

theorem dev_eq_of_zeroExtend {d1 d2 : BitVec 8}
    (h : BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) :
    d1 = d2 := by
  apply BitVec.eq_of_toNat_eq
  have hnat := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hnat
  have h1 := d1.isLt
  have h2 := d2.isLt
  omega

theorem dev_ne_of_not_zeroExtend {P : Prop} {d1 d2 : BitVec 8}
    (h : ¬BitVec.zeroExtend 64 d1 = BitVec.zeroExtend 64 d2) :
    ¬(P ∧ d1 = d2) := by
  rintro ⟨_, rfl⟩
  exact h rfl

theorem readVReg128_eq_of_vregs_eq {s1 : Arm64.State} {vregs0 : VRegFile} (idx : BitVec 5)
    (hv : s1.vregs = vregs0) :
    s1.readVReg128 idx = vregs0.read idx := by
  rw [Arm64.State.readVReg128, hv]

theorem decide_imp_of_not {P Q : Prop} [Decidable P] [Decidable Q] (h : ¬P) :
    decide (P → Q) = true := by
  simp [h]

theorem sepWP_fold_focus {prog : Program} {pc : BitVec 64} {s : Arm64.State}
    {P Q P' R : SepProp} {post : Arm64.State → SepProp → Prop}
    (hfocus : P = P' ∗ R)
    (hent : P' ⊢ Q)
    (hnext : SepWP prog pc s (Q ∗ R) post) :
    SepWP prog pc s P post :=
  SepWP.fold hent hfocus hnext

theorem pollBoolResultAt_of_eq (sret : BitVec 64) (v : BitVec 8) (b : Bool)
    (hv : v = if b then 1#8 else 0#8) :
    ((sret ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((sret + 8#64) ↦₈ v) ∗
      memRegion (sret + 9#64) 39) ⊢
    pollBoolResultAt sret b := by
  subst hv; exact Entails.refl _

/-! ## `isTrustedIdentitySingle_ok'` (`0x079c4`) -/

set_option maxHeartbeats 800000 in
theorem isTrustedIdentitySingle_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName)
      (isTrustedIdentitySingleSpec A) := by
  have hHash : subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName + 0xfffffffffffff3e4#64)
      (hashOneAddr36Spec A) := by
    have h := hashOneAddr36_ok_at_isTrustedIdentityClosure b ext A
    have hsub :
        (RebasedProg b ext).fnAddr isTrustedIdentityClosureName + 0xfffffffffffff3e4#64 =
        (SipHashBin.RebasedProg b ext).fnAddr SipHashBin.isTrustedIdentityClosureName - 0x0c1c#64 := by
      rw [BitVec.sub_eq_add_neg]; rfl
    rwa [hsub]
  have hBcmp := bcmp_ok_at_isTrustedIdentity b hHooks
  have hPkEq := publicKeyEqSlice_ok_at_isTrustedIdentity b hHooks
  simp only [isTrustedIdentitySingleSpec]
  have hfn : libsignalSessionCode.fnOff isTrustedIdentityClosureName = num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}") :=
    (ls_lemma% fnOff "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b ext hfn (num% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}")) 368
  clear hfn
  dsimp only [RebasedProg, BitVec.ofNat_eq_ofNat] at hHash hBcmp hPkEq ⊢
  generalize_entry (libsignalSessionCode.rebase b ext).fnAddr isTrustedIdentityClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b ext) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  wp_init x s0
  examples_hide_fetches
  obtain ⟨futPtr, sret, mp, k0, k1, k, peerG, peerKeyBytes, qAddrPtr, qG, qKeyPtr, qKeyBytes, direction⟩ := x
  dsimp only [IsTrustedIdentitySingleGhost.futPtr, IsTrustedIdentitySingleGhost.sret,
    IsTrustedIdentitySingleGhost.mp, IsTrustedIdentitySingleGhost.k0, IsTrustedIdentitySingleGhost.k1,
    IsTrustedIdentitySingleGhost.k, IsTrustedIdentitySingleGhost.peerG,
    IsTrustedIdentitySingleGhost.peerKeyBytes, IsTrustedIdentitySingleGhost.qAddrPtr,
    IsTrustedIdentitySingleGhost.qG, IsTrustedIdentitySingleGhost.qKeyPtr,
    IsTrustedIdentitySingleGhost.qKeyBytes, IsTrustedIdentitySingleGhost.direction] at *
  wp_conv_pre => rw [table4SingleAt_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepWP_exists_elim; intro ctrl
  wp_conv_pre => rw [sret48_isTrusted_split_eq sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  wp_conv_pre => rw [stackAt_isTrusted_eq s0.sp]
  simp only [sepExists_sepConj_right]
  repeat' (apply sepWP_exists_elim; intro _)
  refine sepWP_extract_pure (P := k < 4) (by sep_focus) fun hk => ?_
  refine sepWP_extract_pure (by sep_focus) ?_
  rintro ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩
  wp_steps
  wp_conv_pre => rw [stackAt_isTrusted_sub_eq (s0.sp - 128#64)]
  wp_apply
  refine SepWP.fold (Entails.of_eq (stackAt_isTrusted_sub_eq (s0.sp - 128#64)).symm) (by sep_focus) ?_
  wp_conv_pre => rw [protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)]
  wp_steps
  let pos := (hashAddrBv k0 k1 qG.name.bytes qG.device &&& 3#64).toNat
  have hpos_lt : pos < 4 := probePos_3_toNat_lt (hashAddrBv k0 k1 qG.name.bytes qG.device)
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
      have hne_key : ¬(qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device) :=
        findGroupIterMask_singleCtrl4_eq_zero_imp_ne k0 k1 k hk
          peerG.name.bytes qG.name.bytes peerG.device qG.device hmask
      rw [decide_imp_of_not (Q := peerKeyBytes = qKeyBytes) hne_key]
      refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
        (by sep_focus) ?_
      refine SepWP.fold (pollBoolResultAt_true_of_cells sret)
        (by sep_focus) ?_
      refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
        peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
        ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
        (by sep_focus) ?_
      refine SepWP.fold (stackAt_isTrusted_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus) ?_
      wp_done
    · exfalso
      exact hemp (evalUmaxv_matchEmpty_singleCtrl4_getLsbD_zero k _ pos hk hpos_lt)
  · have hmask_eq := findGroupIterMask_singleCtrl4_ne_zero_eq k0 k1 k pos hk hpos_lt
      peerG.name.bytes qG.name.bytes peerG.device qG.device hmask
    rw [hmask_eq]
    refine SepWP.fold (Entails.of_eq (bucketArray_isTrusted_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)))
      (by sep_focus) ?_
    wp_steps
    rw [← hpos_bv, eval_probeBucket_singleCtrl4 k pos hk hpos_lt,
        sub_shl6_eq_bucketAddr_add_64 ctrl k hk]
    wp_steps
    wp_conv_pre => rw [stackAt_isTrusted_ext_eq (s0.sp - 128#64)]
    wp_apply
    refine SepWP.fold (stackAt_isTrusted_ext_restore s0.sp _ (by assumption)) (by sep_focus) ?_
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
          rw [decide_imp_of_not (Q := peerKeyBytes = qKeyBytes) hne_key]
          refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (Entails.of_eq (bucketArray_isTrusted_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
            (by sep_focus) ?_
          refine SepWP.fold (pollBoolResultAt_true_of_cells sret)
            (by sep_focus) ?_
          refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
            peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
            ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
            (by sep_focus) ?_
          refine SepWP.fold (stackAt_isTrusted_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
            (by sep_focus) ?_
          wp_done
        · exfalso
          rw [readVReg128_eq_of_vregs_eq 9#5 (by assumption)] at hemp2
          dsimp only [Arm64.State.writeVReg128, Arm64.State.writeReg64, Arm64.State.setPC,
            Arm64.State.setPState, Arm64.State.setMem, VRegFile.read, VRegFile.write,
            arm64_norm] at hemp2
          exact hemp2 (evalUmaxv_matchEmpty_singleCtrl4_getLsbD_zero k _ pos hk hpos_lt)
    · wp_steps
      wp_if hdev
      · wp_steps
        wp_conv_pre => rw [stackAt_isTrusted_ext_eq (s0.sp - 128#64)]
        wp_apply
        refine SepWP.fold (Entails.of_eq (stackAt_isTrusted_ext_eq (s0.sp - 128#64)).symm) (by sep_focus) ?_
        wp_steps
        have heq_key : qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device :=
          ⟨eq_of_not_cbnz_bcmp (by assumption) hcbnz, dev_eq_of_zeroExtend hdev⟩
        refine sepWP_fold_focus
          (P' := (sret ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sret + 8#64) ↦₈ _) ∗ memRegion (sret + 9#64) 39)
          (by sep_focus)
          (pollBoolResultAt_of_eq sret _
            (decide ((qG.name.bytes = peerG.name.bytes ∧ qG.device = peerG.device) → peerKeyBytes = qKeyBytes))
            (by by_cases hq : peerKeyBytes = qKeyBytes <;> simp [*])) ?_
        refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (bucketArray_isTrusted_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
          (by sep_focus) ?_
        refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
          peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
          ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
          (by sep_focus) ?_
        refine SepWP.fold (stackAt_isTrusted_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
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
            rw [decide_imp_of_not (Q := peerKeyBytes = qKeyBytes) hne_key]
            refine SepWP.fold (Entails.of_eq (protocolAddressAt_eq_of_len36 A qG qAddrPtr (by assumption)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (Entails.of_eq (bucketArray_isTrusted_eq A ctrl k peerG peerKeyBytes hk (by assumption) (by assumption)).symm)
              (by sep_focus) ?_
            refine SepWP.fold (pollBoolResultAt_true_of_cells sret)
              (by sep_focus) ?_
            refine SepWP.fold (table4SingleAt_of_parts A identityBucketStride mp k0 k1 k hk
              peerG.name.bytes peerG.device (identityBucketEntryAt A peerG peerKeyBytes) ctrl
              ⟨hctrl_nz, hctrl_align, hctrl_ge, hctrl_lt, hlen4, hmirror, hfull⟩)
              (by sep_focus) ?_
            refine SepWP.fold (stackAt_isTrusted_of_parts s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
              (by sep_focus) ?_
            wp_done
          · exfalso
            rw [readVReg128_eq_of_vregs_eq 9#5 (by assumption)] at hemp2
            dsimp only [Arm64.State.writeVReg128, Arm64.State.writeReg64, Arm64.State.setPC,
              Arm64.State.setPState, Arm64.State.setMem, VRegFile.read, VRegFile.write,
              arm64_norm] at hemp2
            exact hemp2 (evalUmaxv_matchEmpty_singleCtrl4_getLsbD_zero k _ pos hk hpos_lt)

end IsTrusted

theorem isTrustedIdentitySingle_ok' (b : BitVec 64) (ext : HookMap) (A : RustAlloc)
    (hHooks : HashbrownBinHooks A ext) :
    subroutine_ok (RebasedProg b ext)
      ((RebasedProg b ext).fnAddr isTrustedIdentityClosureName)
      (isTrustedIdentitySingleSpec A) :=
  IsTrusted.isTrustedIdentitySingle_ok' b ext A hHooks

end CryptoVerification.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures
