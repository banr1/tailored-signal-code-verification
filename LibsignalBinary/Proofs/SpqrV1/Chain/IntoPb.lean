/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::Chain>::into_pb`

Proves the non-wrapping and wrapping `VecDeque` conversion paths, fixed-image contracts
(`chain_into_pb_pinned_ok`, `chain_into_pb_ok`), and relocatable `[LibsignalPlacement]` contracts
(`chain_into_pb_pinned_placed_ok`, `chain_into_pb_placed_ok`) for `<spqr::chain::Chain>::into_pb`
(`0x60514`, Block `365`, 239 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L36
open IntoPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Unpinning Bridge (`chainPBIntoPinnedAt` to `ProtoRepr.chainPBAt`) -/

theorem topChainPBAt_entails_protoRepr (A : RustAlloc)
    (g : ChainPBGhost) (a : BitVec 64) (ch : ChainPB) :
    chainPBAt A g a ch ⊢
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A a ch := by
  unfold chainPBAt CryptoVerification.SpqrV1.ProtoRepr.chainPBAt
    CryptoVerification.SpqrV1.ProtoRepr.chainLinksVecAt
    CryptoVerification.SpqrV1.ProtoRepr.rustBytesVecAt
    vecOf vecU8 vecAt vecBuf
  refine Entails.pure_left fun hlen => ?_
  have hzlen : (g.epochs.zip ch.links).length = ch.links.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  rw [hzlen, optChainParamsPBAt_eq_protoRepr]
  have harr := arrayAt_chainEpochPBAt_entails_protoRepr A g.epochs ch.links g.linksPtr hlen
  have hvec :
      vecHeader a g.linksCap g.linksPtr (BitVec.ofNat 64 ch.links.length) ∗
        ⌜ch.links.length ≤ g.linksCap.toNat ∧ g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0⌝ ∗
        (if g.linksCap = 0 then emp
         else A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
           arrayAt (chainEpochPBAt A) 112 g.linksPtr (g.epochs.zip ch.links) ∗
           memRegion (g.linksPtr + BitVec.ofNat 64 (ch.links.length * 112))
             ((g.linksCap.toNat - ch.links.length) * 112)) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        vecHeader a cap ptr (BitVec.ofNat 64 ch.links.length) ∗
          ⌜ch.links.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr (cap.toNat * 112) 8 ∗
             arrayAt (fun ep addr => CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBAt A addr ep)
               112 ptr ch.links ∗
             memRegion (ptr + BitVec.ofNat 64 (ch.links.length * 112))
               ((cap.toNat - ch.links.length) * 112)) := by
    refine Entails.sepExists_right g.linksCap (Entails.sepExists_right g.linksPtr ?_)
    refine sepConj_mono_right (sepConj_mono_right ?_)
    by_cases hc : g.linksCap = 0
    · simp only [hc, ↓reduceIte]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      exact sepConj_mono_right (sepConj_mono_left harr)
  have hnr :
      vecU8At A (a + 0x18#64) g.nextRoot.cap g.nextRoot.ptr ch.nextRoot ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        vecU8At A (a + 0x18#64) cap ptr ch.nextRoot :=
    Entails.sepExists_right g.nextRoot.cap (Entails.sepExists_right g.nextRoot.ptr (Entails.refl _))
  exact sepConj_mono hvec (sepConj_mono_left hnr)

theorem chainPBIntoPinnedAt_entails_protoRepr (A : RustAlloc)
    (gChain : ChainGhost) (out : BitVec 64) (cChain : Chain) :
    chainPBIntoPinnedAt A gChain out cChain ⊢
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A out cChain.intoPb := by
  unfold chainPBIntoPinnedAt
  exact Entails.sepExists_elim fun newLinksPtr =>
    topChainPBAt_entails_protoRepr A
      ⟨BitVec.ofNat 64 cChain.links.length, newLinksPtr,
        gChain.epochs.map toChainEpochPBGhost, gChain.nextRoot⟩
      out cChain.intoPb

/-! ## Arithmetic and Buffer Reassembly Helpers -/

theorem take_zip_eq {α β : Type} :
    ∀ (n : Nat) (xs : List α) (ys : List β),
      (xs.zip ys).take n = (xs.take n).zip (ys.take n)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _, [] => by simp
  | n + 1, x :: xs, y :: ys => congrArg ((x, y) :: ·) (take_zip_eq n xs ys)

theorem drop_zip_eq {α β : Type} :
    ∀ (n : Nat) (xs : List α) (ys : List β),
      (xs.zip ys).drop n = (xs.drop n).zip (ys.drop n)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _, [] => by simp
  | n + 1, _ :: xs, _ :: ys => drop_zip_eq n xs ys

theorem memRegion_nonwrap_join (ptr : BitVec 64) (cap head len : Nat)
    (hcap_lt : cap * 112 < 2 ^ 63)
    (hhead_le : head ≤ cap) (hlen_le : len ≤ cap - head) :
    memRegion ptr (head * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 (head * 112)) (len * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ⊢
      memRegion ptr (cap * 112) := by
  have h1 :
      memRegion (ptr + BitVec.ofNat 64 (head * 112)) (len * 112) ∗
        memRegion (ptr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) =
      memRegion (ptr + BitVec.ofNat 64 (head * 112)) ((cap - head) * 112) := by
    have hlen_add : (cap - head) * 112 = len * 112 + (cap - head - len) * 112 := by
      rw [← Nat.add_mul, show len + (cap - head - len) = cap - head by omega]
    have hptr_add : ptr + BitVec.ofNat 64 ((head + len) * 112) =
        ptr + BitVec.ofNat 64 (head * 112) + BitVec.ofNat 64 (len * 112) := by
      rw [Nat.add_mul, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hlen_add]
    exact (ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 (head * 112))
      (n := len * 112) (k := (cap - head - len) * 112)
      (b' := ptr + BitVec.ofNat 64 ((head + len) * 112))
      rfl hptr_add (by omega)).symm
  have h2 :
      memRegion ptr (head * 112) ∗
        memRegion (ptr + BitVec.ofNat 64 (head * 112)) ((cap - head) * 112) =
      memRegion ptr (cap * 112) := by
    have hcap_add : cap * 112 = head * 112 + (cap - head) * 112 := by
      rw [← Nat.add_mul, show head + (cap - head) = cap by omega]
    rw [hcap_add]
    exact (ProofLib.memRegion_split' (b := ptr) (n := head * 112) (k := (cap - head) * 112)
      (b' := ptr + BitVec.ofNat 64 (head * 112)) rfl rfl (by omega)).symm
  rw [h1, h2]
  exact Entails.refl _

theorem memRegion_wrap_join (ptr : BitVec 64) (cap head len : Nat)
    (hcap_lt : cap * 112 < 2 ^ 63)
    (hhead_lt : head < cap) (hlen_le : len ≤ cap) (hlen_gt : cap - head < len) :
    memRegion ptr ((len - (cap - head)) * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len - (cap - head)) * 112))
        ((head - (len - (cap - head))) * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 (head * 112)) ((cap - head) * 112) ⊢
      memRegion ptr (cap * 112) := by
  let m₂ := len - (cap - head)
  have hm2_le : m₂ ≤ head := by omega
  have h1 :
      memRegion ptr (m₂ * 112) ∗
        memRegion (ptr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) =
      memRegion ptr (head * 112) := by
    have hhead_add : head * 112 = m₂ * 112 + (head - m₂) * 112 := by
      rw [← Nat.add_mul, show m₂ + (head - m₂) = head by omega]
    rw [hhead_add]
    exact (ProofLib.memRegion_split' (b := ptr) (n := m₂ * 112) (k := (head - m₂) * 112)
      (b' := ptr + BitVec.ofNat 64 (m₂ * 112)) rfl rfl (by omega)).symm
  have h2 :
      memRegion ptr (head * 112) ∗
        memRegion (ptr + BitVec.ofNat 64 (head * 112)) ((cap - head) * 112) =
      memRegion ptr (cap * 112) := by
    have hcap_add : cap * 112 = head * 112 + (cap - head) * 112 := by
      rw [← Nat.add_mul, show head + (cap - head) = cap by omega]
    rw [hcap_add]
    exact (ProofLib.memRegion_split' (b := ptr) (n := head * 112) (k := (cap - head) * 112)
      (b' := ptr + BitVec.ofNat 64 (head * 112)) rfl rfl (by omega)).symm
  dsimp only [m₂] at h1
  rw [← sepConj_assoc, h1, h2]
  exact Entails.refl _

theorem head_ult_cap {head cap : BitVec 64} (h : head.toNat < cap.toNat) :
    BitVec.ult head cap = true := by simpa [BitVec.ult] using h

theorem cap_sub_head_eq_ofNat {head cap : BitVec 64} (h : head.toNat ≤ cap.toNat) :
    cap - head = BitVec.ofNat 64 (cap.toNat - head.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : cap.toNat - head.toNat < 18446744073709551616 := by omega
  rw [BitVec.toNat_sub_of_le h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem head_mul_112_eq_ofNat (head : BitVec 64) (h : head.toNat * 112 < 2 ^ 63) :
    head * 112#64 = BitVec.ofNat 64 (head.toNat * 112) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : head.toNat * 112 < 18446744073709551616 := by omega
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem nonwrap_ult_hi_false {len m₁ : Nat} (hle : len ≤ m₁) (hm1 : m₁ < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = false := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64]; omega

theorem nonwrap_hi_false {len m₁ : Nat} (hle : len ≤ m₁) (hm1 : m₁ < 2 ^ 63) :
    (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
      !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = false := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  by_cases hlt : len < m₁
  · have hu : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = true := by
      simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64, hlt]
    simp [hu]
  · have heq : len = m₁ := by omega
    subst heq; simp

theorem nonwrap_head_ne_end (head : BitVec 64) {len : Nat}
    (hpos : 1 ≤ len) (hlen : len < 2 ^ 63) :
    (head == head + BitVec.ofNat 64 len) = false := by
  have hl64 : len < 18446744073709551616 := by omega
  rw [beq_eq_false_iff_ne]; intro heq
  have h0 : BitVec.ofNat 64 len = 0#64 := by bv_omega
  have htn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64] at htn; omega

theorem nonwrap_min_eq_len {len m₁ : Nat} (hle : len ≤ m₁) (hm1 : m₁ < 2 ^ 63) :
    (if BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = true
     then BitVec.ofNat 64 len else BitVec.ofNat 64 m₁) = BitVec.ofNat 64 len := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  by_cases hlt : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = true
  · simp [hlt]
  · have hnot : ¬(len < m₁) := fun hlt' => hlt (by
      simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64, hlt'])
    have heq : len = m₁ := by omega
    subst heq; simp

theorem wrap_ult_hi_true {len m₁ : Nat} (hgt : m₁ < len) (hlen : len < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = true := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64, hgt]

theorem wrap_hi_true {len m₁ : Nat} (hgt : m₁ < len) (hlen : len < 2 ^ 63) :
    (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
      !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = true := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  have hu : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false := by
    simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64]; omega
  have hne : (BitVec.ofNat 64 len == BitVec.ofNat 64 m₁) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have htn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64] at htn; omega
  simp [hu, hne]

theorem wrap_ult_false {len m₁ : Nat} (hgt : m₁ < len) (hlen : len < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  simp [BitVec.ult, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64]; omega

theorem wrap_len_sub_m1 {len m₁ : Nat} (hle : m₁ ≤ len) (hlen : len < 2 ^ 63) :
    BitVec.ofNat 64 len - BitVec.ofNat 64 m₁ = BitVec.ofNat 64 (len - m₁) := by
  have hl64 : len < 18446744073709551616 := by omega
  have hm64 : m₁ < 18446744073709551616 := by omega
  have hd64 : len - m₁ < 18446744073709551616 := by omega
  apply BitVec.eq_of_toNat_eq
  have hle_bv : (BitVec.ofNat 64 m₁).toNat ≤ (BitVec.ofNat 64 len).toNat := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64]; exact hle
  rw [BitVec.toNat_sub_of_le hle_bv]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hd64]

/-! ## Non-Wrapping Post-Allocation Path (`+156 .. +952`) -/

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_nonwrap {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length) (hl_pos : 1 ≤ x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hnonwrap : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let srcBase := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 (cap - head) :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hult_hi_false : BitVec.ult (BitVec.ofNat 64 (cap - head)) (BitVec.ofNat 64 len) = false :=
    nonwrap_ult_hi_false hnonwrap (by omega)
  have hhi_false :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head))) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 (cap - head))) = false :=
    nonwrap_hi_false hnonwrap (by omega)
  have hhead_ne_end : (x.gChain.linksHead == x.gChain.linksHead + BitVec.ofNat 64 len) = false :=
    nonwrap_head_ne_end x.gChain.linksHead hl_pos (by omega)
  have hmin_eq :
      (if BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head)) = true
       then BitVec.ofNat 64 len else BitVec.ofNat 64 (cap - head)) = BitVec.ofNat 64 len :=
    nonwrap_min_eq_len hnonwrap (by omega)
  have hlsl_len : (BitVec.ofNat 64 len <<< (7 : Nat)) - (BitVec.ofNat 64 len <<< (4 : Nat)) =
      BitVec.ofNat 64 (len * 112) := mul_112_shift_eq len hl_new_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh := umulh_div112_sub_112 hl_pos hl_new_lt
  have hadd1 := ofNat_sub_one_add_one hl_pos
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hslots := vecDequeSlots_nonwrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt (by rw [hzlen]; exact hnonwrap)
  rw [hzlen] at hslots
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := intoPb_loop1_run (A := A) (b := b) (ext := ext) x.chain.links x.gChain.epochs [] [] s0
  have hepilogue := @chainIntoPb_epilogue A b ext hdealloc x s0
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hloop1 hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (len * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase (x.gChain.epochs.zip x.chain.links) ∗
      memRegion x.gChain.linksPtr (head * 112) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 len ∧ s1.readReg64 .x9 = 0#64 ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x12 = BitVec.ofNat 64 (len * 112) ∧
      s1.readReg64 .x13 = s0.sp - 160#64 ∧ s1.readReg64 .x14 = s0.sp - 208#64 ∧
      s1.readReg64 .x15 = s0.sp - 260#64 ∧ s1.readReg64 .x16 = newLinksPtr + 52#64 ∧
      s1.readReg64 .x17 = srcBase + 56#64 ∧ s1.readReg64 .x19 = x.chainPtr ∧
      s1.readReg64 .x20 = x.out ∧ s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 (cap - head)).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_false hhead_ne_end
      simp only [hult_hi_false, Bool.false_eq_true, ↓reduceIte, hhead_ne_end]
    have humulh_norm :
        BitVec.truncate 64
          ((BitVec.zeroExtend 128 ((BitVec.ofNat 64 (len * 112) - 112#64) >>> 4) *
            2635249153387078803#128) >>> 64) = BitVec.ofNat 64 (len - 1) := by
      simpa using umulh_div112_sub_112 hl_pos hl_new_lt
    dsimp only [len] at hult_hi_false hhi_false hhead_ne_end hmin_eq hlsl_len humulh humulh_norm hadd1
    wp_steps; dsimp only [srcBase]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase newLinksPtr hsp0_align
      hl_pos hlen rfl (by simpa using hl_new_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 hx12_1 hx13_1 hx14_1 hx15_1
      (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
          memRegion x.gChain.linksPtr (head * 112) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    have hjoin_old := memRegion_nonwrap_join x.gChain.linksPtr cap head len hl_cap_lt (Nat.le_of_lt hhead_lt) hnonwrap
    have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
      unfold linksRawAllocAt
      have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
        absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
      have htn : (BitVec.ofNat 64 len).toNat = len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
      exact Entails.refl _
    refine SepWP.weaken_pre hP2 ?_
    refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase]; sep_focus) ?_
    refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
    refine seq_clean (mid := entry + 820#64)
      (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = 0#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x21 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 len ∧ s3.readReg64 .x23 = 0#64 ∧
        s3.readReg64 .x24 = newLinksPtr ∧ s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
    · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3⟩
      exact hepilogue s3 newLinksPtr hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
        hn1 hn2 hn3 hpc3 hrun3 hsp3 htr3 hfp3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx22_3
        hx23_3 hx24_3 hx26_3 hx28_3

/-! ## Wrapping Post-Allocation Path (`+156 .. +952`) -/

@[local wp_norm]
theorem umulh_div112_sub_112_norm {n : Nat} (hpos : 1 ≤ n) (hn : n * 112 < 2 ^ 63) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 ((BitVec.ofNat 64 (n * 112) - 112#64) >>> 4) *
        2635249153387078803#128) >>> 64) = BitVec.ofNat 64 (n - 1) := by
  simpa using umulh_div112_sub_112 hpos hn

theorem add_m1_m2_sub_one {m₁ m₂ len : Nat} (hm2 : 1 ≤ m₂) (hsum : m₁ + m₂ = len) :
    BitVec.ofNat 64 m₁ + BitVec.ofNat 64 (m₂ - 1) + 1#64 = BitVec.ofNat 64 len := by
  have heq : len = m₁ + (m₂ - 1) + 1 := by omega
  conv_rhs => rw [heq, BitVec.ofNat_add, BitVec.ofNat_add]

theorem add_m2_sub_one_m1 {m₁ m₂ len : Nat} (hm2 : 1 ≤ m₂) (hsum : m₁ + m₂ = len) :
    BitVec.ofNat 64 (m₂ - 1) + BitVec.ofNat 64 m₁ + 1#64 = BitVec.ofNat 64 len := by
  have heq : len = (m₂ - 1) + m₁ + 1 := by omega
  conv_rhs => rw [heq, BitVec.ofNat_add, BitVec.ofNat_add]

theorem madd_m1_112_add_52 (newLinksPtr : BitVec 64) (m₁ : Nat) :
    newLinksPtr + BitVec.ofNat 64 m₁ * 112#64 + 52#64 =
      newLinksPtr + BitVec.ofNat 64 (m₁ * 112) + 52#64 := by rw [← BitVec.ofNat_mul]

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_wrap {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hwrap : x.gChain.linksCap.toNat - x.gChain.linksHead.toNat < x.chain.links.length)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let m₁ := cap - head
  let m₂ := len - m₁
  let srcBase1 := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  let rem1 := x.chain.links.take m₁
  let rem1G := x.gChain.epochs.take m₁
  let rem2 := x.chain.links.drop m₁
  let rem2G := x.gChain.epochs.drop m₁
  have hm1_pos : 1 ≤ m₁ := by omega
  have hm2_pos : 1 ≤ m₂ := by omega
  have hm_sum : m₁ + m₂ = len := by omega
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hm1_lt : m₁ * 112 < 2 ^ 63 := by omega
  have hm2_lt : m₂ * 112 < 2 ^ 63 := by omega
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hhead_ne_cap : (x.gChain.linksHead == x.gChain.linksCap) = false := by
    rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hhead_lt; exact Nat.lt_irrefl _ hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 m₁ :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hlen_sub_m1 : BitVec.ofNat 64 len - BitVec.ofNat 64 m₁ = BitVec.ofNat 64 m₂ :=
    wrap_len_sub_m1 (Nat.le_of_lt hwrap) (by omega)
  have hlsl_m2 : (BitVec.ofNat 64 m₂ <<< (7 : Nat)) - (BitVec.ofNat 64 m₂ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₂ * 112) := mul_112_shift_eq m₂ hm2_lt
  have hult_hi_true : BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = true :=
    wrap_ult_hi_true hwrap (by omega)
  have hhi_true :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = true := wrap_hi_true hwrap (by omega)
  have hult_false : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false :=
    wrap_ult_false hwrap (by omega)
  have hlsl_m1 : (BitVec.ofNat 64 m₁ <<< (7 : Nat)) - (BitVec.ofNat 64 m₁ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₁ * 112) := mul_112_shift_eq m₁ hm1_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh1 := umulh_div112_sub_112 hm1_pos hm1_lt
  have humulh1_norm := umulh_div112_sub_112_norm hm1_pos hm1_lt
  have hadd1_m1 := ofNat_sub_one_add_one hm1_pos
  have hm2_cbz_false : (BitVec.ofNat 64 (m₂ * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hm2_lt
  have humulh2 := umulh_div112_sub_112 hm2_pos hm2_lt
  have humulh2_norm := umulh_div112_sub_112_norm hm2_pos hm2_lt
  have hmadd_dst := madd_m1_112_add_52 newLinksPtr m₁
  have hadd_x2 := add_m1_m2_sub_one hm2_pos hm_sum
  have hadd_x8 := add_m2_sub_one_m1 hm2_pos hm_sum
  have hrem1_len : rem1.length = m₁ := List.length_take_of_le (by omega)
  have hrem1G_len : rem1G.length = m₁ := List.length_take_of_le (by omega)
  have hrem2_len : rem2.length = m₂ := by dsimp [rem2]; rw [List.length_drop]
  have hrem2G_len : rem2G.length = m₂ := by dsimp [rem2G]; rw [List.length_drop, hlen]
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hzip_take : (x.gChain.epochs.zip x.chain.links).take m₁ = rem1G.zip rem1 :=
    take_zip_eq m₁ x.gChain.epochs x.chain.links
  have hzip_drop : (x.gChain.epochs.zip x.chain.links).drop m₁ = rem2G.zip rem2 :=
    drop_zip_eq m₁ x.gChain.epochs x.chain.links
  have hslots := vecDequeSlots_wrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt
    (by rw [hzlen]; exact hl_le) (by rw [hzlen]; exact hwrap)
  rw [hzlen, hzip_take, hzip_drop] at hslots
  have hsplit_dst : memRegion newLinksPtr (len * 112) =
      memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) := by
    have hmul_sum : len * 112 = m₁ * 112 + m₂ * 112 := by rw [← Nat.add_mul, hm_sum]
    conv_lhs => rw [hmul_sum]
    exact ProofLib.memRegion_split' (b := newLinksPtr) (n := m₁ * 112) (k := m₂ * 112)
      (b' := newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) rfl rfl (by omega)
  rw [hsplit_dst]
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := intoPb_loop1_run (A := A) (b := b) (ext := ext) rem1 rem1G [] [] s0
  have hloop2 := intoPb_loop2_run (A := A) (b := b) (ext := ext) rem2 rem2G rem1G rem1 s0
  have hepilogue := @chainIntoPb_epilogue A b ext hdealloc x s0
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hloop1 hloop2 hepilogue hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase1 (rem1G.zip rem1) ∗
      arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧ s1.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x11 = 0x2492492492492493#64 ∧
      s1.readReg64 .x12 = BitVec.ofNat 64 (m₁ * 112) ∧ s1.readReg64 .x13 = s0.sp - 160#64 ∧
      s1.readReg64 .x14 = s0.sp - 208#64 ∧ s1.readReg64 .x15 = s0.sp - 260#64 ∧
      s1.readReg64 .x16 = newLinksPtr + 52#64 ∧ s1.readReg64 .x17 = srcBase1 + 56#64 ∧
      s1.readReg64 .x19 = x.chainPtr ∧ s1.readReg64 .x20 = x.out ∧
      s1.readReg64 .x22 = BitVec.ofNat 64 len ∧ s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 m₁).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_true; simp only [hult_hi_true, ↓reduceIte, hhead_ne_cap]
    dsimp only [len] at hlen_sub_m1 hult_hi_true hhi_true hult_false
    wp_steps; dsimp only [srcBase1]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase1 newLinksPtr hsp0_align
      (by rw [hrem1_len]; exact hm1_pos) (by rw [hrem1G_len, hrem1_len]) rfl
      (by rw [List.length_nil, Nat.zero_add, hrem1_len]; exact hm1_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 (by rw [hrem1_len]; exact hx12_1)
      hx13_1 hx14_1 hx15_1 (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append, hrem1_len] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx3_1] at hx3_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2; rw [hx11_1] at hx11_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    refine SepWP.weaken_pre hP2 ?_
    refine seq_clean (mid := entry + 512#64)
      (P_mid := memRegion srcBase1 (m₁ * 112) ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((rem1G.map toChainEpochPBGhost).zip (rem1.map chainEpochIntoPb)) ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32))
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x0 = newLinksPtr ∧ s3.readReg64 .x2 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x3 = x.gChain.linksCap ∧ s3.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧
        s3.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧ s3.readReg64 .x10 = s0.sp - 160#64 ∧
        s3.readReg64 .x11 = BitVec.ofNat 64 (m₂ - 1) ∧ s3.readReg64 .x12 = s0.sp - 160#64 ∧
        s3.readReg64 .x13 = s0.sp - 208#64 ∧ s3.readReg64 .x14 = s0.sp - 260#64 ∧
        s3.readReg64 .x15 = newLinksPtr + BitVec.ofNat 64 (m₁ * 112) + 52#64 ∧
        s3.readReg64 .x16 = x.gChain.linksPtr + 56#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · wp_steps; wp_done
    · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx0_3, hx2_3, hx3_3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3, hx15_3, hx16_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3⟩
      have h0_bv : BitVec.ofNat 64 0 = 0#64 := rfl
      have hrun_l2 := hloop2 s3 x.gChain x.chain x.gChain.linksPtr newLinksPtr m₁ hsp0_align
        (by rw [hrem2_len]; exact hm2_pos) (by rw [hrem2G_len, hrem2_len])
        (by rw [hrem1G_len, hrem1_len]) (by rw [hrem1_len])
        (by rw [hrem1_len, hrem2_len, hm_sum]; exact hl_new_lt)
        hpc3 hrun3 hsp3 htr3 hfp3 (by rw [hrem2_len]; exact hx9_3)
        hx10_3 hx12_3 hx13_3 hx14_3 (by rw [hrem1_len]; exact hx15_3)
        (by rw [hrem1_len, Nat.sub_self, Nat.zero_mul, h0_bv, BitVec.add_zero]; exact hx16_3)
      have happG : rem1G ++ rem2G = x.gChain.epochs := List.take_append_drop m₁ x.gChain.epochs
      have happ : rem1 ++ rem2 = x.chain.links := List.take_append_drop m₁ x.chain.links
      simp only [hrem1_len, hrem2_len, Nat.sub_self, Nat.zero_mul, Nat.zero_add,
        memRegion_zero, emp_sepConj, h0_bv, BitVec.add_zero, happG, happ] at hrun_l2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (SepWP.seq (SepWP.frame_post_entails (F :=
          memRegion srcBase1 (m₁ * 112) ∗ memRegion x.out 80 ∗
            chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
            A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
            memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
            vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
            A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l2) ?_)
      rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hfp4, hx0_4, hx2_4, hx3_4, hx8_4, hx11_4, hcs4⟩
      rw [hx0_3] at hx0_4; rw [hx2_3] at hx2_4; rw [hx3_3] at hx3_4; rw [hx8_3] at hx8_4; rw [hx11_3] at hx11_4
      have hx19_4 : s4.readReg64 .x19 = x.chainPtr := (hcs4.1).trans hx19_3
      have hx20_4 : s4.readReg64 .x20 = x.out := (hcs4.2.1).trans hx20_3
      have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 len := (hcs4.2.2.2.1).trans hx22_3
      have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 len := (hcs4.2.2.2.2.2.2.1).trans hx25_3
      have hx26_4 : s4.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx28_4 : s4.readReg64 .x28 = x.gChain.linksPtr := (hcs4.2.2.2.2.2.2.2.2.2.1).trans hx28_3
      have hjoin_old := memRegion_wrap_join x.gChain.linksPtr cap head len hl_cap_lt hhead_lt hl_le hwrap
      have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
        unfold linksRawAllocAt
        have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
          absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
        have htn : (BitVec.ofNat 64 len).toNat = len := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
        exact Entails.refl _
      refine SepWP.weaken_pre hP4 ?_
      refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase1, m₁, m₂]; sep_focus) ?_
      refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
      refine seq_clean (mid := entry + 820#64)
        (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
          (if (x.gChain.linksCap == 0#64) = true then emp
           else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun s5 =>
          s5.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s5 s0 ∧ s5.readReg64 .fp = s0.sp - 96#64 ∧
          s5.readReg64 .x8 = 0#64 ∧ s5.readReg64 .x9 = 0#64 ∧ s5.readReg64 .x19 = x.chainPtr ∧
          s5.readReg64 .x20 = x.out ∧ s5.readReg64 .x21 = BitVec.ofNat 64 len ∧
          s5.readReg64 .x22 = BitVec.ofNat 64 len ∧ s5.readReg64 .x23 = 0#64 ∧
          s5.readReg64 .x24 = newLinksPtr ∧ s5.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          s5.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
      · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
      · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hfp5, hx8_5, hx9_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hx28_5⟩
        exact hepilogue s5 newLinksPtr hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
          hn1 hn2 hn3 hpc5 hrun5 hsp5 htr5 hfp5 hx8_5 hx9_5 hx19_5 hx20_5 hx21_5 hx22_5
          hx23_5 hx24_5 hx26_5 hx28_5

/-! ## Prologue, Empty-Links Path, Allocation, and Entry Theorems -/

private theorem ofNat_len_mul_112_shift_eq {n : Nat} (hn : n * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 n <<< 7#64) - (BitVec.ofNat 64 n <<< 4#64) = BitVec.ofNat 64 (n * 112) := by
  have htn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h := cap_mul_112_shift_eq (BitVec.ofNat 64 n) (by rw [htn]; exact hn)
  rwa [htn] at h

private theorem ofNat_len_ls_cond {n : Nat} (hn : n * 112 < 2 ^ 63) :
    (!(!BitVec.ult (BitVec.ofNat 64 n) 82351536043346212#64 &&
      !(BitVec.ofNat 64 n - 82351536043346212#64 == 0#64))) = true := by
  have hn64 : n < 18446744073709551616 := by omega
  have hmax : (82351536043346212#64).toNat = 82351536043346212 := rfl
  rcases Nat.lt_or_eq_of_le (show n ≤ 82351536043346212 by omega) with hlt | rfl
  · have hu : BitVec.ult (BitVec.ofNat 64 n) 82351536043346212#64 = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, hmax, decide_eq_true_eq]
      exact hlt
    simp [hu]
  · rfl

private theorem stackAt_chainIntoPb_split_prologue (s0 : State) :
    stackAt s0.sp chainIntoPbStack =
      stackAt (s0.sp - 288#64) dropStack32 ∗ intoPbLoopScratchAt s0 ∗
      (∃∗ s00 : BitVec 64, (s0.sp - 288#64) ↦₆₄ s00) ∗ (∃∗ s08 : BitVec 64, (s0.sp - 280#64) ↦₆₄ s08) ∗
      (∃∗ s10 : BitVec 64, (s0.sp - 272#64) ↦₆₄ s10) ∗ (∃∗ sc0 : BitVec 64, (s0.sp - 96#64) ↦₆₄ sc0) ∗
      (∃∗ sc8 : BitVec 64, (s0.sp - 88#64) ↦₆₄ sc8) ∗ (∃∗ sd0 : BitVec 64, (s0.sp - 80#64) ↦₆₄ sd0) ∗
      (∃∗ sd8 : BitVec 64, (s0.sp - 72#64) ↦₆₄ sd8) ∗ (∃∗ se0 : BitVec 64, (s0.sp - 64#64) ↦₆₄ se0) ∗
      (∃∗ se8 : BitVec 64, (s0.sp - 56#64) ↦₆₄ se8) ∗ (∃∗ sf0 : BitVec 64, (s0.sp - 48#64) ↦₆₄ sf0) ∗
      (∃∗ sf8 : BitVec 64, (s0.sp - 40#64) ↦₆₄ sf8) ∗ (∃∗ s100 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s100) ∗
      (∃∗ s108 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s108) ∗ (∃∗ s110 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s110) ∗
      (∃∗ s118 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s118) := by
  rw [stackAt_chainIntoPb_split s0.sp]; unfold intoPbLoopScratchAt; ac_rfl

set_option maxHeartbeats 800000 in
theorem intoPb_prologue {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (x : ChainIntoPbCall) (s0 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc : s0.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.out) (hx0 : s0.readReg64 .x0 = x.chainPtr) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64) s0
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ stackAt s0.sp chainIntoPbStack)
      (fun s1 P1 =>
        (P1 ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          (if x.gChain.linksCap = 0 then emp
           else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
               x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32) ∧
        s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
        s1.readReg64 .x3 = x.gChain.linksCap ∧ s1.readReg64 .x19 = x.chainPtr ∧
        s1.readReg64 .x20 = x.out ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s1.readReg64 .x27 = x.gChain.linksHead ∧ s1.readReg64 .x28 = x.gChain.linksPtr) := by
  have hule := ofNat_len_ule_max_112 hl_new_lt
  have hls := ofNat_len_ls_cond hl_new_lt
  have hshift := ofNat_len_mul_112_shift_eq hl_new_lt
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  rw [stackAt_chainIntoPb_split_prologue s0]; wp_pull_exists
  unfold chainHeaderCellsAt; wp_steps
  unfold intoPbScratchAt calleeSavedFromPbAt; wp_done

theorem intoPb_empty_links {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hnil : x.chain.links = [])
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc1 : s1.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hepilogue := chainIntoPb_epilogue (A := A) (b := b) (ext := ext) hdealloc x s0
  have hlen0 : x.chain.links.length = 0 := by rw [hnil]; rfl
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by rw [hlen0]; decide
  have hdealloc_buf := vecDequeSlots_nil_entails_dealloc A x.gChain.linksCap x.gChain.linksPtr
    x.gChain.linksHead x.gChain.epochs x.chain.links hnil hl_cap_lt
  have hraw0 : (emp : SepProp) ⊢
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length := by
    unfold linksRawAllocAt; simp [hnil, arrayAt]; exact Entails.refl _
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hepilogue hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken hdealloc_buf (by sep_focus) ?_
  refine seq_clean (mid := entry + 820#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s2 =>
      s2.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s2 s0 ∧ s2.readReg64 .fp = s0.sp - 96#64 ∧
      s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x9 = 0#64 ∧ s2.readReg64 .x19 = x.chainPtr ∧
      s2.readReg64 .x20 = x.out ∧ s2.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧ s2.readReg64 .x23 = 0#64 ∧
      s2.readReg64 .x24 = 8#64 ∧ s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s2.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · rw [hlen0] at hx23_1 hx25_1 ⊢
    simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat] at hx23_1 hx25_1 ⊢
    wp_steps; rw [← emp_sepConj (memRegion x.out 80 ∗ _)]
    refine SepWP.focus_weaken hraw0 (by sep_focus) ?_
    rw [hlen0]; wp_done
  · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2⟩
    exact hepilogue s2 8#64 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt (by decide)
      hn1 hn2 hn3 hpc2 hrun2 hsp2 htr2 hfp2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2
      hx23_2 hx24_2 hx26_2 hx28_2

set_option maxHeartbeats 800000 in
theorem intoPb_alloc_step {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc1 : s1.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = x.gChain.linksHead)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (fun sm Pm =>
        sm.sp = s0.sp - 288#64 ∧ sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x3 = x.gChain.linksCap ∧ sm.readReg64 .x19 = x.chainPtr ∧
        sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        sm.readReg64 .x24 = 8#64 ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.gChain.linksHead ∧ sm.readReg64 .x28 = x.gChain.linksPtr ∧
        (if sm.readReg64 .x0 = 0 then
           sm.trace = s0.trace ++ [allocFailedEvent]
         else
           TraceCalleeSaved sm s0 ∧
           (Pm ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
             A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
             memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
             (if x.gChain.linksCap = 0 then emp
              else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
                vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
                  x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
             vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
             A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
             stackAt (s0.sp - 288#64) dropStack32))) := by
  rcases htr1 with ⟨htr1, hvr1⟩
  have hshim := hA.shim_ok_at chainIntoPbName
    (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb"),
            show libsignalSessionCode.fnOff shimName = num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") from (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := hA.alloc_ok_at chainIntoPbName
    (ls_rel% "<spqr::chain::Chain>::into_pb" "__rustc::__rust_alloc")
    (by rw [show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb"),
            show libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") from (ls_stub% "__rustc::__rust_alloc")])
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hcbz_23 : (BitVec.ofNat 64 (x.chain.links.length * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hl_new_lt
  have halign8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hsplit_stack : stackAt (s0.sp - 288#64) dropStack32 =
      stackAt (s0.sp - 288#64) allocHookStack ∗ memRegion (s0.sp - 4416#64) 32 := by
    rw [stackAt_dropStack32_split_allocHook, BitVec.sub_sub]; rfl
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, tripleRatchetProgAtExt, chainIntoPbName,
    sessionShimSpec, rustAllocSpec, BitVec.ofNat_eq_ofNat] at hshim halloc hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  rw [hsplit_stack]; unfold intoPbScratchAt; wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.chain.links.length * 112, 8)
  rw [‹sf.sp = s1.sp›, hsp1]; wp_steps
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro htr_a
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, and_self]
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro ⟨_, htr_a⟩
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [TraceCalleeSaved, Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, true_and, and_self]
    exact Entails.of_eq (by ac_rfl)

theorem intoPb_oom_panic {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (x : ChainIntoPbCall)
    (s0 sm : State) (Pm R : SepProp)
    (hpc : sm.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64)
    (hrun : sm.status = .Running) (hoom : sm.readReg64 .x0 = 0)
    (htr : sm.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (dropProgAtExt b ext) (s0.readReg64 .lr) sm Pm
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainIntoPbPinnedSpec A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hpanic := panic_at_handle_error_ext b ext chainIntoPbName
    (ls_rel% "<spqr::chain::Chain>::into_pb" "alloc::raw_vec::handle_error")
    (by rw [show libsignalSessionCode.fnOff chainIntoPbName = num% (ls_off% "<spqr::chain::Chain>::into_pb") from (ls_lemma% fnOff "<spqr::chain::Chain>::into_pb"),
            show libsignalSessionCode.fnOff handleErrorName = num% (ls_off% "alloc::raw_vec::handle_error") from (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 956
  dsimp only [dropProgAtExt, tripleRatchetProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hpanic hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP (mid := entry + (bv% (ls_rel% "<spqr::chain::Chain>::into_pb" "alloc::raw_vec::handle_error"))) ?_
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      (entry + (bv% (ls_rel% "<spqr::chain::Chain>::into_pb" "alloc::raw_vec::handle_error"))) sm Pm
      (fun sp Pp => Pp = Pm ∧ sp.trace = sm.trace) := by
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩
  refine SepWP.mono hstep ?_
  rintro sp Pp hpcp hrunp ⟨rfl, htrp⟩
  have hext_at : (libsignalSessionCode.rebase b (Rust.withPanics ext)).externAt? sp.pc =
      some Rust.panicked := by rw [hpcp]; exact hpanic
  refine SepWPp.panic hrunp hext_at fun hm => allowPanic_panicked ?_ hm
  have htr_pan : (Rust.panicked sp).trace = s0.trace ++ [allocFailedEvent] := htrp.trans htr
  refine ⟨?_, ⟨[allocFailedEvent], htr_pan.symm⟩⟩
  unfold allocFailedIn; simp [htrp, htr]

theorem intoPb_post_alloc_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext)
    (x : ChainIntoPbCall) (s0 sm : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_head : if x.gChain.linksCap = 0 then x.gChain.linksHead = 0
               else x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpcm : sm.pc = (dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 288#64) (htrm : TraceCalleeSaved sm s0)
    (hfpm : sm.readReg64 .fp = s0.sp - 96#64) (hx0m_ne : sm.readReg64 .x0 ≠ 0)
    (hx3m : sm.readReg64 .x3 = x.gChain.linksCap) (hx19m : sm.readReg64 .x19 = x.chainPtr)
    (hx20m : sm.readReg64 .x20 = x.out)
    (hx22m : sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24m : sm.readReg64 .x24 = 8#64)
    (hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26m : sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27m : sm.readReg64 .x27 = x.gChain.linksHead)
    (hx28m : sm.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP (dropProgAtExt b ext) (s0.readReg64 .lr) sm
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
        memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hcap_ne0 : x.gChain.linksCap ≠ 0#64 := by
    intro h0; rw [h0] at hl_le; change x.chain.links.length ≤ 0 at hl_le; omega
  have hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat := by
    simpa only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte] using hl_head
  simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte, sepConj_assoc]
  have hnonwrap_lem := intoPb_post_alloc_nonwrap (A := A) (b := b) (ext := ext) hdealloc
    x s0 (sm.setPC ((dropProgAtExt b ext).fnAddr chainIntoPbName + 156#64)) (sm.readReg64 .x0)
  have hwrap_lem := intoPb_post_alloc_wrap (A := A) (b := b) (ext := ext) hdealloc
    x s0 (sm.setPC ((dropProgAtExt b ext).fnAddr chainIntoPbName + 156#64)) (sm.readReg64 .x0)
  have hcbz_x0 : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0m_ne
  have hcbz_x25 : (BitVec.ofNat 64 x.chain.links.length == 0#64) = false :=
    ofNat_beq_zero_false_of_lt (by omega) (by omega)
  code_fetches_sym libsignalSessionCode libsignalSessionBin b (Rust.withPanics ext) "<spqr::chain::Chain>::into_pb" 156
  dsimp only [dropProgAtExt, chainIntoPbName, BitVec.ofNat_eq_ofNat] at hnonwrap_lem hwrap_lem hpcm ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::chain::Chain>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  by_cases hnw : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat
  · exact hnonwrap_lem hsp0_align hlen hlen_pos hl_le hl_cap_lt hl_cap_ne hhead_lt
      hnw hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
      hx24m hx25m hx26m hx27m hx28m
  · exact hwrap_lem hsp0_align hlen hl_le hl_cap_lt hl_cap_ne hhead_lt
      (by omega) hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
      hx24m hx25m hx26m hx27m hx28m

set_option maxHeartbeats 800000 in
theorem chain_into_pb_pinned_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    ChainIntoPbPinnedOkExt b A ext := by
  have hdealloc : DeallocOkExt b A ext := hA.dealloc
  unfold ChainIntoPbPinnedOkExt
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align =>
    ⟨(chainIntoPbPinnedSpec A).pre x s0, R, hpre, ?_⟩
  dsimp only [State.spAligned] at hsp_align
  refine SepWPp.of_sepWP (mid := (dropProgAtExt b ext).fnAddr chainIntoPbName + 116#64) ?_
  wp_conv_pre => dsimp only [chainIntoPbPinnedSpec]
  wp_focus_pure
  rintro ⟨hx8, hx0⟩
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (chainAt_unpack A x.chainPtr x.gChain x.chain))) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_cap_lt, hl_cap_ne, hl_head, hn1, hn2, hn3⟩
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by omega
  wp_simp_pre [sepConj_assoc]
  refine SepWP.mono (intoPb_prologue x s0 hsp_align hl_new_lt hpc hrun hx8 hx0) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hfp1, hx3_1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  refine SepWPp.weaken_pre hP1 ?_
  by_cases hnil : x.chain.links = []
  · refine SepWPp.of_sepWP_ret ?_
    refine SepWP.mono (intoPb_empty_links hdealloc x s0 s1 hsp_align hnil hlen hl_cap_lt hl_cap_ne
      hn1 hn2 hn3 hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx28_1) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
    refine ⟨fun hm => ?_, hspf, hcsf⟩
    dsimp only [chainIntoPbPinnedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩
  · have hlen_pos : 1 ≤ x.chain.links.length := Nat.pos_of_ne_zero (List.length_pos_iff.mpr hnil).ne'
    refine SepWPp.of_sepWP (mid := (dropProgAtExt b ext).fnAddr chainIntoPbName + 148#64) ?_
    refine SepWP.mono (intoPb_alloc_step hA x s0 s1 hsp_align hlen_pos hl_new_lt
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1) ?_
    rintro sm Pm hpcm hrunm ⟨hspm, hfpm, hx3m, hx19m, hx20m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hbranch⟩
    by_cases hoom : sm.readReg64 .x0 = 0
    · simp only [hoom, ↓reduceIte] at hbranch
      exact intoPb_oom_panic (A := A) x s0 sm Pm R hpcm hrunm hoom hbranch
    · simp only [hoom, ↓reduceIte] at hbranch
      refine SepWPp.weaken_pre hbranch.2 ?_
      refine SepWPp.of_sepWP_ret ?_
      refine SepWP.mono (intoPb_post_alloc_ok hdealloc x s0 sm hsp_align hlen_pos hlen hl_le
        hl_cap_lt hl_cap_ne hl_head hn1 hn2 hn3 hpcm hrunm hspm hbranch.1 hfpm hoom hx3m
        hx19m hx20m hx22m hx24m hx25m hx26m hx27m hx28m) ?_
      rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      dsimp only [chainIntoPbPinnedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩

theorem chain_into_pb_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    ChainIntoPbOkExt b A ext := by
  have hpinned := chain_into_pb_pinned_ok_ext hA
  unfold ChainIntoPbOkExt; apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbSpec] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chain_into_pb_pinned_ok_ext_X {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName) (chainIntoPbPinnedSpecX A) := by
  have hpinned := chain_into_pb_pinned_ok_ext hA
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (chainIntoPbPinnedSpec A).pre x s0 ∗
      (memRegion (s0.sp - 16672#64) 12256 ∗ R) := by
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbPinnedSpec] at hpre ⊢
    rw [stackAt_chainIntoPbX_split s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (subroutine_ok_apply_outcome hpinned x
    (memRegion (s0.sp - 16672#64) 12256 ∗ R) hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

theorem chain_into_pb_ok_ext_X {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName) (chainIntoPbSpecX A) := by
  have hpinned := chain_into_pb_pinned_ok_ext_X hA
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbSpecX] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chain_into_pb_pinned_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    ChainIntoPbPinnedOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img (chain_into_pb_pinned_ok_ext_X hA)

theorem chain_into_pb_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    ChainIntoPbOkX img A ext :=
  subroutine_ok_inImage_of_subroutine_ok img (chain_into_pb_ok_ext_X hA)

/-! ## Relocatable `[LibsignalPlacement]` Proofs (Block `365`) -/

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_nonwrap_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length) (hl_pos : 1 ≤ x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hnonwrap : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let srcBase := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 (cap - head) :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hult_hi_false : BitVec.ult (BitVec.ofNat 64 (cap - head)) (BitVec.ofNat 64 len) = false :=
    nonwrap_ult_hi_false hnonwrap (by omega)
  have hhi_false :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head))) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 (cap - head))) = false :=
    nonwrap_hi_false hnonwrap (by omega)
  have hhead_ne_end : (x.gChain.linksHead == x.gChain.linksHead + BitVec.ofNat 64 len) = false :=
    nonwrap_head_ne_end x.gChain.linksHead hl_pos (by omega)
  have hmin_eq :
      (if BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head)) = true
       then BitVec.ofNat 64 len else BitVec.ofNat 64 (cap - head)) = BitVec.ofNat 64 len :=
    nonwrap_min_eq_len hnonwrap (by omega)
  have hlsl_len : (BitVec.ofNat 64 len <<< (7 : Nat)) - (BitVec.ofNat 64 len <<< (4 : Nat)) =
      BitVec.ofNat 64 (len * 112) := mul_112_shift_eq len hl_new_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh := umulh_div112_sub_112 hl_pos hl_new_lt
  have hadd1 := ofNat_sub_one_add_one hl_pos
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hslots := vecDequeSlots_nonwrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt (by rw [hzlen]; exact hnonwrap)
  rw [hzlen] at hslots
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A H x.chain.links x.gChain.epochs [] [] s0
  have hepilogue := @chainIntoPb_epilogue_placed _ A H hdealloc hdrop x s0
  refine seq_clean (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (len * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase (x.gChain.epochs.zip x.chain.links) ∗
      memRegion x.gChain.linksPtr (head * 112) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 len ∧ s1.readReg64 .x9 = 0#64 ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x12 = BitVec.ofNat 64 (len * 112) ∧
      s1.readReg64 .x13 = s0.sp - 160#64 ∧ s1.readReg64 .x14 = s0.sp - 208#64 ∧
      s1.readReg64 .x15 = s0.sp - 260#64 ∧ s1.readReg64 .x16 = newLinksPtr + 52#64 ∧
      s1.readReg64 .x17 = srcBase + 56#64 ∧ s1.readReg64 .x19 = x.chainPtr ∧
      s1.readReg64 .x20 = x.out ∧ s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 (cap - head)).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_false hhead_ne_end
      simp only [hult_hi_false, Bool.false_eq_true, ↓reduceIte, hhead_ne_end]
    have humulh_norm :
        BitVec.truncate 64
          ((BitVec.zeroExtend 128 ((BitVec.ofNat 64 (len * 112) - 112#64) >>> 4) *
            2635249153387078803#128) >>> 64) = BitVec.ofNat 64 (len - 1) := by
      simpa using umulh_div112_sub_112 hl_pos hl_new_lt
    dsimp only [len] at hult_hi_false hhi_false hhead_ne_end hmin_eq hlsl_len humulh humulh_norm hadd1
    wp_steps; dsimp only [srcBase]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase newLinksPtr hsp0_align
      hl_pos hlen rfl (by simpa using hl_new_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 hx12_1 hx13_1 hx14_1 hx15_1
      (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
          memRegion x.gChain.linksPtr (head * 112) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    have hjoin_old := memRegion_nonwrap_join x.gChain.linksPtr cap head len hl_cap_lt (Nat.le_of_lt hhead_lt) hnonwrap
    have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
      unfold linksRawAllocAt
      have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
        absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
      have htn : (BitVec.ofNat 64 len).toNat = len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
      exact Entails.refl _
    refine SepWP.weaken_pre hP2 ?_
    refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase]; sep_focus) ?_
    refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_365).base + 820#64)
      (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = 0#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x21 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 len ∧ s3.readReg64 .x23 = 0#64 ∧
        s3.readReg64 .x24 = newLinksPtr ∧ s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
    · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3⟩
      exact hepilogue s3 newLinksPtr hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
        hn1 hn2 hn3 hpc3 hrun3 hsp3 htr3 hfp3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx22_3
        hx23_3 hx24_3 hx26_3 hx28_3

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_wrap_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hwrap : x.gChain.linksCap.toNat - x.gChain.linksHead.toNat < x.chain.links.length)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let m₁ := cap - head
  let m₂ := len - m₁
  let srcBase1 := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  let rem1 := x.chain.links.take m₁
  let rem1G := x.gChain.epochs.take m₁
  let rem2 := x.chain.links.drop m₁
  let rem2G := x.gChain.epochs.drop m₁
  have hm1_pos : 1 ≤ m₁ := by omega
  have hm2_pos : 1 ≤ m₂ := by omega
  have hm_sum : m₁ + m₂ = len := by omega
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hm1_lt : m₁ * 112 < 2 ^ 63 := by omega
  have hm2_lt : m₂ * 112 < 2 ^ 63 := by omega
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hhead_ne_cap : (x.gChain.linksHead == x.gChain.linksCap) = false := by
    rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hhead_lt; exact Nat.lt_irrefl _ hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 m₁ :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hlen_sub_m1 : BitVec.ofNat 64 len - BitVec.ofNat 64 m₁ = BitVec.ofNat 64 m₂ :=
    wrap_len_sub_m1 (Nat.le_of_lt hwrap) (by omega)
  have hlsl_m2 : (BitVec.ofNat 64 m₂ <<< (7 : Nat)) - (BitVec.ofNat 64 m₂ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₂ * 112) := mul_112_shift_eq m₂ hm2_lt
  have hult_hi_true : BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = true :=
    wrap_ult_hi_true hwrap (by omega)
  have hhi_true :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = true := wrap_hi_true hwrap (by omega)
  have hult_false : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false :=
    wrap_ult_false hwrap (by omega)
  have hlsl_m1 : (BitVec.ofNat 64 m₁ <<< (7 : Nat)) - (BitVec.ofNat 64 m₁ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₁ * 112) := mul_112_shift_eq m₁ hm1_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh1 := umulh_div112_sub_112 hm1_pos hm1_lt
  have humulh1_norm := umulh_div112_sub_112_norm hm1_pos hm1_lt
  have hadd1_m1 := ofNat_sub_one_add_one hm1_pos
  have hm2_cbz_false : (BitVec.ofNat 64 (m₂ * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hm2_lt
  have humulh2 := umulh_div112_sub_112 hm2_pos hm2_lt
  have humulh2_norm := umulh_div112_sub_112_norm hm2_pos hm2_lt
  have hmadd_dst := madd_m1_112_add_52 newLinksPtr m₁
  have hadd_x2 := add_m1_m2_sub_one hm2_pos hm_sum
  have hadd_x8 := add_m2_sub_one_m1 hm2_pos hm_sum
  have hrem1_len : rem1.length = m₁ := List.length_take_of_le (by omega)
  have hrem1G_len : rem1G.length = m₁ := List.length_take_of_le (by omega)
  have hrem2_len : rem2.length = m₂ := by dsimp [rem2]; rw [List.length_drop]
  have hrem2G_len : rem2G.length = m₂ := by dsimp [rem2G]; rw [List.length_drop, hlen]
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hzip_take : (x.gChain.epochs.zip x.chain.links).take m₁ = rem1G.zip rem1 :=
    take_zip_eq m₁ x.gChain.epochs x.chain.links
  have hzip_drop : (x.gChain.epochs.zip x.chain.links).drop m₁ = rem2G.zip rem2 :=
    drop_zip_eq m₁ x.gChain.epochs x.chain.links
  have hslots := vecDequeSlots_wrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt
    (by rw [hzlen]; exact hl_le) (by rw [hzlen]; exact hwrap)
  rw [hzlen, hzip_take, hzip_drop] at hslots
  have hsplit_dst : memRegion newLinksPtr (len * 112) =
      memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) := by
    have hmul_sum : len * 112 = m₁ * 112 + m₂ * 112 := by rw [← Nat.add_mul, hm_sum]
    conv_lhs => rw [hmul_sum]
    exact ProofLib.memRegion_split' (b := newLinksPtr) (n := m₁ * 112) (k := m₂ * 112)
      (b' := newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) rfl rfl (by omega)
  rw [hsplit_dst]
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A H rem1 rem1G [] [] s0
  have hloop2 := @intoPb_loop2_run_placed _ A H rem2 rem2G rem1G rem1 s0
  have hepilogue := @chainIntoPb_epilogue_placed _ A H hdealloc hdrop x s0
  refine seq_clean (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase1 (rem1G.zip rem1) ∗
      arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧ s1.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x11 = 0x2492492492492493#64 ∧
      s1.readReg64 .x12 = BitVec.ofNat 64 (m₁ * 112) ∧ s1.readReg64 .x13 = s0.sp - 160#64 ∧
      s1.readReg64 .x14 = s0.sp - 208#64 ∧ s1.readReg64 .x15 = s0.sp - 260#64 ∧
      s1.readReg64 .x16 = newLinksPtr + 52#64 ∧ s1.readReg64 .x17 = srcBase1 + 56#64 ∧
      s1.readReg64 .x19 = x.chainPtr ∧ s1.readReg64 .x20 = x.out ∧
      s1.readReg64 .x22 = BitVec.ofNat 64 len ∧ s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 m₁).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_true; simp only [hult_hi_true, ↓reduceIte, hhead_ne_cap]
    dsimp only [len] at hlen_sub_m1 hult_hi_true hhi_true hult_false
    wp_steps; dsimp only [srcBase1]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase1 newLinksPtr hsp0_align
      (by rw [hrem1_len]; exact hm1_pos) (by rw [hrem1G_len, hrem1_len]) rfl
      (by rw [List.length_nil, Nat.zero_add, hrem1_len]; exact hm1_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 (by rw [hrem1_len]; exact hx12_1)
      hx13_1 hx14_1 hx15_1 (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append, hrem1_len] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx3_1] at hx3_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2; rw [hx11_1] at hx11_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    refine SepWP.weaken_pre hP2 ?_
    refine seq_clean (mid := (blkPl_365).base + 512#64)
      (P_mid := memRegion srcBase1 (m₁ * 112) ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((rem1G.map toChainEpochPBGhost).zip (rem1.map chainEpochIntoPb)) ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32))
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x0 = newLinksPtr ∧ s3.readReg64 .x2 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x3 = x.gChain.linksCap ∧ s3.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧
        s3.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧ s3.readReg64 .x10 = s0.sp - 160#64 ∧
        s3.readReg64 .x11 = BitVec.ofNat 64 (m₂ - 1) ∧ s3.readReg64 .x12 = s0.sp - 160#64 ∧
        s3.readReg64 .x13 = s0.sp - 208#64 ∧ s3.readReg64 .x14 = s0.sp - 260#64 ∧
        s3.readReg64 .x15 = newLinksPtr + BitVec.ofNat 64 (m₁ * 112) + 52#64 ∧
        s3.readReg64 .x16 = x.gChain.linksPtr + 56#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · wp_steps; wp_done
    · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hfp3, hx0_3, hx2_3, hx3_3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3, hx15_3, hx16_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3⟩
      have h0_bv : BitVec.ofNat 64 0 = 0#64 := rfl
      have hrun_l2 := hloop2 s3 x.gChain x.chain x.gChain.linksPtr newLinksPtr m₁ hsp0_align
        (by rw [hrem2_len]; exact hm2_pos) (by rw [hrem2G_len, hrem2_len])
        (by rw [hrem1G_len, hrem1_len]) (by rw [hrem1_len])
        (by rw [hrem1_len, hrem2_len, hm_sum]; exact hl_new_lt)
        hpc3 hrun3 hsp3 htr3 hfp3 (by rw [hrem2_len]; exact hx9_3)
        hx10_3 hx12_3 hx13_3 hx14_3 (by rw [hrem1_len]; exact hx15_3)
        (by rw [hrem1_len, Nat.sub_self, Nat.zero_mul, h0_bv, BitVec.add_zero]; exact hx16_3)
      have happG : rem1G ++ rem2G = x.gChain.epochs := List.take_append_drop m₁ x.gChain.epochs
      have happ : rem1 ++ rem2 = x.chain.links := List.take_append_drop m₁ x.chain.links
      simp only [hrem1_len, hrem2_len, Nat.sub_self, Nat.zero_mul, Nat.zero_add,
        memRegion_zero, emp_sepConj, h0_bv, BitVec.add_zero, happG, happ] at hrun_l2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (SepWP.seq (SepWP.frame_post_entails (F :=
          memRegion srcBase1 (m₁ * 112) ∗ memRegion x.out 80 ∗
            chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
            A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
            memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
            vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
            A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l2) ?_)
      rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hfp4, hx0_4, hx2_4, hx3_4, hx8_4, hx11_4, hcs4⟩
      rw [hx0_3] at hx0_4; rw [hx2_3] at hx2_4; rw [hx3_3] at hx3_4; rw [hx8_3] at hx8_4; rw [hx11_3] at hx11_4
      have hx19_4 : s4.readReg64 .x19 = x.chainPtr := (hcs4.1).trans hx19_3
      have hx20_4 : s4.readReg64 .x20 = x.out := (hcs4.2.1).trans hx20_3
      have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 len := (hcs4.2.2.2.1).trans hx22_3
      have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 len := (hcs4.2.2.2.2.2.2.1).trans hx25_3
      have hx26_4 : s4.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx28_4 : s4.readReg64 .x28 = x.gChain.linksPtr := (hcs4.2.2.2.2.2.2.2.2.2.1).trans hx28_3
      have hjoin_old := memRegion_wrap_join x.gChain.linksPtr cap head len hl_cap_lt hhead_lt hl_le hwrap
      have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
        unfold linksRawAllocAt
        have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
          absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
        have htn : (BitVec.ofNat 64 len).toNat = len := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
        exact Entails.refl _
      refine SepWP.weaken_pre hP4 ?_
      refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase1, m₁, m₂]; sep_focus) ?_
      refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
      refine seq_clean (mid := (blkPl_365).base + 820#64)
        (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
          (if (x.gChain.linksCap == 0#64) = true then emp
           else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun s5 =>
          s5.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s5 s0 ∧ s5.readReg64 .fp = s0.sp - 96#64 ∧
          s5.readReg64 .x8 = 0#64 ∧ s5.readReg64 .x9 = 0#64 ∧ s5.readReg64 .x19 = x.chainPtr ∧
          s5.readReg64 .x20 = x.out ∧ s5.readReg64 .x21 = BitVec.ofNat 64 len ∧
          s5.readReg64 .x22 = BitVec.ofNat 64 len ∧ s5.readReg64 .x23 = 0#64 ∧
          s5.readReg64 .x24 = newLinksPtr ∧ s5.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          s5.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
      · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
      · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hfp5, hx8_5, hx9_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hx28_5⟩
        exact hepilogue s5 newLinksPtr hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
          hn1 hn2 hn3 hpc5 hrun5 hsp5 htr5 hfp5 hx8_5 hx9_5 hx19_5 hx20_5 hx21_5 hx22_5
          hx23_5 hx24_5 hx26_5 hx28_5

set_option maxHeartbeats 800000 in
theorem intoPb_prologue_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (x : ChainIntoPbCall) (s0 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc : s0.pc = (blkPl_365).base) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = x.out) (hx0 : s0.readReg64 .x0 = x.chainPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      ((blkPl_365).base + 116#64) s0
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ stackAt s0.sp chainIntoPbStack)
      (fun s1 P1 =>
        (P1 ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          (if x.gChain.linksCap = 0 then emp
           else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
               x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32) ∧
        s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
        s1.readReg64 .x3 = x.gChain.linksCap ∧ s1.readReg64 .x19 = x.chainPtr ∧
        s1.readReg64 .x20 = x.out ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s1.readReg64 .x27 = x.gChain.linksHead ∧ s1.readReg64 .x28 = x.gChain.linksPtr) := by
  have hule := ofNat_len_ule_max_112 hl_new_lt
  have hls := ofNat_len_ls_cond hl_new_lt
  have hshift := ofNat_len_mul_112_shift_eq hl_new_lt
  rw [stackAt_chainIntoPb_split_prologue s0]; wp_pull_exists
  unfold chainHeaderCellsAt; wp_steps
  unfold intoPbScratchAt calleeSavedFromPbAt; wp_done

theorem intoPb_empty_links_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hnil : x.chain.links = [])
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc1 : s1.pc = (blkPl_365).base + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hepilogue := @chainIntoPb_epilogue_placed _ A H hdealloc hdrop x s0
  have hlen0 : x.chain.links.length = 0 := by rw [hnil]; rfl
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by rw [hlen0]; decide
  have hdealloc_buf := vecDequeSlots_nil_entails_dealloc A x.gChain.linksCap x.gChain.linksPtr
    x.gChain.linksHead x.gChain.epochs x.chain.links hnil hl_cap_lt
  have hraw0 : (emp : SepProp) ⊢
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length := by
    unfold linksRawAllocAt; simp [hnil, arrayAt]; exact Entails.refl _
  refine SepWP.focus_weaken hdealloc_buf (by sep_focus) ?_
  refine seq_clean (mid := (blkPl_365).base + 820#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s2 =>
      s2.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s2 s0 ∧ s2.readReg64 .fp = s0.sp - 96#64 ∧
      s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x9 = 0#64 ∧ s2.readReg64 .x19 = x.chainPtr ∧
      s2.readReg64 .x20 = x.out ∧ s2.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧ s2.readReg64 .x23 = 0#64 ∧
      s2.readReg64 .x24 = 8#64 ∧ s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s2.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · rw [hlen0] at hx23_1 hx25_1 ⊢
    simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat] at hx23_1 hx25_1 ⊢
    wp_steps; rw [← emp_sepConj (memRegion x.out 80 ∗ _)]
    refine SepWP.focus_weaken hraw0 (by sep_focus) ?_
    rw [hlen0]; wp_done
  · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2⟩
    exact hepilogue s2 8#64 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt (by decide)
      hn1 hn2 hn3 hpc2 hrun2 hsp2 htr2 hfp2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2
      hx23_2 hx24_2 hx26_2 hx28_2

set_option maxHeartbeats 800000 in
theorem intoPb_alloc_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hpc1 : s1.pc = (blkPl_365).base + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27_1 : s1.readReg64 .x27 = x.gChain.linksHead)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      ((blkPl_365).base + 148#64) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (fun sm Pm =>
        sm.sp = s0.sp - 288#64 ∧ sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x3 = x.gChain.linksCap ∧ sm.readReg64 .x19 = x.chainPtr ∧
        sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112) ∧
        sm.readReg64 .x24 = 8#64 ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.gChain.linksHead ∧ sm.readReg64 .x28 = x.gChain.linksPtr ∧
        (if sm.readReg64 .x0 = 0 then
           sm.trace = s0.trace ++ [allocFailedEvent]
         else
           TraceCalleeSaved sm s0 ∧
           (Pm ⊢ memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
             A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
             memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
             (if x.gChain.linksCap = 0 then emp
              else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
                vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
                  x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
             vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
             A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
             stackAt (s0.sp - 288#64) dropStack32))) := by
  rcases htr1 with ⟨htr1, hvr1⟩
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hcbz_23 : (BitVec.ofNat 64 (x.chain.links.length * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hl_new_lt
  have halign8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hsplit_stack : stackAt (s0.sp - 288#64) dropStack32 =
      stackAt (s0.sp - 288#64) allocHookStack ∗ memRegion (s0.sp - 4416#64) 32 := by
    rw [stackAt_dropStack32_split_allocHook, BitVec.sub_sub]; rfl
  dsimp only [sessionShimSpec, rustAllocSpec, BitVec.ofNat_eq_ofNat] at hshim halloc ⊢
  rw [hsplit_stack]; unfold intoPbScratchAt; wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (x.chain.links.length * 112, 8)
  rw [‹sf.sp = s1.sp›, hsp1]; wp_steps
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro htr_a
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, and_self]
  · simp only [hoom, ↓reduceIte]
    wp_focus_pure; rintro ⟨_, htr_a⟩
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    simp only [TraceCalleeSaved, Reg.x0, Reg.x3, Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25,
      Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm, *, ↓reduceIte, true_and, and_self]
    exact Entails.of_eq (by ac_rfl)

theorem intoPb_oom_panic_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (x : ChainIntoPbCall)
    (s0 sm : State) (Pm R : SepProp)
    (hpc : sm.pc = (blkPl_365).base + 148#64)
    (hrun : sm.status = .Running) (hoom : sm.readReg64 .x0 = 0)
    (htr : sm.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) sm Pm
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (chainIntoPbPinnedSpec A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") ?_
  have hstep : SepWP ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") sm Pm
      (fun sp Pp => Pp = Pm ∧ sp.trace = sm.trace) := by
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨rfl, rfl⟩
  refine SepWP.mono hstep ?_
  rintro sp Pp hpcp hrunp ⟨rfl, htrp⟩
  have hext_at : ((blkPC_365).rebase (blkPl_365).base H).externAt? sp.pc =
      some Rust.panicked := by rw [hpcp]; exact hpan_oom
  refine SepWPp.panic hrunp hext_at fun hm => allowPanic_panicked ?_ hm
  have htr_pan : (Rust.panicked sp).trace = s0.trace ++ [allocFailedEvent] := htrp.trans htr
  refine ⟨?_, ⟨[allocFailedEvent], htr_pan.symm⟩⟩
  unfold allocFailedIn; simp [htrp, htr]

theorem intoPb_post_alloc_ok_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (x : ChainIntoPbCall) (s0 sm : State)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_head : if x.gChain.linksCap = 0 then x.gChain.linksHead = 0
               else x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpcm : sm.pc = (blkPl_365).base + 148#64)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 288#64) (htrm : TraceCalleeSaved sm s0)
    (hfpm : sm.readReg64 .fp = s0.sp - 96#64) (hx0m_ne : sm.readReg64 .x0 ≠ 0)
    (hx3m : sm.readReg64 .x3 = x.gChain.linksCap) (hx19m : sm.readReg64 .x19 = x.chainPtr)
    (hx20m : sm.readReg64 .x20 = x.out)
    (hx22m : sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24m : sm.readReg64 .x24 = 8#64)
    (hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26m : sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27m : sm.readReg64 .x27 = x.gChain.linksHead)
    (hx28m : sm.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) sm
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
        memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hcap_ne0 : x.gChain.linksCap ≠ 0#64 := by
    intro h0; rw [h0] at hl_le; change x.chain.links.length ≤ 0 at hl_le; omega
  have hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat := by
    simpa only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte] using hl_head
  simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte, sepConj_assoc]
  have hnonwrap_lem := intoPb_post_alloc_nonwrap_placed (A := A) (H := H) hdealloc hdrop
    x s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0)
  have hwrap_lem := intoPb_post_alloc_wrap_placed (A := A) (H := H) hdealloc hdrop
    x s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0)
  have hcbz_x0 : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0m_ne
  have hcbz_x25 : (BitVec.ofNat 64 x.chain.links.length == 0#64) = false :=
    ofNat_beq_zero_false_of_lt (by omega) (by omega)
  refine seq_clean (mid := (blkPl_365).base + 156#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
      memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
      A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
      vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
        x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 => s1 = sm.setPC ((blkPl_365).base + 156#64)) ?_ ?_
  · wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, rfl⟩
  · rintro _ _ _ rfl
    by_cases hnw : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat
    · exact hnonwrap_lem hsp0_align hlen hlen_pos hl_le hl_cap_lt hl_cap_ne hhead_lt
        hnw hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m
    · exact hwrap_lem hsp0_align hlen hl_le hl_cap_lt hl_cap_ne hhead_lt
        (by omega) hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `chainIntoPbPinnedSpec A`. -/
theorem chain_into_pb_pinned_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (chainIntoPbPinnedSpec A) := by
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align =>
    ⟨(chainIntoPbPinnedSpec A).pre x s0, R, hpre, ?_⟩
  dsimp only [State.spAligned] at hsp_align
  refine SepWPp.of_sepWP (mid := (blkPl_365).base + 116#64) ?_
  wp_conv_pre => dsimp only [chainIntoPbPinnedSpec]
  wp_focus_pure
  rintro ⟨hx8, hx0⟩
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (chainAt_unpack A x.chainPtr x.gChain x.chain))) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_cap_lt, hl_cap_ne, hl_head, hn1, hn2, hn3⟩
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by omega
  wp_simp_pre [sepConj_assoc]
  refine SepWP.mono (intoPb_prologue_placed x s0 hsp_align hl_new_lt hpc hrun hx8 hx0) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hfp1, hx3_1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  refine SepWPp.weaken_pre hP1 ?_
  by_cases hnil : x.chain.links = []
  · refine SepWPp.of_sepWP_ret ?_
    refine SepWP.mono (intoPb_empty_links_placed hdealloc hdrop x s0 s1 hsp_align hnil hlen hl_cap_lt hl_cap_ne
      hn1 hn2 hn3 hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx28_1) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
    refine ⟨fun hm => ?_, hspf, hcsf⟩
    dsimp only [chainIntoPbPinnedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩
  · have hlen_pos : 1 ≤ x.chain.links.length := Nat.pos_of_ne_zero (List.length_pos_iff.mpr hnil).ne'
    refine SepWPp.of_sepWP (mid := (blkPl_365).base + 148#64) ?_
    refine SepWP.mono (intoPb_alloc_step_placed hshim halloc x s0 s1 hsp_align hlen_pos hl_new_lt
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1) ?_
    rintro sm Pm hpcm hrunm ⟨hspm, hfpm, hx3m, hx19m, hx20m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hbranch⟩
    by_cases hoom : sm.readReg64 .x0 = 0
    · simp only [hoom, ↓reduceIte] at hbranch
      exact intoPb_oom_panic_placed (A := A) hpan_oom x s0 sm Pm R hpcm hrunm hoom hbranch
    · simp only [hoom, ↓reduceIte] at hbranch
      refine SepWPp.weaken_pre hbranch.2 ?_
      refine SepWPp.of_sepWP_ret ?_
      refine SepWP.mono (intoPb_post_alloc_ok_placed hdealloc hdrop x s0 sm hsp_align hlen_pos hlen hl_le
        hl_cap_lt hl_cap_ne hl_head hn1 hn2 hn3 hpcm hrunm hspm hbranch.1 hfpm hoom hx3m
        hx19m hx20m hx22m hx24m hx25m hx26m hx27m hx28m) ?_
      rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      dsimp only [chainIntoPbPinnedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩

/-- Relocatable `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `chainIntoPbSpec A`. -/
theorem chain_into_pb_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (chainIntoPbSpec A) := by
  have hpinned := chain_into_pb_pinned_placed_ok hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbSpec] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Relocatable `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `chainIntoPbPinnedSpecX A`. -/
theorem chain_into_pb_pinned_placed_ok_X [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (chainIntoPbPinnedSpecX A) := by
  have hpinned := chain_into_pb_pinned_placed_ok hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (chainIntoPbPinnedSpec A).pre x s0 ∗
      (memRegion (s0.sp - 16672#64) 12256 ∗ R) := by
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbPinnedSpec] at hpre ⊢
    rw [stackAt_chainIntoPbX_split s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (subroutine_ok_apply_outcome hpinned x
    (memRegion (s0.sp - 16672#64) 12256 ∗ R) hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

/-- Relocatable `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `chainIntoPbSpecX A`. -/
theorem chain_into_pb_placed_ok_X [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec A))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (chainIntoPbSpecX A) := by
  have hpinned := chain_into_pb_pinned_placed_ok_X hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [chainIntoPbPinnedSpecX, chainIntoPbSpecX] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.ChainProofs
