/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
public import LibsignalBinary.Proofs.E2E.InMem.SessionStoreImpl.ReprBridge
import GeneratedLean.LibsignalSessionCode -- shake: keep

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli

/-- Maximum sub-callee stack budget needed below `load_session::{closure#0}`'s `0x350` frame. -/
abbrev subMax (addrStk getStk : Nat) : Nat :=
  max (max addrStk getStk) (max E2E.Record.recDeserializeStack extHookStack)

/-- Minimum stack budget of `load_session::{closure#0}` (`0x350` frame + `subMax`). -/
abbrev pollMinStk (addrStk getStk : Nat) : Nat :=
  0x350 + subMax addrStk getStk

private theorem q128_hi_lo (q : BitVec 128) :
    q.extractLsb' 64 64 ++ q.extractLsb' 0 64 = q := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', Nat.zero_add]
  split
  · rfl
  · show q[64 + (i - 64)] = q[i]
    congr 1; omega

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {k m : Nat} (hle : k ≤ m) (hm : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  have heq : m = k + (m - k) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp k (m - k) (by omega), ← heq]

theorem memRegion_16_q128 (a : BitVec 64) :
    memRegion a 16 = (∃∗ q : BitVec 128, (a ↦₁₂₈ q)) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun w1 => Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right (w1 ++ w0) (Entails.of_eq (pointsTo64_pair a w0 w1))
  · refine Entails.sepExists_elim fun q => ?_
    refine Entails.sepExists_right (q.extractLsb' 64 64)
      (Entails.sepExists_right (q.extractLsb' 0 64) ?_)
    exact Entails.of_eq (by rw [pointsTo64_pair, q128_hi_lo])

theorem q128_entails_memRegion16 (a : BitVec 64) (q : BitVec 128) :
    (a ↦₁₂₈ q) ⊢ memRegion a 16 := by
  rw [memRegion_16_q128 a]
  exact Entails.sepExists_right q (Entails.refl _)

/-- Exact 848-byte (`0x350`) stack-frame decomposition of `load_session::{closure#0}`. -/
def loadPollFrameSlots (sp : BitVec 64)
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) : SepProp :=
  ((sp - 0x350#64) ↦₆₄ c_sp0) ∗
  memRegion (sp - 0x348#64) 312 ∗
  ((sp - 0x210#64) ↦₁₂₈ q140) ∗
  memRegion (sp - 0x200#64) 8 ∗
  memRegion (sp - 0x1f8#64) 24 ∗
  memRegion (sp - 0x1e0#64) 368 ∗
  memRegion (sp - 0x070#64) 16 ∗
  ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗
  ((sp - 0x50#64) ↦₆₄ c2) ∗ ((sp - 0x48#64) ↦₆₄ c3) ∗
  ((sp - 0x40#64) ↦₆₄ c4) ∗ ((sp - 0x38#64) ↦₆₄ c5) ∗
  ((sp - 0x30#64) ↦₆₄ c6) ∗ ((sp - 0x28#64) ↦₆₄ c7) ∗
  ((sp - 0x20#64) ↦₆₄ c8) ∗ ((sp - 0x18#64) ↦₆₄ c9) ∗
  ((sp - 0x10#64) ↦₆₄ c10) ∗ ((sp - 0x08#64) ↦₆₄ c11)

theorem stackAt_loadPoll_eq (sp : BitVec 64) {sub : Nat} (hsub : 0x350 + sub ≤ 2 ^ 64) :
    stackAt sp (0x350 + sub) =
      stackAt (sp - 0x350#64) sub ∗
      (∃∗ c_sp0 : BitVec 64, ∃∗ q140 : BitVec 128,
       ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        loadPollFrameSlots sp c_sp0 q140 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) := by
  have htop : stackAt sp (sub + 848) = stackAt (sp - 0x350#64) sub ∗ memRegion (sp - 0x350#64) 848 := by
    simp only [stackAt]
    have hbv : sp - BitVec.ofNat 64 (sub + 848) = sp - 0x350#64 - BitVec.ofNat 64 sub := by bv_omega
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (sub + 848))
          (n := sub) (k := 848) (b' := sp - 0x350#64)
          (by omega) (by bv_omega) (by omega), hbv]
  rw [show 0x350 + sub = sub + 848 by omega, htop,
      ProofLib.memRegion_split' (b := sp - 0x350#64) (n := 8) (k := 840)
        (b' := sp - 0x348#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x348#64) (n := 312) (k := 528)
        (b' := sp - 0x210#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x210#64) (n := 16) (k := 512)
        (b' := sp - 0x200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x200#64) (n := 8) (k := 504)
        (b' := sp - 0x1f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x1f8#64) (n := 24) (k := 480)
        (b' := sp - 0x1e0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x1e0#64) (n := 368) (k := 112)
        (b' := sp - 0x070#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x070#64) (n := 16) (k := 96)
        (b' := sp - 0x60#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 0x350#64),
      memRegion_16_q128 (sp - 0x210#64),
      show (96 : Nat) = 8 * 12 by rfl,
      ProofLib.memRegion_cells (sp - 0x60#64) 12 (by decide)]
  have hc12 : cells (sp - 0x60#64) 12 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((sp - 0x60#64) ↦₆₄ c0) ∗ ((sp - 0x58#64) ↦₆₄ c1) ∗
        ((sp - 0x50#64) ↦₆₄ c2) ∗ ((sp - 0x48#64) ↦₆₄ c3) ∗
        ((sp - 0x40#64) ↦₆₄ c4) ∗ ((sp - 0x38#64) ↦₆₄ c5) ∗
        ((sp - 0x30#64) ↦₆₄ c6) ∗ ((sp - 0x28#64) ↦₆₄ c7) ∗
        ((sp - 0x20#64) ↦₆₄ c8) ∗ ((sp - 0x18#64) ↦₆₄ c9) ∗
        ((sp - 0x10#64) ↦₆₄ c10) ∗ ((sp - 0x08#64) ↦₆₄ c11)) := by
    cells_unfold
  rw [hc12]
  simp only [loadPollFrameSlots, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
      Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
      Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
      Entails.sepExists_elim fun c6 => Entails.sepExists_elim fun c7 =>
      Entails.sepExists_elim fun c8 => Entails.sepExists_elim fun c9 =>
      Entails.sepExists_elim fun c10 => Entails.sepExists_elim fun c11 =>
      Entails.sepExists_elim fun q140 => Entails.sepExists_elim fun c_sp0 => ?_
    refine Entails.sepExists_right c_sp0 (Entails.sepExists_right q140
      (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
      (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11
        (Entails.of_eq (by ac_rfl)))))))))))))))
  · refine Entails.sepExists_elim fun c_sp0 => Entails.sepExists_elim fun q140 =>
      Entails.sepExists_elim fun c0 => Entails.sepExists_elim fun c1 =>
      Entails.sepExists_elim fun c2 => Entails.sepExists_elim fun c3 =>
      Entails.sepExists_elim fun c4 => Entails.sepExists_elim fun c5 =>
      Entails.sepExists_elim fun c6 => Entails.sepExists_elim fun c7 =>
      Entails.sepExists_elim fun c8 => Entails.sepExists_elim fun c9 =>
      Entails.sepExists_elim fun c10 => Entails.sepExists_elim fun c11 => ?_
    refine Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
      (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
      (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11
      (Entails.sepExists_right q140 (Entails.sepExists_right c_sp0
        (Entails.of_eq (by ac_rfl)))))))))))))))

theorem stackAt_loadPoll_of_parts (sp : BitVec 64) {sub : Nat} (hsub : 0x350 + sub ≤ 2 ^ 64)
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64) :
    (stackAt (sp - 0x350#64) sub ∗
      loadPollFrameSlots sp c_sp0 q140 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) ⊢
      stackAt sp (0x350 + sub) := by
  rw [stackAt_loadPoll_eq sp hsub]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right c_sp0 (Entails.sepExists_right q140
    (Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
    (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
    (Entails.sepExists_right c9 (Entails.sepExists_right c10 (Entails.sepExists_right c11
      (Entails.refl _))))))))))))))

/-- Split `memRegion out 368` into the 5 words, 1 quadword, and 312-byte tail written in the epilogue. -/
theorem sret368_epilogue_split (out : BitVec 64) :
    memRegion out 368 =
      (∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64,
       ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64, ∃∗ oq : BitVec 128,
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 0x10#64) ↦₆₄ o2) ∗
        ((out + 0x18#64) ↦₆₄ o3) ∗ ((out + 0x20#64) ↦₆₄ o4) ∗
        ((out + 0x28#64) ↦₁₂₈ oq) ∗ memRegion (out + 0x38#64) 312) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 40) (k := 328)
        (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x28#64) (n := 16) (k := 312)
        (b' := out + 0x38#64) rfl (by bv_omega) (by decide),
      show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) by rfl,
      memRegion_split out 8 (8 + (8 + (8 + 8))) (by decide),
      memRegion_split (out + 8#64) 8 (8 + (8 + 8)) (by decide),
      memRegion_split (out + 8#64 + 8#64) 8 (8 + 8) (by decide),
      memRegion_split (out + 8#64 + 8#64 + 8#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight,
      memRegion_16_q128 (out + 0x28#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun oq => Entails.sepExists_elim fun o4 =>
      Entails.sepExists_elim fun o3 => Entails.sepExists_elim fun o2 =>
      Entails.sepExists_elim fun o1 => Entails.sepExists_elim fun o0 => ?_
    refine Entails.sepExists_right o0 (Entails.sepExists_right o1
      (Entails.sepExists_right o2 (Entails.sepExists_right o3
      (Entails.sepExists_right o4 (Entails.sepExists_right oq
        (Entails.of_eq (by ac_rfl)))))))
  · refine Entails.sepExists_elim fun o0 => Entails.sepExists_elim fun o1 =>
      Entails.sepExists_elim fun o2 => Entails.sepExists_elim fun o3 =>
      Entails.sepExists_elim fun o4 => Entails.sepExists_elim fun oq => ?_
    refine Entails.sepExists_right oq (Entails.sepExists_right o4
      (Entails.sepExists_right o3 (Entails.sepExists_right o2
      (Entails.sepExists_right o1 (Entails.sepExists_right o0
        (Entails.of_eq (by ac_rfl)))))))

/-- Split the 368-byte slot `sp - 0x1e0#64` into 48 bytes for `Dir::get` and 320 spare bytes. -/
theorem slot170_split48 (sp : BitVec 64) :
    memRegion (sp - 0x1e0#64) 368 =
      memRegion (sp - 0x1e0#64) 48 ∗ memRegion (sp - 0x1b0#64) 320 :=
  ProofLib.memRegion_split' (b := sp - 0x1e0#64) (n := 48) (k := 320)
    (b' := sp - 0x1b0#64) rfl (by bv_omega) (by decide)

/-! ## `Vec<u8>` borrow-and-drop decomposition -/

/-- Remaining heap ownership of a `Vec<u8>` after borrowing `SpqrV1.ChainProofs.bytesAt false ptr bs`. -/
def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0#64 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8_eq_bytes_tail (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8))
    (v8 v16 : BitVec 64) (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    vecU8 A v bs =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs) := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader vecU8Tail SpqrV1.ChainProofs.bytesAt
  simp only [Bool.false_eq_true, ite_false]
  refine ProofLib.sepExists_congr fun cap => ProofLib.sepExists_congr fun ptr => ?_
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : cap = 0#64
  · subst hc
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
    have hcomm :
        (((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ emp) =
        (⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))) := by
      rw [sepConj_emp]
      ac_rfl
    rw [hcomm]
    apply sepProp_ext
    · apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs
      apply Entails.pure_right ⟨hlen, hlt, hptr⟩
      simp only [pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
    · apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hbs
      apply Entails.pure_right ⟨hlen, hlt, hptr⟩
      simp only [pointsToBytes_nil, sepConj_emp]
      exact Entails.refl _
  · simp only [hc, ite_false]
    ac_rfl

theorem vecU8_free_zero (A : RustAlloc) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length ≤ (0#64 : BitVec 64).toNat) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A 0#64 ptr bs) ⊢ emp := by
  have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst hbs
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, ite_false, ite_true,
    pointsToBytes_nil, emp_sepConj]
  exact Entails.refl _

theorem vecU8_free_ne (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, hc, ite_false]
  have hpull :
      ((ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
  have hmerge := (ProofLib.memRegion_split (b := ptr) bs.length (cap.toNat - bs.length) (by omega)).symm
  rw [hmerge, show bs.length + (cap.toNat - bs.length) = cap.toNat by omega]
  exact Entails.refl _

theorem header3_entails_memRegion24 (v v8 v16 w0 w1 w2 : BitVec 64)
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    ((v ↦₆₄ w0) ∗ (v8 ↦₆₄ w1) ∗ (v16 ↦₆₄ w2)) ⊢ memRegion v 24 := by
  subst hv8; subst hv16
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion v w0)
      (sepConj_mono (pointsTo64_entails_memRegion (v + 8#64) w1)
        (pointsTo64_entails_memRegion (v + 16#64) w2))) ?_
  rw [show (v + 16#64 : BitVec 64) = (v + 8#64) + 8#64 by bv_omega,
      ← ProofLib.memRegion_split (v + 8#64) 8 8 (by decide),
      ← ProofLib.memRegion_split v 8 16 (by decide)]
  exact Entails.refl _

/-! ## Discriminant & sret reassembly lemmas (`Err`, `Ok(None)`, `Ok(Some r)`) -/

theorem speWord_one_add_two_ne_zero : (speWord 1 + 2#64 == 0#64) = false := by
  decide +kernel

theorem okTagVec_add_two_eq_zero : (okTagVec + 2#64 == 0#64) = true := by
  decide +kernel

theorem speAt_read_invalidState_unpack (A : RustAlloc) (sp : BitVec 64) :
    speAt A (utf8 "read") (sp - 0x1e0#64) .invalidState =
      (∃∗ bs : List (BitVec 8), ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ fnPtr : BitVec 64,
        ((sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗ ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read")) := by
  unfold speAt vecU8 vecU8At vecHeader strRefAt
  have e1 : sp - 0x1e0#64 + asm64% spePayloadOff = sp - 0x1d8#64 := by bv_omega
  have e2 : sp - 0x1d8#64 + 8#64 = sp - 0x1d0#64 := by bv_omega
  have e3 : sp - 0x1d8#64 + 16#64 = sp - 0x1c8#64 := by bv_omega
  have e4 : sp - 0x1e0#64 + asm64% speInvalidStateFnOff = sp - 0x1c0#64 := by bv_omega
  rw [e1, e4]
  simp only [e2, e3, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_elim fun bs =>
      Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.sepExists_right bs (Entails.sepExists_right cap
      (Entails.sepExists_right ptr (Entails.sepExists_right fnPtr ?_)))
    rw [← pointsTo64_pair (sp - 0x1c0#64) fnPtr (BitVec.ofNat 64 (utf8 "read").length)]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun bs => Entails.sepExists_elim fun cap =>
      Entails.sepExists_elim fun ptr => Entails.sepExists_elim fun fnPtr => ?_
    refine Entails.sepExists_right fnPtr (Entails.sepExists_right bs
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)))
    rw [← pointsTo64_pair (sp - 0x1c0#64) fnPtr (BitVec.ofNat 64 (utf8 "read").length)]
    exact Entails.of_eq (by ac_rfl)

theorem speAt_read_invalidState_reassemble (A : RustAlloc) (sp out : BitVec 64)
    (bs : List (BitVec 8)) (cap ptr fnPtr : BitVec 64) (bs312 : List (BitVec 8))
    (hbs312 : bs312.length = 312) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₆₄ speWord 1) ∗
      ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
      ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
      ((out + 0x38#64) ↦ₛ bs312) ∗
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        if cap = 0#64 then emp
        else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
      (fnPtr ↦ᵣ utf8 "read") ∗
      ((sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
      ((sp - 0x1d8#64) ↦₆₄ cap) ∗ ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
      ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
      memRegion (sp - 0x1b0#64) 320) ⊢
      sessLoadOutAt A out (.error ()) ∗ memRegion (sp - 0x1e0#64) 368 := by
  have hout :
      ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((out + 8#64) ↦₆₄ speWord 1) ∗
        ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
        ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        ((out + 0x38#64) ↦ₛ bs312) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ⊢
      sessLoadOutAt A out (.error ()) := by
    unfold sessLoadOutAt speAt vecU8 vecU8At vecHeader strRefAt
    have o1 : out + 8#64 + asm64% spePayloadOff = out + 0x10#64 := by bv_omega
    have o2 : out + 0x10#64 + 8#64 = out + 0x18#64 := by bv_omega
    have o3 : out + 0x10#64 + 16#64 = out + 0x20#64 := by bv_omega
    have o4 : out + 8#64 + asm64% speInvalidStateFnOff = out + 0x28#64 := by bv_omega
    rw [o1, o4]
    simp only [o2, o3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right fnPtr (Entails.sepExists_right bs
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)))
    rw [← pointsTo64_pair (out + 0x28#64) fnPtr (BitVec.ofNat 64 (utf8 "read").length)]
    have htail : ((out + 0x38#64) ↦ₛ bs312) ⊢ memRegion (out + 0x38#64) 312 :=
      hbs312 ▸ pointsToBytes_entails_memRegion (out + 0x38#64) bs312
    have hpull :
        ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₆₄ speWord 1) ∗
          ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
          ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (((out + 0x28#64) ↦₆₄ fnPtr) ∗ ((out + 0x28#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length)) ∗
          ((out + 0x38#64) ↦ₛ bs312) ∗
          (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
            if cap = 0#64 then emp
            else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read")) =
        (((out + 0x38#64) ↦ₛ bs312) ∗
          ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₆₄ speWord 1) ∗
            ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
            ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
              if cap = 0#64 then emp
              else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
                memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
            ((out + 0x28#64) ↦₆₄ fnPtr) ∗
            ((out + 0x28#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (fnPtr ↦ᵣ utf8 "read"))) := by
      ac_rfl
    rw [hpull]
    refine Entails.trans (sepConj_mono_left htail) ?_
    exact Entails.of_eq (by ac_rfl)
  have hslot :
      (((sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗ ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        memRegion (sp - 0x1b0#64) 320) ⊢
      memRegion (sp - 0x1e0#64) 368 := by
    refine Entails.trans
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (q128_entails_memRegion16 _ _) (Entails.refl _)))))) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 0x1c0#64) (n := 16) (k := 320)
          (b' := sp - 0x1b0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x1c8#64) (n := 8) (k := 336)
          (b' := sp - 0x1c0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x1d0#64) (n := 8) (k := 344)
          (b' := sp - 0x1c8#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x1d8#64) (n := 8) (k := 352)
          (b' := sp - 0x1d0#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 0x1e0#64) (n := 8) (k := 360)
          (b' := sp - 0x1d8#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hgroup :
      ((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((out + 8#64) ↦₆₄ speWord 1) ∗
        ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
        ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        ((out + 0x38#64) ↦ₛ bs312) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗
        ((sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗ ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        memRegion (sp - 0x1b0#64) 320) =
      (((out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
        ((out + 8#64) ↦₆₄ speWord 1) ∗
        ((out + 0x10#64) ↦₆₄ cap) ∗ ((out + 0x18#64) ↦₆₄ ptr) ∗
        ((out + 0x20#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        ((out + 0x38#64) ↦ₛ bs312) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read")) ∗
      (((sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗ ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        memRegion (sp - 0x1b0#64) 320)) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono hout hslot

theorem sessLoadOutAt_none_reassemble (A : RustAlloc) (out : BitVec 64)
    (w1 w2 w3 w4 : BitVec 64) (q0 : BitVec 128) (bs312 : List (BitVec 8))
    (hbs312 : bs312.length = 312) :
    ((out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((out + 8#64) ↦₆₄ w1) ∗ ((out + 0x10#64) ↦₆₄ w2) ∗
      ((out + 0x18#64) ↦₆₄ w3) ∗ ((out + 0x20#64) ↦₆₄ w4) ∗
      ((out + 0x28#64) ↦₁₂₈ q0) ∗ ((out + 0x38#64) ↦ₛ bs312)) ⊢
      sessLoadOutAt A out (.ok none) := by
  unfold sessLoadOutAt
  refine sepConj_mono_right ?_
  have htail : ((out + 0x38#64) ↦ₛ bs312) ⊢ memRegion (out + 0x38#64) 312 :=
    hbs312 ▸ pointsToBytes_entails_memRegion (out + 0x38#64) bs312
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (q128_entails_memRegion16 _ _) htail))))) ?_
  rw [← ProofLib.memRegion_split' (b := out + 0x28#64) (n := 16) (k := 312)
        (b' := out + 0x38#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 328)
        (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 336)
        (b' := out + 0x20#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 344)
        (b' := out + 0x18#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 352)
        (b' := out + 0x10#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot170_ok_collapse (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 0x1e0#64) ↦₆₄ w0) ∗ ((sp - 0x1d8#64) ↦₆₄ w1) ∗
      ((sp - 0x1d0#64) ↦₆₄ w2) ∗ ((sp - 0x1c8#64) ↦₆₄ w3) ∗
      memRegion (sp - 0x1c0#64) 16 ∗ memRegion (sp - 0x1b0#64) 320) ⊢
      memRegion (sp - 0x1e0#64) 368 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x1c0#64) (n := 16) (k := 320)
        (b' := sp - 0x1b0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x1c8#64) (n := 8) (k := 336)
        (b' := sp - 0x1c0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x1d0#64) (n := 8) (k := 344)
        (b' := sp - 0x1c8#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x1d8#64) (n := 8) (k := 352)
        (b' := sp - 0x1d0#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x1e0#64) (n := 8) (k := 360)
        (b' := sp - 0x1d8#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem recordDeserialize_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr sessLoadPollName -
      bv% (ls_rel% "<libsignal_protocol::state::session::SessionRecord>::deserialize"
        "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr recordDeserializeName := by
  have h1 := sessLoadPoll_fnOff
  have h2 := recordDeserialize_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadPollName, recordDeserializeName, h1, h2]
  bv_omega

theorem addressText_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr sessLoadPollName +
      bv% (ls_rel% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
        "libsignal_cli::stores::address_text") =
      (tripleRatchetProgAtExt b ext).fnAddr addressTextName := by
  have h1 := sessLoadPoll_fnOff
  have h2 := addressText_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadPollName, addressTextName, h1, h2]
  bv_omega

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr sessLoadPollName +
      bv% (ls_rel% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
        "<libsignal_cli::stores::Dir>::get") =
      (tripleRatchetProgAtExt b ext).fnAddr dirGetName := by
  have h1 := sessLoadPoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, sessLoadPollName, dirGetName, h1, h2]
  bv_omega

theorem files_eq_of_fsInv_trace_eq {F0 : FsFiles} {T0 : List TraceEvent} {s : State}
    (hinv : FsInv F0 T0 s) (ht : s.trace = T0) : s.fs.files = F0 :=
  files_eq_at_callback hinv (ht.trans (List.append_nil T0).symm) .nil

theorem record_unpack_for_poll (A : RustAlloc) (sp : BitVec 64)
    (gE2E : E2E.Record.RecordGhost) (r : SessionRecord (List (BitVec 8))) :
    let g := E2E.InMem.SessionStoreImpl.ofRecordGhost gE2E
    E2E.Record.sessionRecordAt A (sp - 0x1e0#64) gE2E r ⊢
      (∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜g.prevCap.toNat < 2 ^ 63 ∧ Pf.RecordMove.RecordTailInline g r w4 w5 w6 tail⌝ ∗
        ((sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((sp - 0x1a8#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordHeap A g r) := by
  intro g
  have hconv : E2E.Record.sessionRecordAt A (sp - 0x1e0#64) gE2E r =
      sessionRecordAt A (sp - 0x1e0#64) g r := by
    have h1 := E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq A (sp - 0x1e0#64) g r
    simpa [g] using h1
  rw [hconv, Pf.RecordMove.sessionRecordAt_eq_words56_sep_tail A (sp - 0x1e0#64) g r]
  refine Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
    Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun tail => ?_
  refine Entails.sepExists_right w4 (Entails.sepExists_right w5
    (Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)))
  apply Entails.pure_left; intro hinl
  have hpull1 :
      (Pf.RecordMove.recordWords56At (sp - 0x1e0#64) g.prevCap g.prevPtr 0#64
          (Pf.RecordMove.recordCurCap g) w4 w5 w6 ∗
        ((sp - 0x1e0#64 + 0x38#64) ↦ₛ tail) ∗ Pf.RecordMove.recordHeap A g r) =
      (Pf.RecordMove.recordHeap A g r ∗
        (Pf.RecordMove.recordWords56At (sp - 0x1e0#64) g.prevCap g.prevPtr 0#64
          (Pf.RecordMove.recordCurCap g) w4 w5 w6 ∗
          ((sp - 0x1e0#64 + 0x38#64) ↦ₛ tail))) := by
    ac_rfl
  rw [hpull1]
  refine Entails.trans (sepConj_mono_left (Pf.RecordMove.recordHeap_prevCap_lt_two_pow_63 A g r)) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hcap
  apply Entails.pure_right ⟨hcap, hinl⟩
  unfold Pf.RecordMove.recordWords56At
  have e1 : sp - 0x1e0#64 + 8#64 = sp - 0x1d8#64 := by bv_omega
  have e2 : sp - 0x1e0#64 + 0x10#64 = sp - 0x1d0#64 := by bv_omega
  have e3 : sp - 0x1e0#64 + 0x18#64 = sp - 0x1c8#64 := by bv_omega
  have e4 : sp - 0x1e0#64 + 0x20#64 = sp - 0x1c0#64 := by bv_omega
  have e5 : sp - 0x1e0#64 + 0x28#64 = sp - 0x1b8#64 := by bv_omega
  have e6 : sp - 0x1e0#64 + 0x30#64 = sp - 0x1b8#64 + 8#64 := by bv_omega
  have e7 : sp - 0x1e0#64 + 0x38#64 = sp - 0x1a8#64 := by bv_omega
  rw [e1, e2, e3, e4, e5, e6, e7, ← pointsTo64_pair (sp - 0x1b8#64) w5 w6]
  exact Entails.of_eq (by ac_rfl)

theorem record_reassemble_for_poll (A : RustAlloc) (sp out : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8)))
    {w4 w5 w6 : BitVec 64} {tail : List (BitVec 8)}
    (hinl : Pf.RecordMove.RecordTailInline g r w4 w5 w6 tail) :
    ((out ↦₆₄ g.prevCap) ∗ ((out + 8#64) ↦₆₄ g.prevPtr) ∗
      ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
      ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₁₂₈ (w6 ++ w5)) ∗
      ((out + 0x38#64) ↦ₛ tail) ∗
      ((sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗ ((sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
      ((sp - 0x1d0#64) ↦₆₄ 0#64) ∗ ((sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
      ((sp - 0x1c0#64) ↦₆₄ w4) ∗ ((sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
      ((sp - 0x1a8#64) ↦ₛ tail) ∗
      ((sp - 0x348#64) ↦ₛ tail) ∗
      Pf.RecordMove.recordHeap A g r) ⊢
      sessLoadOutAt A out (.ok (some r)) ∗
      memRegion (sp - 0x1e0#64) 368 ∗
      memRegion (sp - 0x348#64) 312 := by
  have o30 : out + 0x28#64 + 8#64 = out + 0x30#64 := by bv_omega
  have e1 : sp - 0x1e0#64 + 8#64 = sp - 0x1d8#64 := by bv_omega
  have e2 : sp - 0x1e0#64 + 0x10#64 = sp - 0x1d0#64 := by bv_omega
  have e3 : sp - 0x1e0#64 + 0x18#64 = sp - 0x1c8#64 := by bv_omega
  have e4 : sp - 0x1e0#64 + 0x20#64 = sp - 0x1c0#64 := by bv_omega
  have e5 : sp - 0x1e0#64 + 0x28#64 = sp - 0x1b8#64 := by bv_omega
  have e6 : sp - 0x1e0#64 + 0x28#64 + 8#64 = sp - 0x1e0#64 + 0x30#64 := by bv_omega
  have e7 : sp - 0x1e0#64 + 0x38#64 = sp - 0x1a8#64 := by bv_omega
  rw [← pointsTo64_pair (out + 0x28#64) w5 w6, o30,
      ← pointsTo64_pair (sp - 0x1b8#64) w5 w6,
      ← e1, ← e2, ← e3, ← e4, ← e5, e6, ← e7]
  have hfold :
      ((out ↦₆₄ g.prevCap) ∗ ((out + 8#64) ↦₆₄ g.prevPtr) ∗
        ((out + 0x10#64) ↦₆₄ 0#64) ∗ ((out + 0x18#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗
        (((out + 0x28#64) ↦₆₄ w5) ∗ ((out + 0x30#64) ↦₆₄ w6)) ∗
        ((out + 0x38#64) ↦ₛ tail) ∗
        ((sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗ ((sp - 0x1e0#64 + 8#64) ↦₆₄ g.prevPtr) ∗
        ((sp - 0x1e0#64 + 0x10#64) ↦₆₄ 0#64) ∗ ((sp - 0x1e0#64 + 0x18#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((sp - 0x1e0#64 + 0x20#64) ↦₆₄ w4) ∗
        (((sp - 0x1e0#64 + 0x28#64) ↦₆₄ w5) ∗ ((sp - 0x1e0#64 + 0x30#64) ↦₆₄ w6)) ∗
        ((sp - 0x1e0#64 + 0x38#64) ↦ₛ tail) ∗
        ((sp - 0x348#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordHeap A g r) =
      (Pf.RecordMove.recordWords56At out g.prevCap g.prevPtr 0#64 (Pf.RecordMove.recordCurCap g) w4 w5 w6 ∗
        ((out + 0x38#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordWords56At (sp - 0x1e0#64) g.prevCap g.prevPtr 0#64
          (Pf.RecordMove.recordCurCap g) w4 w5 w6 ∗
        ((sp - 0x1e0#64 + 0x38#64) ↦ₛ tail) ∗
        ((sp - 0x348#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordHeap A g r) := by
    unfold Pf.RecordMove.recordWords56At
    ac_rfl
  rw [hfold]
  refine Entails.trans
    (Pf.RecordMove.sessionRecordAt_move_words56_twice A (sp - 0x1e0#64) (sp - 0x348#64) out g r hinl) ?_
  unfold sessLoadOutAt
  exact sepConj_mono_left (Entails.sepExists_right g (Entails.refl _))

/-! ## Shared state, stack, and call combinators for `Epilogue` and `Sym` -/

theorem calleeSavedVRegs_writeVReg128_0 (s : State) (val : BitVec 128) :
    calleeSavedVRegs (s.writeVReg128 0#5 val) = calleeSavedVRegs s :=
  calleeSavedVRegs_writeVReg128 s 0#5 val (by decide)

theorem fs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := by cases s; rfl
theorem fs_advancePC (s : State) : s.advancePC.fs = s.fs := by cases s; rfl
theorem fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
theorem fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fs = s.fs := by
  cases s; rfl
theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases w <;> cases s <;> rfl
theorem fs_writeVReg128 (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).fs = s.fs := by cases s; rfl
theorem fs_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by cases wb <;> cases s <;> rfl

theorem spAligned_sub_350 {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 0x350#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem subStack_split (sp : BitVec 64) {addrStk getStk K : Nat}
    (hK : K ≤ subMax addrStk getStk)
    (hhi : pollMinStk addrStk getStk ≤ 2 ^ 64) :
    stackAt (sp - 0x350#64) (subMax addrStk getStk) =
      memRegion (sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - K) ∗
      stackAt (sp - 0x350#64) K :=
  stackAt_sub_split (sp - 0x350#64) hK (by unfold pollMinStk at hhi; omega)

def savedCalleeSlots (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

def epiloguePre (s0 : State) (x : SessLoadPollGhost)
    (q140 : BitVec 128) (bs312 : List (BitVec 8)) : SepProp :=
  ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
  ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
  memRegion x.call.out 368 ∗
  sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
  stackAt (s0.sp - 0x350#64) extHookStack ∗
  savedCalleeSlots s0

def epilogueOut (s0 : State) (x : SessLoadPollGhost)
    (w0 w1 w2 w3 w4 : BitVec 64) (q140 : BitVec 128) (bs312 : List (BitVec 8)) : SepProp :=
  (x.call.out ↦₆₄ w0) ∗ ((x.call.out + 8#64) ↦₆₄ w1) ∗
  ((x.call.out + 0x10#64) ↦₆₄ w2) ∗ ((x.call.out + 0x18#64) ↦₆₄ w3) ∗
  ((x.call.out + 0x20#64) ↦₆₄ w4) ∗ ((x.call.out + 0x28#64) ↦₁₂₈ q140) ∗
  ((x.call.out + 0x38#64) ↦ₛ bs312) ∗
  ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
  ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
  sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
  stackAt (s0.sp - 0x350#64) extHookStack ∗
  savedCalleeSlots s0

theorem restore_pollStack (s0 : State) {addrStk getStk stk : Nat}
    (hstk : pollMinStk addrStk getStk ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (c_sp0 : BitVec 64) (q140 : BitVec 128) :
    (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - extHookStack) ∗
      stackAt (s0.sp - 0x350#64) extHookStack ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      memRegion (s0.sp - 0x200#64) 8 ∗
      memRegion (s0.sp - 0x1f8#64) 24 ∗
      memRegion (s0.sp - 0x1e0#64) 368 ∗
      memRegion (s0.sp - 0x070#64) 16 ∗
      savedCalleeSlots s0) ⊢
      stackAt s0.sp stk := by
  have hmin : pollMinStk addrStk getStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  rw [stackAt_sub_split s0.sp hstk hhi]
  refine sepConj_mono_right ?_
  refine Entails.trans ?_
    (stackAt_loadPoll_of_parts s0.sp hmin c_sp0 q140
      (s0.readReg64 .x29) (s0.readReg64 .lr) (s0.readReg64 .x28) (s0.readReg64 .x27)
      (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
  rw [subStack_split s0.sp hext hmin]
  unfold loadPollFrameSlots savedCalleeSlots
  exact Entails.of_eq (by ac_rfl)

theorem layoutOk_u8_of_ne_zero {cap : BitVec 64} (hc : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem lpoll_dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := sessLoadPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "__rustc::__rust_dealloc"))
    (by rw [sessLoadPoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem lpoll_memcpy_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
          "memcpy"))
      (session2MemcpySpecX.inImage img) :=
  memcpy_ok_at2_ext_x hC (name := sessLoadPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "memcpy"))
    (by rw [sessLoadPoll_fnOff, (ls_stub% "memcpy")])

theorem sepWPp_conseq {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : P ⊢ P')
    (hw : SepWPp prog ret s P' Q Qp) : SepWPp prog ret s P Q Qp :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_with_stk_bound {prog : Program} {ret : BitVec 64} {s : State}
    {stk : Nat} {a v : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P ⊢ stackAt s.sp stk ∗ (a ↦₆₄ v) ∗ Rest)
    (hw : stk ≤ 2 ^ 64 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  have hm' : s.mem ⊨ memRegion (s.sp - BitVec.ofNat 64 stk) stk ∗ ((a ↦₆₄ v) ∗ (Rest ∗ R)) := by
    have h1 := Satisfies.mono (sepConj_mono_left hfoc) hm
    simpa only [stackAt, sepConj_assoc] using h1
  exact hw (memRegion_bound_of_pointsTo64 hm') R hm hL

/-- Call any `Spec` whose panic implies `allocFailedIn` and whose exit/OOM are `False`, preserving `ImgCallInv img`. -/
theorem lpoll_call_panicking_raw {α : Type} {prog : Program} {img : Obj.Image}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine ProofLib.SepWPp.call_wpp_frozen hcall (x := x) (F := F) hinv.1 hinv.2
    hpc hrun hsp_align hlr
    (fun R' hm => by
      have hm' := Satisfies.mono (sepConj_mono_left hpre) hm
      rwa [sepConj_assoc] at hm')
    (fun sm code _ _ hex => hexit_imp code sm _ hex)
    (fun sm _ ⟨R', hpost⟩ =>
      hpan sm _ (by simpa [allocFailedIn, htr] using hpan_imp sm R' hpost))
    (fun sm hpcm hrunm hspm hcsm hfz hsym =>
      hnext sm hpcm hrunm hspm hcsm ⟨hfz, hsym⟩)
    (fun sm _ _ hpost => (hoom_imp sm _ hpost).elim)

theorem lpoll_call_addrText {prog : Program} {img : Obj.Image} {A : RustAlloc} {addrStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (addrTextSpec A img addrStk) s0_files s0_trace))
    (xg : AddrTextGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.addr)
    (hlen : xg.g.name.bytes.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (protocolAddressAt A xg.g xg.addr ∗ memRegion xg.ret 24 ∗
      stackAt s.sp addrStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      FsInv s0_files s0_trace sm → sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (addressText xg.g.val) ∗ protocolAddressAt A xg.g xg.addr ∗
          stackAt s.sp addrStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [withFsInv, addrTextSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hfs
      (Entails.pure_right hinv (Entails.pure_right ⟨hx0, hx1, hlen⟩ (Entails.refl _)))
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, addrTextSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, addrTextSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [withFsInv, addrTextSpec, Spec.inImage, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hinvm hfsm htrm)

theorem lpoll_call_dirGet {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpec rd pathOk A img getStk))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc]
    exact Entails.pure_right hinv
      (Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _))
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpec, Spec.inImage] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [dirGetSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hinvm hgr)

theorem lpoll_call_deser {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (sessDeserializeSpec Scope A img))
    (xg : E2E.Record.DeserializeGeneral.DeserializeGenGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord xg.r).length)
    (hx8 : s.readReg64 .x8 = xg.out)
    (hsc : Scope xg.r)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗ memRegion xg.out 368 ∗
      stackAt s.sp E2E.Record.recDeserializeStack) ∗ F)
    (hnext : ∀ (sm : State) (gE2E : E2E.Record.RecordGhost),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace → E2E.Record.Serialization.CanonRecord gE2E xg.r →
      SepWPp prog ret sm
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessDeserializeSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx8, hsc, hinv.1, hinv.2⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sessDeserializeSpec, E2E.Record.Serialization.allocPanic, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [sessDeserializeSpec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun gE2E => SepWPp.pure_elim fun htrm => ?_
    refine sepWPp_conseq
      (P' := ⌜E2E.Record.Serialization.CanonRecord gE2E xg.r⌝ ∗
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    exact SepWPp.pure_elim fun hcan =>
      hnext sm gE2E hpcm hrunm hspm hcsm hinvm htrm hcan

theorem subroutine_ok_sessDeserializeExtSpec_of_spec {prog : Program} {entry : BitVec 64}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {A : RustAlloc} {img : Obj.Image}
    (h : subroutine_ok prog entry (sessDeserializeSpec Scope A img)) :
    subroutine_ok prog entry (sessDeserializeExtSpec Scope A img) := by
  refine subroutine_ok_map_panic h fun x R s0 hpre => ?_
  refine ⟨x, A.pool ∗ R, ?_, ?_, ?_⟩
  · dsimp only [sessDeserializeExtSpec, sessDeserializeSpec] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  · intro sf hpost
    dsimp only [sessDeserializeExtSpec, sessDeserializeSpec] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · intro sf hpan
    dsimp only [sessDeserializeExtSpec, sessDeserializeSpec,
      E2E.Record.Serialization.allocPanic] at hpan ⊢
    have habsorb : anyHeap ∗ A.pool ⊢ anyHeap := entails_anyHeap (anyHeap ∗ A.pool)
    have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (A.pool ∗ R) =
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ A.pool) ∗ R := by ac_rfl
    have h2 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R =
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R := by ac_rfl
    rw [h1] at hpan
    rw [h2]
    exact Satisfies.mono (sepConj_mono_right (sepConj_mono_left habsorb)) hpan

theorem lpoll_call_deser_ext {prog : Program} {img : Obj.Image} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (sessDeserializeExtSpec Scope A img))
    (xg : E2E.Record.DeserializeGeneral.DeserializeGenGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx0 : s.readReg64 .x0 = xg.p)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord xg.r).length)
    (hx8 : s.readReg64 .x8 = xg.out)
    (hsc : Scope xg.r)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗ memRegion xg.out 368 ∗ A.pool ∗
      stackAt s.sp E2E.Record.recDeserializeStack) ∗ F)
    (hnext : ∀ (sm : State) (gE2E : E2E.Record.RecordGhost),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → ImgCallInv img sm →
      sm.trace = s.trace → E2E.Record.Serialization.CanonRecord gE2E xg.r →
      SepWPp prog ret sm
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine lpoll_call_panicking_raw hcall xg F hpc hrun hsp_align hlr htr hinv hpan ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [sessDeserializeExtSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx8, hsc, hinv.1, hinv.2⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [sessDeserializeExtSpec, E2E.Record.Serialization.allocPanic, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hinvm
    simp only [sessDeserializeExtSpec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun gE2E => SepWPp.pure_elim fun htrm => ?_
    refine sepWPp_conseq
      (P' := ⌜E2E.Record.Serialization.CanonRecord gE2E xg.r⌝ ∗
        (((xg.p ↦ₛ E2E.Record.encodeRecord xg.r) ∗
          E2E.Record.sessionRecordAt A xg.out gE2E xg.r ∗
          stackAt s.sp E2E.Record.recDeserializeStack ∗ A.pool) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    exact SepWPp.pure_elim fun hcan =>
      hnext sm gE2E hpcm hrunm hspm hcsm hinvm htrm hcan

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
