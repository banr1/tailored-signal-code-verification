/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.ChainKeyCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.ConsumeCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The base session program, rebased at `b`. -/
noncomputable abbrev SP (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

/-- Close a `CalleeSavedPreserved s0 sf` goal after straight-line execution. -/
macro "ck_cc_close" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, applyWriteback,
    State.advancePC_eq_setPC, State.setPC_setPC, State.writeReg64_setPC, State.setPState_setPC,
    State.setPState_setPState, State.writeReg64_setPState, State.setMem_setPC, State.setMem_setMem,
    State.writeReg64_setMem, State.setPState_setMem, State.writeReg64_writeReg64_same,
    State.writeVReg128_setPC, State.writeVReg128_setPState, State.writeVReg128_setMem,
    arm64_norm, *]
  done))

/-! ## Pure and separation-logic helpers -/

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  simp only [leBytes, unpack32, List.range, List.range.loop, List.map]
  have h0 : BitVec.ofNat 8 (w.toNat / 256 ^ 0) = w.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  have h1 : BitVec.ofNat 8 (w.toNat / 256 ^ 1) = (w >>> 8).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : BitVec.ofNat 8 (w.toNat / 256 ^ 2) = (w >>> 16).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : BitVec.ofNat 8 (w.toNat / 256 ^ 3) = (w >>> 24).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h0, h1, h2, h3]
  unfold BitVec.extractLsb'
  rfl

theorem pointsToBytes_chainKeyBytes_eq (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) = (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

theorem hmacWith_two_eq_chainStep (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) :
    hmacWith F (keyToBytes32 k) [0x02#8] = Ratchet.chainHmac F k Ratchet.chainKeySeed := rfl

@[local simp] private theorem toBEBytes_length (n : ℕ) (w : BitVec (8 * n)) :
    (toBEBytes n w).length = n := by
  simp [toBEBytes]

@[local simp] private theorem shaState_flatMap_length (h : ShaState) :
    (h.toList.flatMap (toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  simp [List.length_flatMap, hl]

@[local simp]
theorem nck_length_hmacWith (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) : (hmacWith F key msg).length = 32 := by
  unfold hmacWith sha256With
  exact shaState_flatMap_length _

private theorem extractLsb'_zero_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons (b : BitVec 8) (acc : BitVec 256) (j : ℕ)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32 (bs : List (BitVec 8)) (j : ℕ)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero =>
      simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons b (bytesToKey32 rest) j h32,
        List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [keyToBytes32, h]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32 bs j h2 (by omega)

theorem nextChainKey_ok_of_ne (F : ShaCompress) (ck : ChainKey) (hne : ck.index ≠ BitVec.allOnes 32) :
    ck.nextChainKey F = .ok ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩ := by
  simp only [ChainKey.nextChainKey, hne, ↓reduceIte]

theorem nextChainKey_panic_of_eq (F : ShaCompress) (ck : ChainKey) (heq : ck.index = BitVec.allOnes 32) :
    ck.nextChainKey F = .error .panic := by
  simp only [ChainKey.nextChainKey, heq, ↓reduceIte]

/-- Split `memRegion (sp - c) N` at `n` (`N = n + k`, `c' = c - n`). -/
theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

theorem pointsTo8_eq_pointsToBytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

/-- Stack layout for `next_chain_key` (`nextChainKeyStack = 4096`, frame `0x50 = 80`). -/
theorem stackAt_nextChainKey (sp : BitVec 64) :
    stackAt sp nextChainKeyStack =
      memRegion (sp - 4096#64) 1968 ∗
      stackAt (sp - 80#64) 2048 ∗
      memRegion (sp - 80#64) 12 ∗
      memRegion (sp - 68#64) 32 ∗
      (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
      memRegion (sp - 35#64) 3 ∗
      (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
      (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
      (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
      (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19) := by
  show memRegion (sp - BitVec.ofNat 64 4096) 4096 = _
  rw [mr_cut' sp 4096 2128 1968 2128 4096 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 2128 80 2048 80 2128 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 68 12 68 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 68 36 32 36 68 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 36 35 1 35 36 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 35 32 3 32 35 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  rw [memRegion_one (sp - 36#64), memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  have h2128 : sp - 80#64 - 2048#64 = sp - 2128#64 := by bv_arith
  unfold stackAt
  change _ =
    memRegion (sp - 4096#64) 1968 ∗
    memRegion (sp - 80#64 - 2048#64) 2048 ∗
    memRegion (sp - 80#64) 12 ∗
    memRegion (sp - 68#64) 32 ∗
    (∃∗ b0 : BitVec 8, (sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    (∃∗ v29 : BitVec 64, (sp - 32#64) ↦₆₄ v29) ∗
    (∃∗ v30 : BitVec 64, (sp - 24#64) ↦₆₄ v30) ∗
    (∃∗ v20 : BitVec 64, (sp - 16#64) ↦₆₄ v20) ∗
    (∃∗ v19 : BitVec 64, (sp - 8#64) ↦₆₄ v19)
  rw [h2128]

theorem stackAt_nextChainKey_repack (sp : BitVec 64) (w0 w1 w2 w3 v29 v30 v20 v19 : BitVec 64)
    (b0 : BitVec 8) :
    memRegion (sp - 4096#64) 1968 ∗
    stackAt (sp - 80#64) 2048 ∗
    memRegion (sp - 80#64) 12 ∗
    ((sp - 68#64) ↦₆₄ w0) ∗
    ((sp - 60#64) ↦₆₄ w1) ∗
    ((sp - 52#64) ↦₆₄ w2) ∗
    ((sp - 44#64) ↦₆₄ w3) ∗
    ((sp - 36#64) ↦₈ b0) ∗
    memRegion (sp - 35#64) 3 ∗
    ((sp - 32#64) ↦₆₄ v29) ∗
    ((sp - 24#64) ↦₆₄ v30) ∗
    ((sp - 16#64) ↦₆₄ v20) ∗
    ((sp - 8#64) ↦₆₄ v19) ⊢
      stackAt sp nextChainKeyStack := by
  rw [stackAt_nextChainKey sp]
  have hw0 := pointsTo64_entails_memRegion (sp - 68#64) w0
  have hw1 := pointsTo64_entails_memRegion (sp - 60#64) w1
  have hw2 := pointsTo64_entails_memRegion (sp - 52#64) w2
  have hw3 := pointsTo64_entails_memRegion (sp - 44#64) w3
  have h60 : sp - 68#64 + 8#64 = sp - 60#64 := by bv_arith
  have h52 : sp - 60#64 + 8#64 = sp - 52#64 := by bv_arith
  have h44 : sp - 52#64 + 8#64 = sp - 44#64 := by bv_arith
  have h32 :
      ((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗ ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3) ⊢
        memRegion (sp - 68#64) 32 := by
    refine Entails.trans (sepConj_mono hw0 (sepConj_mono hw1 (sepConj_mono hw2 hw3))) ?_
    rw [← h44, ← memRegion_split (sp - 52#64) 8 8 (by decide),
        ← h52, ← memRegion_split (sp - 60#64) 8 16 (by decide),
        ← h60, ← memRegion_split (sp - 68#64) 8 24 (by decide)]
    exact Entails.refl _
  have hb0 : ((sp - 36#64) ↦₈ b0) ⊢ ∃∗ b : BitVec 8, (sp - 36#64) ↦₈ b :=
    Entails.sepExists_right b0 (Entails.refl _)
  have hv29 : ((sp - 32#64) ↦₆₄ v29) ⊢ ∃∗ v : BitVec 64, (sp - 32#64) ↦₆₄ v :=
    Entails.sepExists_right v29 (Entails.refl _)
  have hv30 : ((sp - 24#64) ↦₆₄ v30) ⊢ ∃∗ v : BitVec 64, (sp - 24#64) ↦₆₄ v :=
    Entails.sepExists_right v30 (Entails.refl _)
  have hv20 : ((sp - 16#64) ↦₆₄ v20) ⊢ ∃∗ v : BitVec 64, (sp - 16#64) ↦₆₄ v :=
    Entails.sepExists_right v20 (Entails.refl _)
  have hv19 : ((sp - 8#64) ↦₆₄ v19) ⊢ ∃∗ v : BitVec 64, (sp - 8#64) ↦₆₄ v :=
    Entails.sepExists_right v19 (Entails.refl _)
  have hpull :
      (memRegion (sp - 4096#64) 1968 ∗
        stackAt (sp - 80#64) 2048 ∗
        memRegion (sp - 80#64) 12 ∗
        ((sp - 68#64) ↦₆₄ w0) ∗
        ((sp - 60#64) ↦₆₄ w1) ∗
        ((sp - 52#64) ↦₆₄ w2) ∗
        ((sp - 44#64) ↦₆₄ w3) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) =
      (memRegion (sp - 4096#64) 1968 ∗
        stackAt (sp - 80#64) 2048 ∗
        memRegion (sp - 80#64) 12 ∗
        (((sp - 68#64) ↦₆₄ w0) ∗ ((sp - 60#64) ↦₆₄ w1) ∗
         ((sp - 52#64) ↦₆₄ w2) ∗ ((sp - 44#64) ↦₆₄ w3)) ∗
        ((sp - 36#64) ↦₈ b0) ∗
        memRegion (sp - 35#64) 3 ∗
        ((sp - 32#64) ↦₆₄ v29) ∗
        ((sp - 24#64) ↦₆₄ v30) ∗
        ((sp - 16#64) ↦₆₄ v20) ∗
        ((sp - 8#64) ↦₆₄ v19)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono h32 (sepConj_mono hb0 (sepConj_mono_right
      (sepConj_mono hv29 (sepConj_mono hv30 (sepConj_mono hv20 hv19))))))))

theorem memRegion36_unpack (r : BitVec 64) :
    memRegion r 36 =
      (∃∗ d0 : BitVec 64, r ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (r + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (r + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (r + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 32, (r + 32#64) ↦₃₂ d4) := by
  rw [show (36 : Nat) = 8 + 28 from rfl, memRegion_split r 8 28 (by decide),
      show (28 : Nat) = 8 + 20 from rfl, memRegion_split (r + 8#64) 8 20 (by decide)]
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by bv_arith
  rw [h16, show (20 : Nat) = 8 + 12 from rfl, memRegion_split (r + 16#64) 8 12 (by decide)]
  have h24 : r + 16#64 + 8#64 = r + 16#64 + 8#64 := rfl
  have h24' : r + 16#64 + 8#64 = r + 24#64 := by bv_arith
  rw [h24', show (12 : Nat) = 8 + 4 from rfl, memRegion_split (r + 24#64) 8 4 (by decide)]
  have h32 : r + 24#64 + 8#64 = r + 32#64 := by bv_arith
  rw [h32, memRegion_eight r, memRegion_eight (r + 8#64), memRegion_eight (r + 16#64),
      memRegion_eight (r + 24#64), memRegion_four (r + 32#64)]

/-- The `core::panicking::panic_const::panic_const_add_overflow` stub (offset 294716 / `0x47f3c`) panics. -/
theorem panic_at_add_overflow {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow")) :
    (SP b F alloc).externAt? ((SP b F alloc).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol hfn hk (by decide) (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
    (by simp [Rust.isPanicSymbol])

theorem hmac_ok_at_nextChainKey {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhmac : HmacOk img F alloc) :
    subroutine_ok (SP img.base F alloc)
      ((SP img.base F alloc).fnAddr nextChainKeyName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"))
      ((hmacSpec F).inImage img) := by
  unfold HmacOk at hhmac
  rw [show sessionProg img F alloc = SP img.base F alloc from libsignalSessionCode_ofImage himg] at hhmac
  have haddr : (SP img.base F alloc).fnAddr nextChainKeyName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key") = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key"), BitVec.add_assoc]
    rfl
  rwa [haddr]

private theorem pure_and_entails_pure_sep_of {P P' Q : Prop} {R : SepProp}
    (h : P → P' ∧ Q) :
    ⌜P⌝ ∗ R ⊢ ⌜P'⌝ ∗ (⌜Q⌝ ∗ R) := by
  apply Entails.pure_left
  intro hp
  rcases h hp with ⟨hp', hq⟩
  exact Entails.pure_right hp' (Entails.pure_right hq (Entails.refl R))

theorem hmac_ok_at_state {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {img : Obj.Image} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok (SP b F alloc) addr ((hmacSpec F).inImage img))
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    subroutine_ok (SP b F alloc) addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧ s'.symtab = s.symtab ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
        post := (hmacSpec F).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine hhmac.mono_outcome (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  dsimp only [Spec.inImage, hmacSpec]
  exact pure_and_entails_pure_sep_of fun ⟨hmem, hsym', hrest⟩ =>
    ⟨⟨frozenLoaded_of_mem_eq hmem hfrozen, hsym'.trans hsym⟩, hrest⟩

theorem SepWPp.conseq_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem nextChainKey_ok_sessionProg {img : Obj.Image} {F : ShaCompress}
    {abs : String → Option (State → State)} (himg : Obj.Loads libsignalSessionImage img)
    (hhmac : HmacOk img F abs) :
    subroutine_ok (sessionProg img F abs)
      ((SP img.base F abs).fnAddr nextChainKeyName) (nextChainKeySpec F img) := by
  rw [show sessionProg img F abs = SP img.base F abs from libsignalSessionCode_ofImage himg]
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")
  have hhmac_at := hmac_ok_at_nextChainKey himg hhmac
  have hpan_ovf := panic_at_add_overflow (b := img.base) (F := F) (alloc := abs) hfn (k := num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) (by decide)
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  simp only [nextChainKeySpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrozen, hsym⟩, ⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s0.sp nextChainKeyStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck, memRegion36_unpack ret, stackAt_nextChainKey s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun b0 =>
    SepWPp.exists_elim fun v29 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v19 => ?_
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
    img.base (Rust.withPanics (sessionExterns F abs)) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
  generalize_entry hentry : (SP img.base F abs).fnAddr nextChainKeyName = entry
  apply SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) hfrozen hsym
  wp_steps
  examples_hide_fetches
  apply SepWP.done (by simp_all) (by simp_all)
  intro hfrozen1 hsym1
  have hhmac1 := hmac_ok_at_state hhmac_at hfrozen1 hsym1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 36#64) 2#8]
  apply SepWPp.of_sepWP_frozen (mid := entry + bv% (56)) hfrozen1 hsym1
  wp_call hhmac1 (s0.sp - 68#64, self, keyToBytes32 ck.key, s0.sp - 36#64, [2#8])
  examples_hide_fetches
  apply SepWP.done (by simp_all) (by simp_all)
  intro hfrozen2 hsym2
  by_cases hidx : ck.index = BitVec.allOnes 32
  · have hidx_max : ck.index = 0xffffffff#32 := hidx
    rw [hidx_max]
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
      img.base (Rust.withPanics (sessionExterns F abs)) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
    subst hentry
    generalize_entry hentry : (SP img.base F abs).fnAddr nextChainKeyName = entry
    apply SepWPp.of_sepWP_frozen (mid := entry + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) hfrozen2 hsym2
    wp_steps
    examples_hide_fetches
    apply SepWP.done (by simp_all) (by simp_all)
    intro _ _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_ovf) fun hm' => ?_
    simpa only [nextChainKeySpec, Spec.inImage, sepConj_assoc] using
      allowPanic_panicked ⟨nextChainKey_panic_of_eq F ck hidx,
        by simp_all [Rust.panicked]⟩ hm'
  · have hz2 : (ck.index + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hidx; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := ck.index.isLt
      rw [BitVec.toNat_add] at h1
      change (ck.index.toNat + 1) % 4294967296 = 0 at h1
      change ck.index.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (nck_length_hmacWith F (keyToBytes32 ck.key) [2#8])
    have hw_sp := hw32 (s0.sp - 68#64)
    have h60 : s0.sp - 68#64 + 8#64 = s0.sp - 60#64 := by bv_arith
    have h52 : s0.sp - 68#64 + 16#64 = s0.sp - 52#64 := by bv_arith
    have h44 : s0.sp - 68#64 + 24#64 = s0.sp - 44#64 := by bv_arith
    rw [h60, h52, h44] at hw_sp
    rw [hw_sp]
    code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalSession.libsignalSessionBin
      img.base (Rust.withPanics (sessionExterns F abs)) hfn (num% (ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::next_chain_key")) 116
    subst hentry
    generalize_entry hentry : (SP img.base F abs).fnAddr nextChainKeyName = entry
    apply SepWPp.of_sepWP_frozen (mid := s0.readReg64 Reg.lr) hfrozen2 hsym2
    wp_steps
    examples_hide_fetches
    apply SepWP.done (by simp_all) (by simp_all)
    intro _ _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by ck_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    have hok := nextChainKey_ok_of_ne F ck hidx
    rw [hok]
    dsimp only
    refine Entails.pure_right ⟨by nofun, by simp_all⟩ ?_
    let ck' : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩
    have hkey_eq : keyToBytes32 ck'.key = hmacWith F (keyToBytes32 ck.key) [2#8] := by
      show keyToBytes32 (bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed)) = _
      rw [← hmacWith_two_eq_chainStep]
      exact keyToBytes32_bytesToKey32 _ (nck_length_hmacWith F _ _)
    rw [pointsToBytes_chainKeyBytes_eq self ck, pointsToBytes_chainKeyBytes_eq ret ck',
        hkey_eq, hw32 ret]
    have hstk := stackAt_nextChainKey_repack s0.sp w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 2#8
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hstk))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by dsimp only [ck', Reg.x19, Reg.x20, Reg.lr, Reg.x29]; ac_rfl)

theorem nextChainKey_ok_of_hmac_ext
    {img : Obj.Image} {F : ShaCompress} {abs ext : String → Option (State → State)}
    (hhmac : HmacOk img F abs)
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hloads : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOkExt img F ext := by
  unfold NextChainKeyOkExt
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName =
      (SP img.base F abs).fnAddr nextChainKeyName := by
    simp only [tripleRatchetProgAtExt, SP, Program.fnAddr_rebase]
  rw [hfn]
  exact ConsumeMessageKeyTransfer.session_subroutine_ok_mono_ext hloads hle (nextChainKey_ok_sessionProg hloads hhmac)

theorem nextChainKey_ok_ext
    {img : Obj.Image} {F : ShaCompress} {abs ext : String → Option (State → State)}
    (hle : ∀ n f, Rust.withPanics (CryptoVerification.LibsignalSession.sessionExterns F abs) n = some f →
      Rust.withPanics ext n = some f)
    (hloads : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOkExt img F ext :=
  nextChainKey_ok_of_hmac_ext (hmac_sha256_ok img F abs hloads) hle hloads

theorem nextChainKey_ok_of_hmac
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hhmac : HmacOk img C.F abs)
    (hloads : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOk img C ctl abs :=
  nextChainKey_ok_of_hmac_ext hhmac (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs) hloads

/-- `ChainKey::next_chain_key` satisfies `NextChainKeyOk` on `tripleRatchetProgAt`. -/
theorem nextChainKey_ok
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img) :
    NextChainKeyOk img C ctl abs :=
  nextChainKey_ok_of_hmac (hmac_sha256_ok img C.F abs hloads) hloads

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `39`) -/

abbrev lsPanicConstAddOverflowSym : String :=
  "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow"

def nextChainKeyPlacedSpec (F : ShaCompress) : Spec ChainKeyGhost where
  pre := fun (self, ck, ret) s =>
    ⌜s.readReg64 .x0 = self ∧ s.readReg64 .x8 = ret⌝ ∗
    (self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s.sp nextChainKeyStack
  post := fun (self, ck, ret) s0 sf =>
    ⌜ck.nextChainKey F ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
    (self ↦ₛ chainKeyBytes ck) ∗
    (match ck.nextChainKey F with
      | .ok ck' => ret ↦ₛ chainKeyBytes ck'
      | .error _ => ⌜False⌝) ∗
    stackAt s0.sp nextChainKeyStack
  onPanic := fun (_, ck, _) s0 sf =>
    ⌜ck.nextChainKey F = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem sepWPp_seq_lscl {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

private theorem hmac_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr (withLsCodeLoaded lsmpl (hmacSpec F)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
        post := (hmacSpec F).post } := by
  refine subroutine_ok_outcome_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hm hsp => ?_
  refine hhmac.mono_outcome (out, ka, key, ia, inp) R s0 hpc hrun ?_ hsp (fun _ hout => hout)
  dsimp only [withLsCodeLoaded, hmacSpec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem next_chain_key_placed_ok [LibsignalPlacement] {F : ShaCompress}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (lsmpl.base 73)
      (withLsCodeLoaded lsmpl (hmacSpec F)))
    (hpan : H lsPanicConstAddOverflowSym = some Rust.panicked) :
    subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (blkPl_39).base
      (withLsCodeLoaded lsmpl (nextChainKeyPlacedSpec F)) := by
  have hpan_ovf : ((blkPC_39).rebase (blkPl_39).base H).externAt?
      (lsρ lsPanicConstAddOverflowSym) = some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpan
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [nextChainKeyPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s0.sp nextChainKeyStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck, memRegion36_unpack ret, stackAt_nextChainKey s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun b0 =>
    SepWPp.exists_elim fun v29 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v19 => ?_
  apply sepWPp_seq_lscl (mid := lsmpl.base 73) hcl0
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmac_placed_ok_at_state hhmac hcl1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 36#64) 2#8]
  apply sepWPp_seq_lscl (mid := (blkPl_39).base + 56#64) hcl1
  wp_call hhmac1 (s0.sp - 68#64, self, keyToBytes32 ck.key, s0.sp - 36#64, [2#8])
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2
  by_cases hidx : ck.index = BitVec.allOnes 32
  · have hidx_max : ck.index = 0xffffffff#32 := hidx
    rw [hidx_max]
    apply sepWPp_seq_lscl (mid := lsρ lsPanicConstAddOverflowSym) hcl2
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_ovf) fun hm' => ?_
    simpa only [withLsCodeLoaded, nextChainKeyPlacedSpec, sepConj_assoc] using
      allowPanic_panicked ⟨nextChainKey_panic_of_eq F ck hidx,
        by simp_all [Rust.panicked]⟩ hm'
  · have hz2 : (ck.index + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hidx; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := ck.index.isLt
      rw [BitVec.toNat_add] at h1
      change (ck.index.toNat + 1) % 4294967296 = 0 at h1
      change ck.index.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (nck_length_hmacWith F (keyToBytes32 ck.key) [2#8])
    have hw_sp := hw32 (s0.sp - 68#64)
    have h60 : s0.sp - 68#64 + 8#64 = s0.sp - 60#64 := by bv_arith
    have h52 : s0.sp - 68#64 + 16#64 = s0.sp - 52#64 := by bv_arith
    have h44 : s0.sp - 68#64 + 24#64 = s0.sp - 44#64 := by bv_arith
    rw [h60, h52, h44] at hw_sp
    rw [hw_sp]
    apply sepWPp_seq_lscl (mid := s0.readReg64 Reg.lr) hcl2
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by ck_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    have hok := nextChainKey_ok_of_ne F ck hidx
    rw [hok]
    dsimp only
    refine Entails.pure_right ⟨by nofun, by simp_all⟩ ?_
    let ck' : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩
    have hkey_eq : keyToBytes32 ck'.key = hmacWith F (keyToBytes32 ck.key) [2#8] := by
      show keyToBytes32 (bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed)) = _
      rw [← hmacWith_two_eq_chainStep]
      exact keyToBytes32_bytesToKey32 _ (nck_length_hmacWith F _ _)
    rw [pointsToBytes_chainKeyBytes_eq self ck, pointsToBytes_chainKeyBytes_eq ret ck',
        hkey_eq, hw32 ret]
    have hstk := stackAt_nextChainKey_repack s0.sp w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 2#8
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hstk))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by dsimp only [ck', Reg.x19, Reg.x20, Reg.lr, Reg.x29]; ac_rfl)

private theorem hmac_placed_cro_ok_at_state [LibsignalPlacement] {prog : Program}
    {F : ShaState → List (BitVec 8) → ShaState} {addr : BitVec 64} {s : State}
    (hhmac : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl (hmacSpec F)))
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun (out, ka, key, ia, inp) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
            s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
            inp.length = 1⌝ ∗
          memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
        post := (hmacSpec F).post } := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, hmacSpec] at hm ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine ⟨hmem ▸ hcl, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem next_chain_key_placed_cro_ok [LibsignalPlacement] {F : ShaCompress}
    {H : String → Option (State → State)}
    (hhmac : subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (lsmpl.base 73)
      (withLsCodeRoLoaded lsmpl (hmacSpec F)))
    (hpan : H lsPanicConstAddOverflowSym = some Rust.panicked) :
    subroutine_ok ((blkPC_39).rebase (blkPl_39).base H) (blkPl_39).base
      (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec F)) := by
  have hpan_ovf : ((blkPC_39).rebase (blkPl_39).base H).externAt?
      (lsρ lsPanicConstAddOverflowSym) = some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpan
  apply subroutine_ok_of_sepWPp
  intro ⟨self, ck, ret⟩ R s0 hpc hrun hpre hsp0
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [nextChainKeyPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  refine ⟨(self ↦ₛ chainKeyBytes ck) ∗ memRegion ret 36 ∗ stackAt s0.sp nextChainKeyStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  rw [pointsToBytes_chainKeyBytes_eq self ck, memRegion36_unpack ret, stackAt_nextChainKey s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun b0 =>
    SepWPp.exists_elim fun v29 => SepWPp.exists_elim fun v30 =>
    SepWPp.exists_elim fun v20 => SepWPp.exists_elim fun v19 => ?_
  apply sepWPp_seq_lscro (mid := lsmpl.base 73) hcl0
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl1
  have hhmac1 := hmac_placed_cro_ok_at_state hhmac hcl1
  have hlen_key : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 36#64) 2#8]
  apply sepWPp_seq_lscro (mid := (blkPl_39).base + 56#64) hcl1
  wp_call hhmac1 (s0.sp - 68#64, self, keyToBytes32 ck.key, s0.sp - 36#64, [2#8])
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcl2
  by_cases hidx : ck.index = BitVec.allOnes 32
  · have hidx_max : ck.index = 0xffffffff#32 := hidx
    rw [hidx_max]
    apply sepWPp_seq_lscro (mid := lsρ lsPanicConstAddOverflowSym) hcl2
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.panic (by simp_all) (by simpa using hpan_ovf) fun hm' => ?_
    simpa only [withLsCodeRoLoaded, nextChainKeyPlacedSpec, sepConj_assoc] using
      allowPanic_panicked ⟨nextChainKey_panic_of_eq F ck hidx,
        by simp_all [Rust.panicked]⟩ hm'
  · have hz2 : (ck.index + 1#32 == 0#32) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hidx; apply BitVec.eq_of_toNat_eq
      have h1 := congrArg BitVec.toNat h
      have h2 := ck.index.isLt
      rw [BitVec.toNat_add] at h1
      change (ck.index.toNat + 1) % 4294967296 = 0 at h1
      change ck.index.toNat = 4294967295
      omega
    obtain ⟨w0, w1, w2, w3, _, hw32⟩ :=
      exists_unpack64_of_length_32 (nck_length_hmacWith F (keyToBytes32 ck.key) [2#8])
    have hw_sp := hw32 (s0.sp - 68#64)
    have h60 : s0.sp - 68#64 + 8#64 = s0.sp - 60#64 := by bv_arith
    have h52 : s0.sp - 68#64 + 16#64 = s0.sp - 52#64 := by bv_arith
    have h44 : s0.sp - 68#64 + 24#64 = s0.sp - 44#64 := by bv_arith
    rw [h60, h52, h44] at hw_sp
    rw [hw_sp]
    apply sepWPp_seq_lscro (mid := s0.readReg64 Reg.lr) hcl2
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro _
    refine SepWPp.done (by simp_all) (by simp_all) ⟨fun hm => ?_, rfl, by ck_cc_close⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    have hok := nextChainKey_ok_of_ne F ck hidx
    rw [hok]
    dsimp only
    refine Entails.pure_right ⟨by nofun, by simp_all⟩ ?_
    let ck' : ChainKey := ⟨bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed), ck.index + 1⟩
    have hkey_eq : keyToBytes32 ck'.key = hmacWith F (keyToBytes32 ck.key) [2#8] := by
      show keyToBytes32 (bytesToKey32 (Ratchet.chainHmac F ck.key Ratchet.chainKeySeed)) = _
      rw [← hmacWith_two_eq_chainStep]
      exact keyToBytes32_bytesToKey32 _ (nck_length_hmacWith F _ _)
    rw [pointsToBytes_chainKeyBytes_eq self ck, pointsToBytes_chainKeyBytes_eq ret ck',
        hkey_eq, hw32 ret]
    have hstk := stackAt_nextChainKey_repack s0.sp w0 w1 w2 w3
      (s0.readReg64 Reg.x29) (s0.readReg64 Reg.lr) (s0.readReg64 Reg.x20) (s0.readReg64 Reg.x19) 2#8
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right hstk))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by dsimp only [ck', Reg.x19, Reg.x20, Reg.lr, Reg.x29]; ac_rfl)

end CryptoVerification.LibsignalTripleRatchet
