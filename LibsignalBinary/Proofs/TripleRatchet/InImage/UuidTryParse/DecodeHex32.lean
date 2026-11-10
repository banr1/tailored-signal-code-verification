/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `uuid::parser::decode_hex32`

Verifies the 32-nibble hexadecimal decoder `uuid::parser::decode_hex32` against the pure
`decodeHex32` specification.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure nibble and hex-pair lemmas -/

def rawNibble (c : BitVec 8) : BitVec 8 :=
  if (9#32).ult (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 c - 48#32) &&& 255#64)) = true then
    BitVec.truncate 8 (BitVec.truncate 32 (BitVec.zeroExtend 64 c ||| 137438953504#64) - 87#32)
  else BitVec.truncate 8 (BitVec.zeroExtend 32 c - 48#32)

def rawInvalid (c : BitVec 8) : BitVec 64 :=
  if (250#32).ule (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 c ||| 137438953504#64) - 103#32) &&& 255#64)) = true then
    0#64
  else if (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 c - 48#32) &&& 255#64)).ule 9#32 = true then
    0#64
  else 1#64

def stepAcc (acc : BitVec 64) (c : BitVec 8) : BitVec 64 :=
  BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 acc) ||| rawInvalid c))

def isHexByte (c : BitVec 8) : Bool :=
  decide (c - 0x30#8 < 10#8) || decide ((c ||| 0x20#8) - 0x61#8 < 6#8)

theorem rawInvalid_eq (c : BitVec 8) :
    rawInvalid c = if isHexByte c then 0#64 else 1#64 := by
  revert c
  unfold rawInvalid isHexByte
  decide +kernel

theorem rawNibble_digit (c : BitVec 8) (h : c - 0x30#8 < 10#8) :
    rawNibble c = c - 0x30#8 := by
  revert c
  unfold rawNibble
  decide +kernel

theorem rawNibble_alpha (c : BitVec 8) (h1 : ¬ (c - 0x30#8 < 10#8))
    (h2 : (c ||| 0x20#8) - 0x61#8 < 6#8) :
    rawNibble c = (c ||| 0x20#8) - 0x61#8 + 10#8 := by
  revert c
  unfold rawNibble
  decide +kernel

theorem hexNibble_eq (c : BitVec 8) :
    hexNibble c = if isHexByte c then some (rawNibble c) else none := by
  unfold hexNibble isHexByte
  by_cases h1 : c - 0x30#8 < 10#8
  · simp [h1, rawNibble_digit c h1]
  · by_cases h2 : (c ||| 0x20#8) - 0x61#8 < 6#8
    · simp [h1, h2, rawNibble_alpha c h1 h2]
    · simp [h1, h2]

theorem stepAcc_one (c : BitVec 8) : stepAcc 1#64 c = 1#64 := by
  unfold stepAcc
  rw [rawInvalid_eq]
  cases isHexByte c <;> rfl

theorem stepAcc_zero (c : BitVec 8) :
    stepAcc 0#64 c = if isHexByte c then 0#64 else 1#64 := by
  unfold stepAcc
  rw [rawInvalid_eq]
  cases isHexByte c <;> rfl

theorem foldl_stepAcc_one (bs : List (BitVec 8)) :
    bs.foldl stepAcc 1#64 = 1#64 := by
  induction bs with
  | nil => rfl
  | cons c rest ih => simp only [List.foldl_cons, stepAcc_one, ih]

theorem foldl_stepAcc_zero (bs : List (BitVec 8)) :
    bs.foldl stepAcc 0#64 = if bs.all isHexByte then 0#64 else 1#64 := by
  induction bs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons, List.all_cons, stepAcc_zero]
    rcases Bool.eq_false_or_eq_true (isHexByte c) with hc | hc
    · simp only [hc, Bool.true_and, ↓reduceIte, ih]
    · simp only [hc, Bool.false_and]; exact foldl_stepAcc_one rest

def rawCombine (hi lo : BitVec 8) : BitVec 8 :=
  (hi <<< 4) ||| lo

theorem rawCombine_step_eq (hi lo : BitVec 8) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 lo ||| BitVec.zeroExtend 64 (BitVec.zeroExtend 32 hi <<< 4)) =
    rawCombine hi lo := by
  unfold rawCombine
  ext i hi8
  simp
  exact Bool.or_comm _ _

def decodeNibbles : List (BitVec 8) → List (BitVec 8)
  | hi :: lo :: rest => rawCombine hi lo :: decodeNibbles rest
  | _ => []

theorem decodeHex_cons2 (hi lo : BitVec 8) (rest : List (BitVec 8)) :
    decodeHex (hi :: lo :: rest) =
      if isHexByte hi && isHexByte lo then
        (decodeHex rest).map (fun r => rawCombine (rawNibble hi) (rawNibble lo) :: r)
      else none := by
  conv => lhs; unfold decodeHex
  unfold rawCombine
  rw [hexNibble_eq hi, hexNibble_eq lo]
  cases isHexByte hi <;> cases isHexByte lo <;> cases decodeHex rest <;> rfl


theorem decodeHex_pair_step (hi lo : BitVec 8) (rest : List (BitVec 8))
    (ih : decodeHex rest = if rest.all isHexByte then some (decodeNibbles (rest.map rawNibble)) else none) :
    decodeHex (hi :: lo :: rest) =
      if (hi :: lo :: rest).all isHexByte then
        some (decodeNibbles ((hi :: lo :: rest).map rawNibble))
      else none := by
  rw [decodeHex_cons2, ih]
  simp only [List.all_cons, List.map_cons, decodeNibbles]
  cases isHexByte hi <;> cases isHexByte lo <;> cases rest.all isHexByte <;> rfl

theorem decodeHex_even : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 2 * k →
    decodeHex bs =
      if bs.all isHexByte then some (decodeNibbles (bs.map rawNibble)) else none
  | 0, [], _ => rfl
  | k + 1, hi :: lo :: rest, h =>
    decodeHex_pair_step hi lo rest (decodeHex_even k rest (by simp at h; omega))

theorem length_decodeNibbles : ∀ (k : Nat) (ns : List (BitVec 8)), ns.length = 2 * k →
    (decodeNibbles ns).length = k
  | 0, [], _ => rfl
  | k + 1, _ :: _ :: rest, h => by
    simp only [decodeNibbles, List.length_cons]
    rw [length_decodeNibbles k rest (by simp at h; omega)]

theorem decodeHex32_of_length_32 {hex : List (BitVec 8)} (h : hex.length = 32) :
    decodeHex32 hex =
      if hex.all isHexByte then
        some ⟨decodeNibbles (hex.map rawNibble),
          length_decodeNibbles 16 (hex.map rawNibble) (by simp [h])⟩
      else none := by
  unfold decodeHex32
  rw [decodeHex_even 16 hex h]
  have hlen : (decodeNibbles (hex.map rawNibble)).length = 16 :=
    length_decodeNibbles 16 (hex.map rawNibble) (by simp [h])
  cases hex.all isHexByte
  · rfl
  · simp [Option.bind, hlen]


/-! ## Loop invariant and step lemmas -/

structure DecodeLoopInv (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) (i : Nat) : Prop where
  hpc : s.pc = entry + bv% (20)
  hrun : s.status = .Running
  hsp : s.sp = sp'
  hsp_align : sp' &&& 15#64 = 0#64
  hx0 : s.readReg64 (Reg.gpr 0#5) = out
  hx1 : s.readReg64 (Reg.gpr 1#5) = src
  hx8 : s.readReg64 (Reg.gpr 8#5) = acc
  hx9 : s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 i
  hx10 : s.readReg64 (Reg.gpr 10#5) = sp'
  hx30 : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5)
  htrace : s.trace = s0.trace
  hcs : CalleeSavedPreserved s0 s

structure DecodeLoopPost (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) : Prop where
  hpc : s.pc = entry + bv% (88)
  hrun : s.status = .Running
  hsp : s.sp = sp'
  hsp_align : sp' &&& 15#64 = 0#64
  hx0 : s.readReg64 (Reg.gpr 0#5) = out
  hx1 : s.readReg64 (Reg.gpr 1#5) = src
  hx8 : s.readReg64 (Reg.gpr 8#5) = acc
  hx30 : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5)
  htrace : s.trace = s0.trace
  hcs : CalleeSavedPreserved s0 s

theorem decode_hex32_iter_step (b : BitVec 64)
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 s : State) (out src sp' acc : BitVec 64) (i : Nat)
    (c old_b : BitVec 8) (Frame : SepProp) (post : State → SepProp → Prop)
    (hinv : DecodeLoopInv ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 s out src sp' acc i)
    (hnext : ∀ s' : State,
      s'.pc = (if (BitVec.ofNat 64 i + 1#64 != 32#64) = true
               then (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + 20#64
               else (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + 88#64) →
      s'.status = .Running →
      s'.sp = sp' →
      s'.readReg64 (Reg.gpr 0#5) = out →
      s'.readReg64 (Reg.gpr 1#5) = src →
      s'.readReg64 (Reg.gpr 8#5) = stepAcc acc c →
      s'.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (i + 1) →
      s'.readReg64 (Reg.gpr 10#5) = sp' →
      s'.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5) →
      s'.trace = s0.trace →
      CalleeSavedPreserved s0 s' →
      SepWP (libsignalSessionCode.rebase b hooks) target_pc s'
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame) post) :
    SepWP (libsignalSessionCode.rebase b hooks) target_pc s
      (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗ Frame) post := by
  rcases hinv with ⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8, hx9, hx10, hx30, htrace, hcs⟩
  have hsp' : s.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc hnext ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply hnext
  · rfl
  · simp only [arm64_norm, hrun]
  · simp only [arm64_norm, hsp]
  · simp only [arm64_norm, hx0]
  · simp only [arm64_norm, hx1]
  · rfl
  · simp only [arm64_norm, BitVec.ofNat_add]
  · simp only [arm64_norm, hx10]
  · simp only [arm64_norm, hx30]
  · simp only [arm64_norm, htrace]
  · simp (config := { decide := true }) only [arm64_norm, hcs]

theorem bne_32_of_lt {i : Nat} (hi : i + 1 < 32) :
    (BitVec.ofNat 64 i + 1#64 != 32#64) = true := by
  rw [bne_iff_ne]
  intro h
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hnat
  omega

theorem decode_hex32_loop (b : BitVec 64)
    (hooks : String → Option (State → State))
    (target_pc : BitVec 64) (s0 : State) (out src sp' : BitVec 64)
    (post : State → SepProp → Prop) :
    ∀ (rem_src rem_sp : List (BitVec 8)) (i : Nat) (acc : BitVec 64)
      (s : State) (Frame : SepProp),
      rem_src ≠ [] →
      rem_sp.length = rem_src.length →
      i + rem_src.length = 32 →
      DecodeLoopInv ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 s out src sp' acc i →
      (∀ sf : State,
        DecodeLoopPost ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 sf out src sp'
          (rem_src.foldl stepAcc acc) →
        SepWP (libsignalSessionCode.rebase b hooks) target_pc sf
          (((src + BitVec.ofNat 64 i) ↦ₛ rem_src) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ (rem_src.map rawNibble)) ∗ Frame) post) →
      SepWP (libsignalSessionCode.rebase b hooks) target_pc s
        (((src + BitVec.ofNat 64 i) ↦ₛ rem_src) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ rem_sp) ∗ Frame) post
  | [], _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | c :: rest_src, rem_sp, i, acc, s, Frame, _, hlen_sp, hi_sum, hinv, hcont => by
    rcases rem_sp with _ | ⟨old_b, rest_sp⟩
    · simp at hlen_sp
    have hsplit_pre :
        (((src + BitVec.ofNat 64 i) ↦ₛ (c :: rest_src)) ∗
         ((sp' + BitVec.ofNat 64 i) ↦ₛ (old_b :: rest_sp)) ∗ Frame) =
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ old_b) ∗
         (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_src) ∗
          ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) := by
      rw [pointsToBytes_cons_off src i c rest_src, pointsToBytes_cons_off sp' i old_b rest_sp]
      ac_rfl
    rw [hsplit_pre]
    refine decode_hex32_iter_step b hooks target_pc s0 s out src sp' acc i c old_b
      (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_src) ∗
       ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame) post hinv ?_
    intro s' hpc' hrun' hsp' hx0' hx1' hx8' hx9' hx10' hx30' htrace' hcs'
    rcases rest_src with _ | ⟨c2, rest_src'⟩
    · have hi31 : i = 31 := by simp at hi_sum; omega
      subst hi31
      have hpc_done : s'.pc = (libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name + 88#64 := by
        simpa using hpc'
      have hpost_inv : DecodeLoopPost ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 s'
          out src sp' ([c].foldl stepAcc acc) :=
        ⟨hpc_done, hrun', hsp', hinv.hsp_align, hx0', hx1', hx8', hx30', htrace', hcs'⟩
      have hrest_sp : rest_sp = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen_sp)
      subst hrest_sp
      have hrecomb :
          (((src + BitVec.ofNat 64 31) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 31) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (31 + 1)) ↦ₛ []) ∗
            ((sp' + BitVec.ofNat 64 (31 + 1)) ↦ₛ []) ∗ Frame)) =
          (((src + BitVec.ofNat 64 31) ↦ₛ [c]) ∗
           ((sp' + BitVec.ofNat 64 31) ↦ₛ ([c].map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons, List.map_nil, pointsToBytes_singleton, pointsToBytes_nil,
          emp_sepConj]
      rw [hrecomb]
      exact hcont s' hpost_inv
    · have hi_lt : i + 1 < 32 := by simp at hi_sum; omega
      have hbne : (BitVec.ofNat 64 i + 1#64 != 32#64) = true := bne_32_of_lt hi_lt
      simp only [hbne, ↓reduceIte] at hpc'
      have hnext_inv : DecodeLoopInv ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 s'
          out src sp' (stepAcc acc c) (i + 1) :=
        ⟨hpc', hrun', hsp', hinv.hsp_align, hx0', hx1', hx8', hx9', hx10', hx30', htrace', hcs'⟩
      have hrearr1 :
          (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗
           (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
            ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗ Frame)) =
          (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ rest_sp) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) := by
        ac_rfl
      rw [hrearr1]
      refine decode_hex32_loop b hooks target_pc s0 out src sp' post
        (c2 :: rest_src') rest_sp (i + 1) (stepAcc acc c) s'
        (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)
        (List.cons_ne_nil _ _) (by simp at hlen_sp; omega) (by simp at hi_sum ⊢; omega)
        hnext_inv ?_
      intro sf hpost_sf
      have hrearr2 :
          (((src + BitVec.ofNat 64 (i + 1)) ↦ₛ (c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 (i + 1)) ↦ₛ ((c2 :: rest_src').map rawNibble)) ∗
           (((src + BitVec.ofNat 64 i) ↦₈ c) ∗ ((sp' + BitVec.ofNat 64 i) ↦₈ rawNibble c) ∗ Frame)) =
          (((src + BitVec.ofNat 64 i) ↦ₛ (c :: c2 :: rest_src')) ∗
           ((sp' + BitVec.ofNat 64 i) ↦ₛ ((c :: c2 :: rest_src').map rawNibble)) ∗ Frame) := by
        simp only [List.map_cons]
        rw [pointsToBytes_cons_off src i c (c2 :: rest_src'),
            pointsToBytes_cons_off sp' i (rawNibble c) (rawNibble c2 :: List.map rawNibble rest_src')]
        ac_rfl
      rw [hrearr2]
      exact hcont sf hpost_sf

/-! ## Post-loop and full `decode_hex32` proof -/

theorem list_length_8_elim {α : Type _} (xs : List α) (h : xs.length = 8) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7, xs = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩

theorem list_length_16_elim {α : Type _} (xs : List α) (h : xs.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
  have h1 : (xs.take 8).length = 8 := by simp [h]
  have h2 : (xs.drop 8).length = 8 := by simp [h]
  rcases list_length_8_elim _ h1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, e1⟩
  rcases list_length_8_elim _ h2 with ⟨x8, x9, x10, x11, x12, x13, x14, x15, e2⟩
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, ?_⟩
  rw [← List.take_append_drop 8 xs, e1, e2]; rfl

theorem list_length_32_elim {α : Type _} (xs : List α) (h : xs.length = 32) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
            x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] := by
  have h1 : (xs.take 16).length = 16 := by simp [h]
  have h2 : (xs.drop 16).length = 16 := by simp [h]
  rcases list_length_16_elim _ h1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, e1⟩
  rcases list_length_16_elim _ h2 with ⟨x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, e2⟩
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
          x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, ?_⟩
  rw [← List.take_append_drop 16 xs, e1, e2]; rfl

theorem list_length_17_elim {α : Type _} (xs : List α) (h : xs.length = 17) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16] := by
  rcases xs with _ | ⟨x0, xs'⟩
  · simp at h
  have h1 : xs'.length = 16 := by simp at h; omega
  rcases list_length_16_elim xs' h1 with ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, e1⟩
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, congrArg (x0 :: ·) e1⟩

theorem pointsToBytes_32_expand (a : BitVec 64)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15
     n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 : BitVec 8) :
    (a ↦ₛ [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
           n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]) =
    ((a ↦₈ n0) ∗ ((a + 1#64) ↦₈ n1) ∗ ((a + 2#64) ↦₈ n2) ∗ ((a + 3#64) ↦₈ n3) ∗
     ((a + 4#64) ↦₈ n4) ∗ ((a + 5#64) ↦₈ n5) ∗ ((a + 6#64) ↦₈ n6) ∗ ((a + 7#64) ↦₈ n7) ∗
     ((a + 8#64) ↦₈ n8) ∗ ((a + 9#64) ↦₈ n9) ∗ ((a + 10#64) ↦₈ n10) ∗ ((a + 11#64) ↦₈ n11) ∗
     ((a + 12#64) ↦₈ n12) ∗ ((a + 13#64) ↦₈ n13) ∗ ((a + 14#64) ↦₈ n14) ∗ ((a + 15#64) ↦₈ n15) ∗
     ((a + 16#64) ↦₈ n16) ∗ ((a + 17#64) ↦₈ n17) ∗ ((a + 18#64) ↦₈ n18) ∗ ((a + 19#64) ↦₈ n19) ∗
     ((a + 20#64) ↦₈ n20) ∗ ((a + 21#64) ↦₈ n21) ∗ ((a + 22#64) ↦₈ n22) ∗ ((a + 23#64) ↦₈ n23) ∗
     ((a + 24#64) ↦₈ n24) ∗ ((a + 25#64) ↦₈ n25) ∗ ((a + 26#64) ↦₈ n26) ∗ ((a + 27#64) ↦₈ n27) ∗
     ((a + 28#64) ↦₈ n28) ∗ ((a + 29#64) ↦₈ n29) ∗ ((a + 30#64) ↦₈ n30) ∗ ((a + 31#64) ↦₈ n31)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_17_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16]) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
     ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
     ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
     ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
     ((a + 16#64) ↦₈ b16)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_16_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    ((a + 1#64) ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
    (((a + 1#64) ↦₈ b0) ∗ ((a + 2#64) ↦₈ b1) ∗ ((a + 3#64) ↦₈ b2) ∗ ((a + 4#64) ↦₈ b3) ∗
     ((a + 5#64) ↦₈ b4) ∗ ((a + 6#64) ↦₈ b5) ∗ ((a + 7#64) ↦₈ b6) ∗ ((a + 8#64) ↦₈ b7) ∗
     ((a + 9#64) ↦₈ b8) ∗ ((a + 10#64) ↦₈ b9) ∗ ((a + 11#64) ↦₈ b10) ∗ ((a + 12#64) ↦₈ b11) ∗
     ((a + 13#64) ↦₈ b12) ∗ ((a + 14#64) ↦₈ b13) ∗ ((a + 15#64) ↦₈ b14) ∗ ((a + 16#64) ↦₈ b15)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_16_tail_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (Tail : SepProp) :
    ((a + 1#64) ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) ∗ Tail =
    (((a + 1#64) ↦₈ b0) ∗ ((a + 2#64) ↦₈ b1) ∗ ((a + 3#64) ↦₈ b2) ∗ ((a + 4#64) ↦₈ b3) ∗
     ((a + 5#64) ↦₈ b4) ∗ ((a + 6#64) ↦₈ b5) ∗ ((a + 7#64) ↦₈ b6) ∗ ((a + 8#64) ↦₈ b7) ∗
     ((a + 9#64) ↦₈ b8) ∗ ((a + 10#64) ↦₈ b9) ∗ ((a + 11#64) ↦₈ b10) ∗ ((a + 12#64) ↦₈ b11) ∗
     ((a + 13#64) ↦₈ b12) ∗ ((a + 14#64) ↦₈ b13) ∗ ((a + 15#64) ↦₈ b14) ∗ ((a + 16#64) ↦₈ b15) ∗ Tail) := by
  rw [pointsToBytes_16_expand a]
  simp only [sepConj_assoc]

theorem pointsToBytes_32_sub32_expand (sp : BitVec 64)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15
     n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 : BitVec 8)
    (Tail : SepProp) :
    ((sp - 32#64) ↦ₛ [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]) ∗ Tail =
    ((sp - 32#64) ↦₈ n0 ∗ (sp - 31#64) ↦₈ n1 ∗ (sp - 30#64) ↦₈ n2 ∗ (sp - 29#64) ↦₈ n3 ∗
     (sp - 28#64) ↦₈ n4 ∗ (sp - 27#64) ↦₈ n5 ∗ (sp - 26#64) ↦₈ n6 ∗ (sp - 25#64) ↦₈ n7 ∗
     (sp - 24#64) ↦₈ n8 ∗ (sp - 23#64) ↦₈ n9 ∗ (sp - 22#64) ↦₈ n10 ∗ (sp - 21#64) ↦₈ n11 ∗
     (sp - 20#64) ↦₈ n12 ∗ (sp - 19#64) ↦₈ n13 ∗ (sp - 18#64) ↦₈ n14 ∗ (sp - 17#64) ↦₈ n15 ∗
     (sp - 16#64) ↦₈ n16 ∗ (sp - 15#64) ↦₈ n17 ∗ (sp - 14#64) ↦₈ n18 ∗ (sp - 13#64) ↦₈ n19 ∗
     (sp - 12#64) ↦₈ n20 ∗ (sp - 11#64) ↦₈ n21 ∗ (sp - 10#64) ↦₈ n22 ∗ (sp - 9#64) ↦₈ n23 ∗
     (sp - 8#64) ↦₈ n24 ∗ (sp - 7#64) ↦₈ n25 ∗ (sp - 6#64) ↦₈ n26 ∗ (sp - 5#64) ↦₈ n27 ∗
     (sp - 4#64) ↦₈ n28 ∗ (sp - 3#64) ↦₈ n29 ∗ (sp - 2#64) ↦₈ n30 ∗ (sp - 1#64) ↦₈ n31 ∗ Tail) := by
  simp only [arm64_norm, sepConj_assoc]

def decodeHex32ResultAt (out : BitVec 64) : Option (List.Vector (BitVec 8) 16) → SepProp
  | some u => (out ↦₈ 1#8) ∗ ((out + 1#64) ↦ₛ u.toList)
  | none => (out ↦₈ 0#8) ∗ memRegion (out + 1#64) 16

def decodeHex32Spec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, src, hex) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = src ∧ hex.length = 32⌝ ∗
      (src ↦ₛ hex) ∗ memRegion out 17 ∗ stackAt s.sp 0x20
  post := fun (out, src, hex) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (src ↦ₛ hex) ∗ decodeHex32ResultAt out (decodeHex32 hex) ∗ stackAt s0.sp 0x20

theorem stack32_zero_eq_replicate (sp : BitVec 64) :
    (((sp - 32#64) ↦₆₄ 0#64) ∗ ((sp - 24#64) ↦₆₄ 0#64) ∗
     ((sp - 16#64) ↦₆₄ 0#64) ∗ ((sp - 8#64) ↦₆₄ 0#64)) =
    ((sp - 32#64) ↦ₛ List.replicate 32 0#8) := by
  have h32 : List.replicate 32 (0#8) =
      List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ List.replicate 8 0#8)) := rfl
  rw [h32, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [List.length_replicate, pointsToBytes_replicate8_zero]
  have a1 : sp - 32#64 + BitVec.ofNat 64 8 = sp - 24#64 := by bv_arith
  have a2 : sp - 24#64 + BitVec.ofNat 64 8 = sp - 16#64 := by bv_arith
  have a3 : sp - 16#64 + BitVec.ofNat 64 8 = sp - 8#64 := by bv_arith
  rw [a1, a2, a3]

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

theorem pointsToBytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (h : bs.length = n) (hle : n ≤ 2 ^ 64) :
    (a ↦ₛ bs) ⊢ memRegion a n := by
  rw [memRegion_eq_exists_bytes a n hle]
  exact Entails.trans (Entails.of_eq (pure_sepConj_of_true h (a ↦ₛ bs)).symm)
    (Entails.sepExists_intro (P := fun bs => ⌜bs.length = n⌝ ∗ a ↦ₛ bs) bs)

theorem pointsToBytes_entails_stackAt_32 (sp : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    ((sp - 32#64) ↦ₛ bs) ⊢ stackAt sp 0x20 :=
  pointsToBytes_entails_memRegion (sp - 32#64) bs 0x20 h (by decide)

theorem decode_hex32_post_err (b : BitVec 64)
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = false)
    (hpost : DecodeLoopPost ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 sf out src (s0.sp - 32#64)
      (hex.foldl stepAcc 0#64)) :
    SepWP (libsignalSessionCode.rebase b hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ₛ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ ⌜s'.trace = s0.trace⌝ ∗ (src ↦ₛ hex) ∗
             decodeHex32ResultAt out (decodeHex32 hex) ∗ stackAt s0.sp 0x20 ∗ R)) := by
  rcases hpost with ⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 1#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hmem17 : memRegion out 17 = (∃∗ b0 : BitVec 8, out ↦₈ b0) ∗ memRegion (out + 1#64) 16 := by
    rw [show (17 : Nat) = 1 + 16 from rfl, memRegion_split out 1 16 (by decide), memRegion_one]
  rw [hmem17]
  wp_pull_exists
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  have hdec : decodeHex32 hex = none := by
    rw [decodeHex32_of_length_32 hlen, hall]; rfl
  rw [hdec]
  dsimp only [decodeHex32ResultAt]
  simp only [arm64_norm, htrace, pure_true, emp_sepConj]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp (hex.map rawNibble) (by simp [hlen])
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  ac_rfl

theorem decode_hex32_post_ok (b : BitVec 64)
    (hooks : String → Option (State → State))
    (s0 sf : State) (out src : BitVec 64) (hex : List (BitVec 8)) (R : SepProp)
    (hlen : hex.length = 32)
    (hall : hex.all isHexByte = true)
    (hpost : DecodeLoopPost ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name) s0 sf out src (s0.sp - 32#64)
      (hex.foldl stepAcc 0#64)) :
    SepWP (libsignalSessionCode.rebase b hooks) (s0.readReg64 (Reg.gpr 30#5)) sf
      ((src ↦ₛ hex) ∗ ((s0.sp - 32#64) ↦ₛ (hex.map rawNibble)) ∗ memRegion out 17 ∗ R)
      (fun s' Q =>
        s'.status = .Running ∧
        s'.sp = s0.sp ∧
        CalleeSavedPreserved s0 s' ∧
        (Q ⊢ ⌜s'.trace = s0.trace⌝ ∗ (src ↦ₛ hex) ∗
             decodeHex32ResultAt out (decodeHex32 hex) ∗ stackAt s0.sp 0x20 ∗ R)) := by
  rcases hpost with ⟨hpc, hrun, hsp, hsp_align, hx0, hx1, hx8_0, hx30, htrace, hcs⟩
  have hx8 : sf.readReg64 (Reg.gpr 8#5) = 0#64 := by
    rw [hx8_0, foldl_stepAcc_zero, hall]; rfl
  clear hx8_0
  have hsp' : sf.sp &&& 15#64 = 0#64 := hsp ▸ hsp_align
  have hns_len : (hex.map rawNibble).length = 32 := by simp [hlen]
  rcases list_length_32_elim (hex.map rawNibble) hns_len with
    ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, hns⟩
  have hdec_len :
      (decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]).length = 16 := rfl
  have hdec : decodeHex32 hex =
      some ⟨decodeNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                           n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31],
            hdec_len⟩ := by
    rw [decodeHex32_of_length_32 hlen]
    simp only [hall, ↓reduceIte]
    congr 1
    exact Subtype.ext (congrArg decodeNibbles hns)
  have hdec_res : decodeHex32ResultAt out (decodeHex32 hex) =
      (out ↦₈ 1#8) ∗
      ((out + 1#64) ↦ₛ
        [rawCombine n0 n1, rawCombine n2 n3, rawCombine n4 n5, rawCombine n6 n7,
         rawCombine n8 n9, rawCombine n10 n11, rawCombine n12 n13, rawCombine n14 n15,
         rawCombine n16 n17, rawCombine n18 n19, rawCombine n20 n21, rawCombine n22 n23,
         rawCombine n24 n25, rawCombine n26 n27, rawCombine n28 n29, rawCombine n30 n31]) := by
    rw [hdec]; rfl
  rw [hns, ← hsp, pointsToBytes_32_expand sf.sp]
  rw [memRegion_eq_exists_bytes out 17 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro os
  wp_focus_pure; intro hos_len
  rcases list_length_17_elim os hos_len with
    ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, hos⟩
  rw [hos, pointsToBytes_17_expand out]
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done
  · rfl
  · simp only [arm64_norm, hrun]
  refine ⟨by simp only [arm64_norm, hrun], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hcs], ?_⟩
  simp only [arm64_norm, htrace, pure_true, emp_sepConj, rawCombine_step_eq]
  rw [hdec_res, ← pointsToBytes_32_sub32_expand s0.sp, ← pointsToBytes_16_tail_expand out]
  have hcells := pointsToBytes_entails_stackAt_32 s0.sp
    [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
     n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31] rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hcells)) ?_
  apply entails_of_eq
  ac_rfl

theorem subroutine_ok_of_sepWP_entails {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      s0.spAligned = true →
      SepWP prog (s0.readReg64 (Reg.gpr 30#5)) s0 (spec.pre x s0 ∗ R)
        (fun sf Q =>
          sf.status = .Running ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          (Q ⊢ spec.post x s0 sf ∗ R))) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp_align
  refine ⟨spec.pre x s0 ∗ R, ⌜True⌝, by simpa [sepConj_emp] using hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hsp_align) ?_
  rintro sf Q _ _ ⟨_, hsp, hcs, hent⟩
  refine ⟨fun hmf => by simpa [sepConj_emp] using Satisfies.mono (sepConj_mono_left hent) hmf, hsp, hcs⟩

theorem stackAt_32_split (sp : BitVec 64) :
    stackAt sp 0x20 =
      (∃∗ w0 : BitVec 64, (sp - 32#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 24#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (sp - 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (sp - 8#64) ↦₆₄ w3) := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x20 = 32#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

theorem decodeHex32_ok (b : BitVec 64)
    (hooks : String → Option (State → State)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks) ((libsignalSessionCode.rebase b hooks).fnAddr decodeHex32Name)
      decodeHex32Spec := by
  apply subroutine_ok_of_sepWP_entails
  intro ⟨out, src, hex⟩ R s0 hpc hrun hsp_align
  simp only [decodeHex32Spec, sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hx0, hx1, hlen⟩
  conv => arg 4; rw [stackAt_32_split s0.sp]
  wp_pull_exists
  have hloop := decode_hex32_loop b hooks (s0.readReg64 (Reg.gpr 30#5)) s0 out src (s0.sp - 32#64)
  have herr := fun sf => decode_hex32_post_err b hooks s0 sf out src hex R hlen
  have hok := fun sf => decode_hex32_post_ok b hooks s0 sf out src hex R hlen
  code_fetches CryptoVerification.libsignalSessionCode decodeHex32Bin
    b hooks
    (ls_lemma% fnOff "uuid::parser::decode_hex32") (num% (ls_off% "uuid::parser::decode_hex32")) 380
  dsimp only [decodeHex32Name] at hpc hloop herr hok ⊢
  generalize_entry (libsignalSessionCode.rebase b
    hooks).fnAddr "uuid::parser::decode_hex32" = entry
  examples_hide_fetches
  wp_steps 5
  have hgroup :
      ((src ↦ₛ hex) ∗ memRegion out 17 ∗
       ((s0.sp - 32#64) ↦₆₄ 0#64) ∗ ((s0.sp - 24#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 16#64) ↦₆₄ 0#64) ∗ ((s0.sp - 8#64) ↦₆₄ 0#64) ∗ R) =
      (((src + BitVec.ofNat 64 0) ↦ₛ hex) ∗
       (((s0.sp - 32#64) + BitVec.ofNat 64 0) ↦ₛ List.replicate 32 0#8) ∗
       (memRegion out 17 ∗ R)) := by
    have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
    have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
    rw [h0a, h0b, ← stack32_zero_eq_replicate s0.sp]
    ac_rfl
  rw [hgroup]
  have hsp32_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    unfold State.spAligned at hsp_align
    have h : s0.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := s0.sp.isLt; omega
  have hhex_ne : hex ≠ [] := by intro h; simp [h] at hlen
  refine hloop _ hex (List.replicate 32 0#8) 0 0#64 _ (memRegion out 17 ∗ R)
    hhex_ne (by simp [hlen]) (by omega)
    ⟨rfl, by simp only [arm64_norm, hrun], by simp only [arm64_norm],
     hsp32_align, by simp only [arm64_norm, hx0], by simp only [arm64_norm, hx1],
     by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm, CalleeSavedPreserved.rfl]⟩
    ?_
  intro sf hpost_sf
  have h0a : src + BitVec.ofNat 64 0 = src := by bv_arith
  have h0b : s0.sp - 32#64 + BitVec.ofNat 64 0 = s0.sp - 32#64 := by bv_arith
  rw [h0a, h0b]
  cases hall : hex.all isHexByte
  · exact herr sf hall hpost_sf
  · exact hok sf hall hpost_sf

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse



