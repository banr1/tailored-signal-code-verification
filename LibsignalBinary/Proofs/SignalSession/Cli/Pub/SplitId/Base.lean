/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.AsmConstants

/-!
# Base Layout and Separation-Logic Helpers for `signal_session::public::split_id`

Stack-frame decomposition (`0x60` B), `.rodata` string layouts (`"malformed file"` and `"bundle"`),
overlapping 14-byte copy realignment, 4-byte little-endian `ofLe32` splitting, and `SepWPp` call
combinators.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.SplitId.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.SignalSession.Cli

/-! ## Byte Packing and `.rodata` String Layouts -/

def pack8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

abbrev malfHead6 : List (BitVec 8) := utf8 "malfor"
abbrev malfTail6 : List (BitVec 8) := utf8 "d file"
def malfMid2 : BitVec 16 := 101#8 ++ 109#8
def malfLo : BitVec 64 := pack8 109#8 97#8 108#8 102#8 111#8 114#8 109#8 101#8
def malfHi : BitVec 64 := pack8 109#8 101#8 100#8 32#8 102#8 105#8 108#8 101#8

theorem rodata_malformed_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_str% "malformed file") - libsignalSessionImage.dataOff)).take 14 =
      utf8 "malformed file" := by
  decide +kernel

theorem rodata_bundle_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_str% "bundle") - libsignalSessionImage.dataOff)).take 6 =
      utf8 "bundle" := by
  decide +kernel

theorem rodata_malformed_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "malformed file")) ↦ᵣ utf8 "malformed file") ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (dataOff := libsignalSessionImage.dataOff) rfl
    (secOff := num% (ls_str% "malformed file")) (secLen := 14)
    (List.mem_of_elem_eq_true (by decide +kernel))
    (Nat.le_of_ble_eq_true (by decide +kernel))
    (by decide +kernel)
    (Nat.le_of_ble_eq_true (by decide +kernel))
    (by decide +kernel) hro hP
  rwa [rodata_malformed_eq] at h

theorem rodata_bundle_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (dataOff := libsignalSessionImage.dataOff) rfl
    (secOff := num% (ls_str% "bundle")) (secLen := 6)
    (List.mem_of_elem_eq_true (by decide +kernel))
    (Nat.le_of_ble_eq_true (by decide +kernel))
    (by decide +kernel)
    (Nat.le_of_ble_eq_true (by decide +kernel))
    (by decide +kernel) hro hP
  rwa [rodata_bundle_eq] at h

theorem pointsToBytesRO_malf_8_6 (p : BitVec 64) :
    (p ↦ᵣ utf8 "malformed file") =
      (p ↦₆₄ᵣ malfLo) ∗ ((p + 8#64) ↦ᵣ malfTail6) := by
  have heq : utf8 "malformed file" = unpack64 malfLo ++ malfTail6 := by decide +kernel
  rw [heq, pointsToBytesRO_append, ← pointsTo64RO_eq_pointsToBytesRO]
  simp only [unpack64_length]

theorem pointsToBytesRO_malf_6_8 (p : BitVec 64) :
    (p ↦ᵣ utf8 "malformed file") =
      (p ↦ᵣ malfHead6) ∗ ((p + 6#64) ↦₆₄ᵣ malfHi) := by
  have heq : utf8 "malformed file" = malfHead6 ++ unpack64 malfHi := by decide +kernel
  have hlen : malfHead6.length = 6 := by decide +kernel
  rw [heq, pointsToBytesRO_append, hlen, ← pointsTo64RO_eq_pointsToBytesRO]

/-! ## PC-Relative `ADRP` and `ADD` Address Lemmas -/

theorem adrp_malf_ok {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "libsignal_cli::public::split_id")) :
    (((fnBase + 60#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_str% "malformed file") -
        page% (ls_off% "libsignal_cli::public::split_id" + 60))) +
      bv% ((ls_str% "malformed file") % 4096) =
      b + bv% (ls_str% "malformed file") := by
  subst hfn
  bv_arith

theorem adrp_bundle_ok {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "libsignal_cli::public::split_id")) :
    (((fnBase + 84#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_str% "bundle") -
        page% (ls_off% "libsignal_cli::public::split_id" + 84))) +
      bv% ((ls_str% "bundle") % 4096) =
      b + bv% (ls_str% "bundle") := by
  subst hfn
  bv_arith

theorem adrp_malf_err {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "libsignal_cli::public::split_id")) :
    (((fnBase + 192#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_str% "malformed file") -
        page% (ls_off% "libsignal_cli::public::split_id" + 192))) +
      bv% ((ls_str% "malformed file") % 4096) =
      b + bv% (ls_str% "malformed file") := by
  subst hfn
  bv_arith

theorem adrp_bundle_err {b fnBase : BitVec 64}
    (hb : (b &&& 4095#64) = 0#64)
    (hfn : fnBase = b + bv% (ls_off% "libsignal_cli::public::split_id")) :
    (((fnBase + 200#64) &&& bv% (2 ^ 64 - 4096)) +
      bv% (page% (ls_str% "bundle") -
        page% (ls_off% "libsignal_cli::public::split_id" + 200))) +
      bv% ((ls_str% "bundle") % 4096) =
      b + bv% (ls_str% "bundle") := by
  subst hfn
  bv_arith

/-! ## 14-Byte Copy Realignment and `splitIdResultAt` Helpers -/

theorem buf14_open_lo (buf : BitVec 64) :
    memRegion buf 14 =
      (∃∗ w0 : BitVec 64, buf ↦₆₄ w0) ∗ memRegion (buf + 8#64) 6 := by
  rw [memRegion_uncons (n := 14) buf (by decide) (by decide), sepExists_sepConj_left]

theorem buf14_realign (buf : BitVec 64) :
    ((buf ↦₆₄ malfLo) ∗ memRegion (buf + 8#64) 6) ⊢
      (buf ↦ₛ malfHead6) ∗ (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) := by
  have heq : unpack64 malfLo = malfHead6 ++ unpack16 malfMid2 := by decide +kernel
  have hlen : malfHead6.length = 6 := by decide +kernel
  have h8 : buf + 6#64 + 2#64 = buf + 8#64 := by bv_omega
  have h64 : (buf ↦₆₄ malfLo) = (buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₁₆ malfMid2) := by
    rw [pointsTo64_eq_pointsToBytes, heq, pointsToBytes_append, hlen,
      ← pointsTo16_eq_pointsToBytes]
  have htail : (((buf + 6#64) ↦₁₆ malfMid2) ∗ memRegion (buf + 8#64) 6) ⊢
      (∃∗ w1 : BitVec 64, (buf + 6#64) ↦₆₄ w1) := by
    rw [← ProofLib.memRegion_eight (buf + 6#64),
      memRegion_split (buf + 6#64) 2 6 (by decide), h8]
    exact sepConj_mono_left (pointsTo16_entails_memRegion (buf + 6#64) malfMid2)
  rw [h64, sepConj_assoc]
  exact sepConj_mono_right htail

theorem buf14_close (buf : BitVec 64) :
    ((buf ↦ₛ malfHead6) ∗ ((buf + 6#64) ↦₆₄ malfHi)) =
      (buf ↦ₛ utf8 "malformed file") := by
  have heq : utf8 "malformed file" = malfHead6 ++ unpack64 malfHi := by decide +kernel
  have hlen : malfHead6.length = 6 := by decide +kernel
  rw [heq, pointsToBytes_append, hlen, ← pointsTo64_eq_pointsToBytes]

theorem speWord1_eq : (9223372036854775809#64 : BitVec 64) = speWord 1 := by
  decide

theorem splitOkTag_eq : (BitVec.ofNat 64 (2 ^ 64 - 2)) = splitOkTag := by
  decide

theorem speAt_invalidState_intro (A : RustAlloc) (img : Obj.Image) (dst buf : BitVec 64)
    (hbuf : buf ≠ 0#64) :
    ((dst ↦₆₄ speWord 1) ∗
      ((dst + 8#64) ↦₆₄ 14#64) ∗
      ((dst + 16#64) ↦₆₄ buf) ∗
      ((dst + 24#64) ↦₆₄ 14#64) ∗
      A.live buf 14 1 ∗
      (buf ↦ₛ utf8 "malformed file") ∗
      ((dst + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
      ((dst + 40#64) ↦₆₄ 6#64) ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle")) ⊢
      speAt A (utf8 "bundle") dst .invalidState := by
  have hlen_m : (utf8 "malformed file").length = 14 := by decide +kernel
  have hlen_b : (utf8 "bundle").length = 6 := by decide +kernel
  have hvec : (((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
      ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file")) ⊢
      (∃∗ bs : List (BitVec 8), vecU8 A (dst + 8#64) bs) := by
    refine Entails.sepExists_right (utf8 "malformed file") ?_
    unfold vecU8
    refine Entails.sepExists_right 14#64 (Entails.sepExists_right buf ?_)
    have h16 : dst + 8#64 + 8#64 = dst + 16#64 := by bv_omega
    have h24 : dst + 8#64 + 16#64 = dst + 24#64 := by bv_omega
    have hne : ((14#64 : BitVec 64) = 0) = False := eq_false (by decide)
    have h14 : (14#64 : BitVec 64).toNat = 14 := rfl
    simp only [vecU8At, vecHeader, hlen_m, hne, ↓reduceIte, h14, Nat.sub_self,
      memRegion_zero, sepConj_emp, h16, h24]
    rw [show (14 ≤ 14 ∧ 14 < 2 ^ 63 ∧ buf ≠ 0) = True from
      eq_true ⟨by decide, by decide, hbuf⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  have hstr : (((dst + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
      ((dst + 40#64) ↦₆₄ 6#64) ∗
      ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle")) ⊢
      strRefAt (dst + 32#64) (utf8 "bundle") := by
    unfold strRefAt
    refine Entails.sepExists_right (img.base + bv% (ls_str% "bundle")) ?_
    have h40 : dst + 32#64 + 8#64 = dst + 40#64 := by bv_omega
    rw [hlen_b, h40]
    exact Entails.of_eq (by ac_rfl)
  dsimp only [speAt]
  have hoff8 : asm64% spePayloadOff = 8#64 := rfl
  have hoff32 : asm64% speInvalidStateFnOff = 32#64 := rfl
  rw [hoff8, hoff32]
  have hgroup :
      ((dst ↦₆₄ speWord 1) ∗ ((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
        ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file") ∗
        ((dst + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
        ((dst + 40#64) ↦₆₄ 6#64) ∗
        ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle")) =
      ((dst ↦₆₄ speWord 1) ∗
        (((dst + 8#64) ↦₆₄ 14#64) ∗ ((dst + 16#64) ↦₆₄ buf) ∗
          ((dst + 24#64) ↦₆₄ 14#64) ∗ A.live buf 14 1 ∗ (buf ↦ₛ utf8 "malformed file")) ∗
        (((dst + 32#64) ↦₆₄ (img.base + bv% (ls_str% "bundle"))) ∗
          ((dst + 40#64) ↦₆₄ 6#64) ∗
          ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle"))) := by
    ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono hvec hstr)

/-! ## Return-Slot Layouts and 4-Byte Slice Splitting -/

theorem ret48_open_ok (r : BitVec 64) :
    memRegion r 48 =
      (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗
      (∃∗ w8 : BitVec 32, (r + 8#64) ↦₃₂ w8) ∗
      memRegion (r + 12#64) 4 ∗
      (∃∗ w16 : BitVec 64, (r + 16#64) ↦₆₄ w16) ∗
      (∃∗ w24 : BitVec 64, (r + 24#64) ↦₆₄ w24) ∗
      memRegion (r + 32#64) 16 := by
  have h1 : memRegion r 48 = (∃∗ w0 : BitVec 64, r ↦₆₄ w0) ∗ memRegion (r + 8#64) 40 := by
    rw [memRegion_uncons (n := 48) r (by decide) (by decide), sepExists_sepConj_left]
  have h2 : memRegion (r + 8#64) 40 =
      (∃∗ w8 : BitVec 32, (r + 8#64) ↦₃₂ w8) ∗ memRegion (r + 12#64) 4 ∗
        memRegion (r + 16#64) 32 := by
    have ha12 : r + 8#64 + 4#64 = r + 12#64 := by bv_omega
    have ha16 : r + 12#64 + 4#64 = r + 16#64 := by bv_omega
    rw [memRegion_split (r + 8#64) 4 36 (by decide), ha12,
      memRegion_split (r + 12#64) 4 32 (by decide), ha16,
      memRegion_four, ← sepConj_assoc]
  have h3 : memRegion (r + 16#64) 32 =
      (∃∗ w16 : BitVec 64, (r + 16#64) ↦₆₄ w16) ∗ memRegion (r + 24#64) 24 := by
    have ha24 : r + 16#64 + 8#64 = r + 24#64 := by bv_omega
    rw [memRegion_uncons (n := 32) (r + 16#64) (by decide) (by decide), ha24,
      sepExists_sepConj_left]
  have h4 : memRegion (r + 24#64) 24 =
      (∃∗ w24 : BitVec 64, (r + 24#64) ↦₆₄ w24) ∗ memRegion (r + 32#64) 16 := by
    have ha32 : r + 24#64 + 8#64 = r + 32#64 := by bv_omega
    rw [memRegion_uncons (n := 24) (r + 24#64) (by decide) (by decide), ha32,
      sepExists_sepConj_left]
  rw [h1, h2, h3, h4]

theorem unpack32_ofLe32 (b0 b1 b2 b3 : BitVec 8) :
    unpack32 (ofLe32 b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  simp only [unpack32, ofLe32, List.cons.injEq, and_true]
  exact ⟨by bv_bits, by bv_bits, by bv_bits, by bv_bits⟩

theorem bytesAt_cons4_false (fp : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    SpqrV1.ChainProofs.bytesAt false fp (b0 :: b1 :: b2 :: b3 :: rest) =
      ((fp ↦₃₂ ofLe32 b0 b1 b2 b3) ∗ SpqrV1.ChainProofs.bytesAt false (fp + 4#64) rest) := by
  simp only [SpqrV1.ChainProofs.bytesAt_false]
  have hlist : b0 :: b1 :: b2 :: b3 :: rest = [b0, b1, b2, b3] ++ rest := rfl
  rw [hlist, pointsToBytes_append, ← unpack32_ofLe32 b0 b1 b2 b3,
    ← pointsTo32_eq_pointsToBytes]
  rfl

theorem bytesAt_cons4_true (fp : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    SpqrV1.ChainProofs.bytesAt true fp (b0 :: b1 :: b2 :: b3 :: rest) =
      ((fp ↦₃₂ᵣ ofLe32 b0 b1 b2 b3) ∗ SpqrV1.ChainProofs.bytesAt true (fp + 4#64) rest) := by
  simp only [SpqrV1.ChainProofs.bytesAt_true]
  have hlist : b0 :: b1 :: b2 :: b3 :: rest = [b0, b1, b2, b3] ++ rest := rfl
  rw [hlist, pointsToBytesRO_append, ← unpack32_ofLe32 b0 b1 b2 b3,
    ← pointsTo32RO_eq_pointsToBytesRO]
  rfl

/-! ## Stack Bounds and 96-Byte Frame Decomposition -/

theorem stack_lt_addr_space {m : Memory} {ret sp : BitVec 64} {stk : Nat} {R : SepProp}
    (h : m ⊨ stackAt sp stk ∗ (memRegion ret 48 ∗ R))
    (hpos : 0 < stk) : stk < 2 ^ 64 := by
  have hd := IsBlock.disjoint (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk)
    (IsBlock.memRegion ret 48) hpos (by decide) h
  unfold DisjointRegions at hd
  have := (ret - (sp - BitVec.ofNat 64 stk)).isLt
  omega

def sidSavedRegs (sp0 : BitVec 64) (s0 : State) (v24 : BitVec 64) : SepProp :=
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 24#64) ↦₆₄ v24) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem sidSavedRegs_entails_cells6 (sp0 : BitVec 64) (s0 : State) (v24 : BitVec 64) :
    sidSavedRegs sp0 s0 v24 ⊢ cells (sp0 - 48#64) 6 := by
  unfold sidSavedRegs
  apply cells_sub_succ_entails 48 6
  apply cells_sub_succ_entails 40 5
  apply cells_sub_succ_entails 32 4
  apply cells_sub_succ_entails 24 3
  apply cells_sub_succ_entails 16 2
  rw [cells_sub_succ sp0 8 1 (by decide) (by decide), Nat.sub_self, cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right _ (Entails.refl _)

theorem stackAt_sid_split (sp0 : BitVec 64) (stk : Nat)
    (hstk : 96 + dropSpeStackX ≤ stk) (hlt : stk ≤ 2 ^ 64) :
    stackAt sp0 stk =
      memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      stackAt (sp0 - 96#64) dropSpeStackX ∗
      cells (sp0 - 96#64) 6 ∗
      cells (sp0 - 48#64) 6 := by
  have heq : stk = (dropSpeStackX + 96) + (stk - (dropSpeStackX + 96)) := by omega
  conv => lhs; rw [heq]
  rw [stackAt_split_bottom sp0 (dropSpeStackX + 96) (stk - (dropSpeStackX + 96)) (by omega)]
  rw [show dropSpeStackX + 96 = dropSpeStackX + 8 * 12 by omega,
    ProofLib.stackAt_split_cells sp0 dropSpeStackX 12 (by omega)]
  have h12 : cells (sp0 - 96#64) 12 = cells (sp0 - 96#64) 6 ∗ cells (sp0 - 48#64) 6 :=
    cells_split_sub sp0 96 48 6 6 (by decide)
  have hsub_n : dropSpeStackX + 8 * 12 + (stk - (dropSpeStackX + 8 * 12)) = stk := by omega
  rw [hsub_n, h12]

theorem stackAt_sid_pack_cells (sp0 : BitVec 64) (stk : Nat) (s0 : State) (v24 : BitVec 64)
    (hstk : 96 + dropSpeStackX ≤ stk) (hlt : stk ≤ 2 ^ 64) :
    (memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      stackAt (sp0 - 96#64) dropSpeStackX ∗
      cells (sp0 - 96#64) 6 ∗
      sidSavedRegs sp0 s0 v24) ⊢ stackAt sp0 stk := by
  rw [stackAt_sid_split sp0 stk hstk hlt]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sidSavedRegs_entails_cells6 sp0 s0 v24)))

theorem stackAt_sid_pack_region (sp0 : BitVec 64) (stk : Nat) (s0 : State) (v24 : BitVec 64)
    (hstk : 96 + dropSpeStackX ≤ stk) (hlt : stk ≤ 2 ^ 64) :
    (memRegion (sp0 - BitVec.ofNat 64 stk) (stk - (dropSpeStackX + 96)) ∗
      stackAt (sp0 - 96#64) dropSpeStackX ∗
      memRegion (sp0 - 96#64) 48 ∗
      sidSavedRegs sp0 s0 v24) ⊢ stackAt sp0 stk := by
  rw [ProofLib.memRegion_cells (sp0 - 96#64) 6 (by decide)]
  exact stackAt_sid_pack_cells sp0 stk s0 v24 hstk hlt

theorem stackAt_hook_split (sp1 : BitVec 64) :
    stackAt sp1 dropSpeStackX =
      memRegion (sp1 - BitVec.ofNat 64 dropSpeStackX) 32 ∗
      stackAt sp1 extHookStack := by
  have heq : dropSpeStackX = extHookStack + 32 := by
    unfold dropSpeStackX
    omega
  rw [heq, stackAt_split_bottom sp1 extHookStack 32 (by unfold extHookStack; decide)]

/-! ## `SepWPp` Call Helpers -/

def SidPanicAllow (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ∀ R, (sf.mem ⊨ P_f ∗ R) →
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R

theorem sidPanicAllow_of_eq {s0 sf : State} {P_f : SepProp}
    (h : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    SidPanicAllow s0 sf P_f :=
  fun _ hm => allowPanic_panicked h hm

theorem sid_call_inImage {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (spec.inImage img))
    (hinv : ImgCallInv img s)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False := by
      intro _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') →
      allocFailedIn s sf ∧ s.trace <+: sf.trace := by
      intro _ _ _ hp; exact (not_satisfies_false_sepConj hp).elim)
    (hnext : ∀ sf : State,
      ImgCallInv img sf →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (SidPanicAllow s0)) :
    SepWPp prog ret s P Q (SidPanicAllow s0) := by
  exact ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F)
    hcall hinv.1 hinv.2 hpc hrun hsp hlr
    (fun R hm => by
      have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
        Satisfies.mono (sepConj_mono_left hP) hm
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hinv, by simpa only [sepConj_assoc] using hm_pre⟩)
    hexit
    (fun sm hpan ⟨R', hpost⟩ => by
      dsimp only [Spec.inImage] at hpost ⊢
      have halloc := hpanic sm R' hpan hpost
      have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
        simpa [allocFailedIn, htr] using halloc
      exact sidPanicAllow_of_eq halloc0)
    (fun sm hpcm hrunm hspm hcsm hfz hsym =>
      hnext sm ⟨hfz, hsym⟩ hpcm hrunm hspm hcsm)
    (fun sm R' hoom_s hpost => (hoom sm (F ∗ R') hoom_s hpost).elim)

theorem sid_fnAddr_rel {b : BitVec 64} {ext : String → Option (State → State)}
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff splitIdName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (tripleRatchetProgAtExt b ext).fnAddr splitIdName + off =
      (tripleRatchetProgAtExt b ext).fnAddr target := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem sid_drop_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeSpecX A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName +
        bv% ((2 ^ 64 + ls_off% cliDropSpeName - ls_off% splitIdName) % 2 ^ 64))
      ((dropSpeSpecX A).inImage img) := by
  rw [sid_fnAddr_rel (target := cliDropSpeName)
    (by rw [splitId_fnOff, cliDropSpe_fnOff]; decide)]
  exact hDrop

theorem sid_shim_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% splitIdName))
      (session2ShimSpecX.inImage img) :=
  shim_ok_at2_ext_x hC (name := splitIdName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% splitIdName))
    (by rw [splitId_fnOff, ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"])

theorem sid_alloc_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% splitIdName))
      ((rustAllocSpecWithStack A extHookStack).inImage img) := by
  rw [sid_fnAddr_rel (target := "__rustc::__rust_alloc")
    (by rw [splitId_fnOff, ls_stub% "__rustc::__rust_alloc"]; decide)]
  exact hC.alloc

theorem sid_panic_handle_error (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr splitIdName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% splitIdName)) =
      some Rust.panicked :=
  panic_at_handle_error_norm_ext (b := img.base) (ext := ext) (name := splitIdName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% splitIdName))
    (by rw [splitId_fnOff, ls_stub% "alloc::raw_vec::handle_error"])

/-! ## `.rodata` Views, Alignment, and Callee-Saved State -/

def sidMalfRO (img : Obj.Image) : SepProp :=
  ((img.base + bv% (ls_str% "malformed file")) ↦₆₄ᵣ malfLo) ∗
  ((img.base + bv% (ls_str% "malformed file") + 8#64) ↦ᵣ malfTail6) ∗
  ((img.base + bv% (ls_str% "malformed file")) ↦ᵣ malfHead6) ∗
  ((img.base + bv% (ls_str% "malformed file") + 6#64) ↦₆₄ᵣ malfHi)

theorem sidMalfRO_bundle_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ sidMalfRO img ∗ ((img.base + bv% (ls_str% "bundle")) ↦ᵣ utf8 "bundle") ∗ P := by
  have h1 := rodata_bundle_intro himg hro hP
  have h2 := rodata_malformed_intro himg hro h1
  rw [pointsToBytesRO_malf_6_8] at h2
  have h3 := rodata_malformed_intro himg hro h2
  rw [pointsToBytesRO_malf_8_6] at h3
  unfold sidMalfRO
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h3

theorem ret48_open_err (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
        ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        (a ↦₆₄ u5) ∗ ((a + 8#64) ↦₆₄ u4) ∗ ((a + 16#64) ↦₆₄ u3) ∗
        ((a + 24#64) ↦₆₄ u2) ∗ ((a + 32#64) ↦₆₄ u1) ∗ ((a + 40#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 40 (by decide),
    memRegion_split (a + 8#64) 8 32 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem sp_sub_96_spAligned {s0 s : State} (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - 96#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp] at hal0 ⊢
  revert hal0
  generalize s0.sp = p
  bv_bits

def SidUpperSaved (s0 s : State) : Prop :=
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem SidUpperSaved.refl (s0 : State) : SidUpperSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SidUpperSaved.trans_calleeSaved {s0 s sf : State}
    (h1 : SidUpperSaved s0 s) (h2 : CalleeSavedPreserved s sf) :
    SidUpperSaved s0 sf :=
  ⟨h2.2.2.2.1.trans h1.1,
   h2.2.2.2.2.1.trans h1.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2⟩

end CryptoVerification.SignalSession.Cli.SplitId.Helpers
