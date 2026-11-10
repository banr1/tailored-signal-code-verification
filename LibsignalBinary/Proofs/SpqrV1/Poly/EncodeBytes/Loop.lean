/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`: Distribution Loop

**Checked by Lean.**

Proves `[Point; 16]` pinned-buffer splitting/updating helpers, the OOM panic block (`+824`), and the
chunk distribution loop (`+724..+668`), at fixed base and on Block `417`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.EncodeBytes

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## `pointPinAt` and `pointListPinAt` Splitting, Updating, and Byte-Slice Bridge -/

/-- Remaining buffer and allocator live token of a `Point` after splitting out the header and
    the next 2-byte element slot at `pin.ptr + 2 * pt.value.length`. -/
def pointPushRest (A : RustAlloc) (pin : VecPin) (pt : Point) (totalChunks : Nat) : SepProp :=
  ⌜pin.ptr ≠ 0⌝ ∗
    A.live pin.ptr (totalChunks * 2) 2 ∗
    arrayAt gf16At 2 pin.ptr pt.value ∗
    memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
      ((totalChunks - (pt.value.length + 1)) * 2)

theorem pointPinAt_open_push (A : RustAlloc) (pin : VecPin) (pt : Point) (slotA : BitVec 64)
    (totalChunks : Nat)
    (hcap : pin.cap = BitVec.ofNat 64 totalChunks)
    (hlt : pt.value.length < totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63) :
    pointPinAt A pin pt slotA ⊢
      ∃∗ d : BitVec 16,
        (slotA ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
        ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
        ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ d) ∗
        pointPushRest A pin pt totalChunks := by
  unfold pointPinAt pointAt vecAt vecHeader vecBuf gf16Stride gf16Align pointPushRest
  have hcap_nat : pin.cap.toNat = totalChunks := by
    rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : pin.cap ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [hcap_nat] at ht
    change totalChunks = 0 at ht
    omega
  rw [hcap_nat]
  simp only [hcap_ne, ↓reduceIte, ← hcap]
  have hrem_split : (totalChunks - pt.value.length) * 2 =
      2 + (totalChunks - (pt.value.length + 1)) * 2 := by omega
  have hmul_comm : pt.value.length * 2 = 2 * pt.value.length := by omega
  have haddr_next : pin.ptr + BitVec.ofNat 64 (2 * pt.value.length) + 2#64 =
      pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2) := by
    rw [BitVec.add_assoc]
    congr 1
    have h1 : (pt.value.length + 1) * 2 = 2 * pt.value.length + 2 := by omega
    rw [h1, BitVec.ofNat_add]
  rw [hmul_comm, hrem_split,
      ProofLib.memRegion_split (pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) 2
        ((totalChunks - (pt.value.length + 1)) * 2) (by omega),
      ProofLib.memRegion_two, haddr_next]
  rw [ show ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
        ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length)) ∗
        (⌜pt.value.length ≤ totalChunks ∧ totalChunks * 2 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (A.live pin.ptr (totalChunks * 2) 2 ∗ arrayAt gf16At 2 pin.ptr pt.value ∗
            ((∃∗ v : BitVec 16, (pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ v) ∗
              memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
                ((totalChunks - (pt.value.length + 1)) * 2)))) =
      ⌜pt.value.length ≤ totalChunks ∧ totalChunks * 2 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
        ((∃∗ v : BitVec 16, (pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ v) ∗
          ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
            ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
            A.live pin.ptr (totalChunks * 2) 2 ∗ arrayAt gf16At 2 pin.ptr pt.value ∗
            memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
              ((totalChunks - (pt.value.length + 1)) * 2))) by ac_rfl]
  apply Entails.pure_left; rintro ⟨_, _, hptr⟩
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro d
  refine Entails.sepExists_right d ?_
  rw [ show (slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
        ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ d) ∗
        (⌜pin.ptr ≠ 0⌝ ∗ A.live pin.ptr (totalChunks * 2) 2 ∗
          arrayAt gf16At 2 pin.ptr pt.value ∗
          memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
            ((totalChunks - (pt.value.length + 1)) * 2)) =
      ⌜pin.ptr ≠ 0⌝ ∗
        (((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ d) ∗
          ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
            ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
            A.live pin.ptr (totalChunks * 2) 2 ∗ arrayAt gf16At 2 pin.ptr pt.value ∗
            memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
              ((totalChunks - (pt.value.length + 1)) * 2))) by ac_rfl]
  exact Entails.pure_right hptr (Entails.refl _)

theorem gf16ArrayAt_append (base : BitVec 64) (xs ys : List GF16) :
    arrayAt gf16At 2 base (xs ++ ys) =
      arrayAt gf16At 2 base xs ∗
        arrayAt gf16At 2 (base + BitVec.ofNat 64 (2 * xs.length)) ys := by
  induction xs generalizing base with
  | nil =>
    simp [arrayAt]
  | cons x xs ih =>
    simp only [List.cons_append, arrayAt, List.length_cons]
    rw [ih (base + 2#64), sepConj_assoc]
    congr 2
    have hadd : (base + 2#64) + BitVec.ofNat 64 (2 * xs.length) =
        base + BitVec.ofNat 64 (2 * (xs.length + 1)) := by
      have h1 : 2 * (xs.length + 1) = 2 + 2 * xs.length := by omega
      rw [BitVec.add_assoc, h1, BitVec.ofNat_add]
    rw [hadd]

theorem pointPinAt_close_push (A : RustAlloc) (pin : VecPin) (pt : Point) (gf : GF16)
    (slotA : BitVec 64) (totalChunks : Nat)
    (hcap : pin.cap = BitVec.ofNat 64 totalChunks)
    (hlt : pt.value.length < totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63) :
    (slotA ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
      ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
      ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
      ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
      pointPushRest A pin pt totalChunks ⊢
      pointPinAt A pin { value := pt.value ++ [gf] } slotA := by
  unfold pointPinAt pointAt vecAt vecHeader vecBuf gf16Stride gf16Align pointPushRest
  have hcap_nat : pin.cap.toNat = totalChunks := by
    rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : pin.cap ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [hcap_nat] at ht
    change totalChunks = 0 at ht
    omega
  have hlen_app : (pt.value ++ [gf]).length = pt.value.length + 1 := by simp
  have harr_app :
      arrayAt gf16At 2 pin.ptr (pt.value ++ [gf]) =
        arrayAt gf16At 2 pin.ptr pt.value ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) := by
    rw [gf16ArrayAt_append]
    simp only [arrayAt, gf16At, sepConj_emp]
  rw [hcap_nat, hlen_app, harr_app]
  simp only [hcap_ne, ↓reduceIte, ← hcap]
  rw [show (slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
        ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
        ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
        (⌜pin.ptr ≠ 0⌝ ∗ A.live pin.ptr (totalChunks * 2) 2 ∗
          arrayAt gf16At 2 pin.ptr pt.value ∗
          memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
            ((totalChunks - (pt.value.length + 1)) * 2)) =
      ⌜pin.ptr ≠ 0⌝ ∗
        ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
          ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          A.live pin.ptr (totalChunks * 2) 2 ∗
          (arrayAt gf16At 2 pin.ptr pt.value ∗
            ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value)) ∗
          memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
            ((totalChunks - (pt.value.length + 1)) * 2)) by ac_rfl]
  rw [show ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
        ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1))) ∗
        (⌜pt.value.length + 1 ≤ totalChunks ∧ totalChunks * 2 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
          (A.live pin.ptr (totalChunks * 2) 2 ∗
            (arrayAt gf16At 2 pin.ptr pt.value ∗
              ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value)) ∗
            memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
              ((totalChunks - (pt.value.length + 1)) * 2))) =
      ⌜pt.value.length + 1 ≤ totalChunks ∧ totalChunks * 2 < 2 ^ 63 ∧ pin.ptr ≠ 0⌝ ∗
        ((slotA ↦₆₄ pin.cap) ∗ ((slotA + 8#64) ↦₆₄ pin.ptr) ∗
          ((slotA + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          A.live pin.ptr (totalChunks * 2) 2 ∗
          (arrayAt gf16At 2 pin.ptr pt.value ∗
            ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value)) ∗
          memRegion (pin.ptr + BitVec.ofNat 64 ((pt.value.length + 1) * 2))
            ((totalChunks - (pt.value.length + 1)) * 2)) by ac_rfl]
  apply Entails.pure_left; intro hptr
  exact Entails.pure_right ⟨by omega, hmax, hptr⟩ (Entails.refl _)

/-- 24-byte serialized header of a `Point` (`cap`, `ptr`, `len`). -/
def pointHeaderBytes (pin : VecPin) (pt : Point) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 pt.value.length)

/-- Concatenated 24-byte headers of a list of `Point`s. -/
def pointHeadersBytes : List VecPin → List Point → List (BitVec 8)
  | _, [] => []
  | [], _ :: _ => []
  | pin :: pins, pt :: pts => pointHeaderBytes pin pt ++ pointHeadersBytes pins pts

/-- Iterated separating conjunction of `pointBuf`s for a list of `Point`s. -/
def pointBufList (A : RustAlloc) : List VecPin → List Point → SepProp
  | _, [] => emp
  | [], _ :: _ => ⌜False⌝
  | pin :: pins, pt :: pts => pointBuf A pin.cap pin.ptr pt ∗ pointBufList A pins pts

@[simp] theorem length_unpack64 (w : BitVec 64) : (unpack64 w).length = 8 := rfl

@[simp] theorem length_pointHeaderBytes (pin : VecPin) (pt : Point) :
    (pointHeaderBytes pin pt).length = 24 := by
  simp [pointHeaderBytes]

theorem length_pointHeadersBytes (pins : List VecPin) (pts : List Point)
    (h : pins.length = pts.length) :
    (pointHeadersBytes pins pts).length = 24 * pts.length := by
  induction pts generalizing pins with
  | nil =>
    cases pins with
    | nil => rfl
    | cons _ _ => simp at h
  | cons pt pts ih =>
    cases pins with
    | nil => simp at h
    | cons pin pins =>
      have h' : pins.length = pts.length := by simpa using h
      simp only [pointHeadersBytes, List.length_append, length_pointHeaderBytes,
        ih pins h', List.length_cons]
      omega

theorem vecHeader_eq_pointsToBytes (v : BitVec 64) (pin : VecPin) (pt : Point) :
    vecHeader v pin.cap pin.ptr (BitVec.ofNat 64 pt.value.length) =
      (v ↦ₛ pointHeaderBytes pin pt) := by
  unfold vecHeader pointHeaderBytes
  have h16 : (v + 8#64) + 8#64 = v + 16#64 := by bv_omega
  rw [List.append_assoc, pointsToBytes_append, length_unpack64,
      pointsToBytes_append, length_unpack64, h16,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]

theorem pointListPinAt_eq_bytes_bufs (A : RustAlloc)
    (base : BitVec 64) (pins : List VecPin) (pts : List Point)
    (h : pins.length = pts.length) :
    pointListPinAt A base pins pts =
      (base ↦ₛ pointHeadersBytes pins pts) ∗ pointBufList A pins pts := by
  induction pts generalizing base pins with
  | nil =>
    cases pins with
    | nil => simp [pointListPinAt, pointHeadersBytes, pointBufList]
    | cons _ _ => simp at h
  | cons pt pts ih =>
    cases pins with
    | nil => simp at h
    | cons pin pins =>
      have h' : pins.length = pts.length := by simpa using h
      have ihb := ih (base + 24#64) pins h'
      simp only [pointListPinAt, pointHeadersBytes, pointBufList]
      unfold pointPinAt pointAt vecAt
      rw [vecHeader_eq_pointsToBytes, ihb]
      have h24 : (base ↦ₛ (pointHeaderBytes pin pt ++ pointHeadersBytes pins pts)) =
          (base ↦ₛ pointHeaderBytes pin pt) ∗ ((base + 24#64) ↦ₛ pointHeadersBytes pins pts) := by
        rw [pointsToBytes_append, length_pointHeaderBytes]
      rw [h24]
      ac_rfl

/-! ## OOM Panic Helper (`+824`, `0x338`) -/

abbrev encodeBytesOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- OOM panic block at `+0x338` (`+824..+832`: `mov w0, #2; mov x1, x21; bl handle_error`). -/
theorem encode_bytes_panic_824 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (contractProg b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := encodeBytesName)
    (k := ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"
      "alloc::raw_vec::handle_error")
  encode_bytes_fetches_range b (Rust.withPanics ext) 824 12
  dsimp only [contractProg, tripleRatchetProgAtExt, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP
    (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"
      "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [encodeBytesOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

/-! ## Distribution Loop (`+784 -> +668` and `+724 -> +668`) -/

/-- Two-instruction helper for `+784 -> +792` (`0x310 -> 0x318`: `and x8, x22, #0xf; ldrh w27, [x20]`),
    abstracting over `msgRO` (`true` for read-only `↦ᵣ`, `false` for read-write `↦ₛ`). -/
theorem encode_bytes_dist_load_chunk {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64) (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat) (hi : i < 2 ^ 64)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 792#64) s
      (bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (i % 16) ∧
        sm.readReg64 .x27 = (c1 ++ c0).zeroExtend 64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 i ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  encode_bytes_fetches_range b (Rust.withPanics ext) 784 8
  dsimp only [contractProg, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
  examples_hide_fetches
  cases msgRO
  · rw [bytesAt_pair_rw]
    wp_steps
    rw [bv_and_15_eq_mod_16 i hi]
    wp_done
  · rw [bytesAt_pair_ro]
    wp_steps
    rw [bv_and_15_eq_mod_16 i hi]
    wp_done

/-- Single iteration of the distribution loop (`+784 -> +668` when `i + 1 = totalChunks`, or
    `+784 -> +784` when `i + 1 < totalChunks`). -/
theorem encode_bytes_dist_step {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat)
    (hilt : i < totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext)
      (if i + 1 = totalChunks then
        (contractProg b ext).fnAddr encodeBytesName + 668#64
       else
        (contractProg b ext).fnAddr encodeBytesName + 784#64)
      s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i [c0, c1] pts) ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr + 2#64 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hi_lt : i < 2 ^ 64 := by omega
  have htot_lt : totalChunks < 2 ^ 64 := by omega
  have hpoly_lt16 : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < pts.length := by rw [hpts_len]; exact hpoly_lt16
  have hpoly_pins : i % 16 < pins.length := by rw [hpins_len]; exact hpoly_lt16
  have hlen_eq : pins.length = pts.length := by rw [hpins_len, hpts_len]
  let pin := pins[i % 16]'hpoly_pins
  let pt := pts[i % 16]'hpoly_pts
  let gf := GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
  have hdist_one : distributeMsgChunksTotal i [c0, c1] pts =
      pts.set (i % 16) { value := pt.value ++ [gf] } := by
    have hpt_some : pts[i % 16]? = some pt :=
      List.getElem?_eq_some_iff.mpr ⟨hpoly_pts, rfl⟩
    simp [distributeMsgChunksTotal, hpt_some, gf]
  have hpin_cap : pin.cap = BitVec.ofNat 64 totalChunks :=
    hpins_cap pin (List.getElem_mem hpoly_pins)
  have hpt_le_i : pt.value.length ≤ i :=
    hpts_bound pt (List.getElem_mem hpoly_pts)
  have hpt_lt_tot : pt.value.length < totalChunks := by omega
  let FrameSlots :=
    pointListPinAt A (fsp + 72#64) (pins.take (i % 16)) (pts.take (i % 16)) ∗
      pointListPinAt A ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16 + 1)))
        (pins.drop (i % 16 + 1)) (pts.drop (i % 16 + 1))
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encodeBytesName + 792#64)
    (P_mid := bytesAt msgRO msgPtr [c0, c1] ∗ (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = BitVec.ofNat 64 (i % 16) ∧
      sm.readReg64 .x27 = (c1 ++ c0).zeroExtend 64 ∧
      sm.readReg64 .x19 = s0.readReg64 .x8 ∧
      sm.readReg64 .x20 = msgPtr ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 i ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
      sm.readReg64 .x24 = 24#64 ∧
      sm.readReg64 .x25 = fsp + 72#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [show pointListPinAt A (fsp + 72#64) pins pts ∗ bytesAt msgRO msgPtr [c0, c1] ∗ Frame =
          bytesAt msgRO msgPtr [c0, c1] ∗ (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame) by ac_rfl]
    exact encode_bytes_dist_load_chunk s0 s fsp msgPtr msgRO c0 c1 i totalChunks hi_lt
      (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame)
      hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
  · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx27_1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
    encode_bytes_fetches_range b (Rust.withPanics ext) 748 36
    encode_bytes_fetches_range b (Rust.withPanics ext) 792 20
    dsimp only [contractProg, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
    examples_hide_fetches
    rw [pointListPinAt_split_at A (fsp + 72#64) pins pts (i % 16) hlen_eq hpoly_pts]
    have hopen :
        bytesAt msgRO msgPtr [c0, c1] ∗
          ((pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗ Frame) ⊢
        ∃∗ d : BitVec 16,
          (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ d) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) := by
      rw [show bytesAt msgRO msgPtr [c0, c1] ∗ ((pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗ Frame) =
            pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ (FrameSlots ∗ bytesAt msgRO msgPtr [c0, c1] ∗ Frame) by ac_rfl]
      refine Entails.trans (sepConj_mono_left (pointPinAt_open_push A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) totalChunks hpin_cap hpt_lt_tot hmax)) ?_
      rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d
      refine Entails.sepExists_right d ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hopen ?_
    apply SepWP.exists_left; intro d16
    have hbne : (BitVec.ofNat 64 pt.value.length != BitVec.ofNat 64 totalChunks) = true :=
      bne_cap_of_lt hpt_lt_tot htot_lt
    have hclose :
        (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i [c0, c1] pts) ∗
          bytesAt msgRO msgPtr [c0, c1] ∗ Frame := by
      rw [hdist_one, ← pointListPinAt_set_eq A (fsp + 72#64) pins pts (i % 16) { value := pt.value ++ [gf] } hlen_eq hpoly_pts]
      change (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        (pointPinAt A pin { value := pt.value ++ [gf] } ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗
          bytesAt msgRO msgPtr [c0, c1] ∗ Frame
      rw [sepConj_assoc (pointPinAt A pin { value := pt.value ++ [gf] } ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))))]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_left (pointPinAt_close_push A pin pt gf ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) totalChunks hpin_cap hpt_lt_tot hmax))
    dsimp only [gf] at hclose
    by_cases hdone : i + 1 = totalChunks
    · have hbeq : (BitVec.ofNat 64 totalChunks == BitVec.ofNat 64 (i + 1)) = true := by
        rw [hdone]; exact beq_total_of_eq
      simp only [hdone, ↓reduceIte]
      wp_steps
      refine align_pre hclose ?_
      wp_done
    · have hlt_next : i + 1 < totalChunks := by omega
      have hbeq : (BitVec.ofNat 64 totalChunks == BitVec.ofNat 64 (i + 1)) = false :=
        beq_total_false_of_lt hlt_next htot_lt
      simp only [hdone, ↓reduceIte]
      wp_steps
      refine align_pre hclose ?_
      wp_done

theorem totalChunks_bv_eq_nat (n : Nat) (heven : n % 2 = 0) (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n - 2#64) >>> 1) + 1#64 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hge2 : 2 ≤ n := by omega
  have hsub : (BitVec.ofNat 64 n - 2#64).toNat = n - 2 := by
    rw [BitVec.toNat_sub_of_le]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · rw [BitVec.le_def]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      exact hge2
  have hlsr : ((BitVec.ofNat 64 n - 2#64) >>> 1).toNat = (n - 2) / 2 := by
    rw [BitVec.toNat_ushiftRight, hsub, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_add, hlsr, BitVec.toNat_ofNat]
  change ((n - 2) / 2 + 1) % 2 ^ 64 = (n / 2) % 2 ^ 64
  omega

theorem totalChunks_bv_eq (n : Nat) (heven : n % 2 = 0) (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n - 2#64) >>> 1#64) + 1#64 = BitVec.ofNat 64 (n / 2) :=
  totalChunks_bv_eq_nat n heven hpos hlt

/-- Full distribution loop (`+784 -> +668`, `0x310 -> 0x29c`) over a non-empty even-length
    byte slice `msg` starting at chunk index `i` (`i + msg.length / 2 = totalChunks`). -/
theorem encode_bytes_dist_loop {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (i totalChunks : Nat)
    (hrem_even : msg.length % 2 = 0)
    (hrem_pos : 0 < msg.length)
    (hi_rem : i + msg.length / 2 = totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  match msg with
  | [] => simp at hrem_pos
  | [_] => simp at hrem_even
  | [c0, c1] =>
    have hdone : i + 1 = totalChunks := by simp at hi_rem; omega
    have hilt : i < totalChunks := by omega
    have hstep := encode_bytes_dist_step (A := A) s0 s fsp msgPtr hfsp_align msgRO c0 c1 i totalChunks
      hilt hmax pins pts hpins_len hpts_len hpins_cap hpts_bound Frame
      hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
    simp only [hdone, ↓reduceIte] at hstep
    exact SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hsp', hx19', _, _, _, _, _, htr', hvr'⟩ =>
      ⟨hPm, hsp', hx19', htr', hvr'⟩
  | c0 :: c1 :: d0 :: rest =>
    have hrest_even : (d0 :: rest).length % 2 = 0 := by
      simp only [List.length_cons] at hrem_even ⊢; omega
    have hrest_pos : 0 < (d0 :: rest).length := by simp
    have hi_next : (i + 1) + (d0 :: rest).length / 2 = totalChunks := by
      simp only [List.length_cons] at hi_rem ⊢; omega
    have hilt : i < totalChunks := by omega
    have hnot_done : ¬(i + 1 = totalChunks) := by
      simp only [List.length_cons] at hi_rem hrem_even; omega
    let pts' := distributeMsgChunksTotal i [c0, c1] pts
    have hev2 : ([c0, c1] : List (BitVec 8)).length % 2 = 0 := by simp
    have hpts'_len : pts'.length = 16 :=
      (distributeMsgChunks_eq_ok [c0, c1] i pts hev2 hpts_len).2
    have hpts'_bound : ∀ pt ∈ pts', pt.value.length ≤ i + 1 := by
      simpa using distributeMsgChunksTotal_value_length_le [c0, c1] i pts hev2 hpts_len hpts_bound
    refine seq_clean
      (mid := (contractProg b ext).fnAddr encodeBytesName + 784#64)
      (P_mid := pointListPinAt A (fsp + 72#64) pins pts' ∗
        bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ (bytesAt msgRO msgPtr [c0, c1] ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr + 2#64 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rw [bytesAt_cons_cons msgRO msgPtr c0 c1 (d0 :: rest)]
      rw [show pointListPinAt A (fsp + 72#64) pins pts ∗
            (bytesAt msgRO msgPtr [c0, c1] ∗ bytesAt msgRO (msgPtr + 2#64) (d0 :: rest)) ∗ Frame =
          pointListPinAt A (fsp + 72#64) pins pts ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ (bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ Frame) by ac_rfl]
      have hstep := encode_bytes_dist_step (A := A) s0 s fsp msgPtr hfsp_align msgRO c0 c1 i totalChunks
        hilt hmax pins pts hpins_len hpts_len hpins_cap hpts_bound
        (bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ Frame)
        hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
      simp only [hnot_done, ↓reduceIte] at hstep
      refine SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hQ⟩ => ⟨?_, hQ⟩
      refine Entails.trans hPm ?_
      exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
      have ih := encode_bytes_dist_loop (A := A) (d0 :: rest) s0 s1 fsp (msgPtr + 2#64) hfsp_align msgRO
        (i + 1) totalChunks hrest_even hrest_pos hi_next hmax pins pts'
        hpins_len hpts'_len hpins_cap hpts'_bound
        (bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htrace1 hvregs1
      refine SepWP.mono ih fun sm Pm _ _ ⟨hPm, hQ⟩ => ⟨?_, hQ⟩
      refine Entails.trans hPm ?_
      rw [bytesAt_cons_cons msgRO msgPtr c0 c1 (d0 :: rest)]
      change pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal (i + 1) (d0 :: rest) pts') ∗
          bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ (bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal (i + 1) (d0 :: rest) pts') ∗
          (bytesAt msgRO msgPtr [c0, c1] ∗ bytesAt msgRO (msgPtr + 2#64) (d0 :: rest)) ∗ Frame
      exact Entails.of_eq (by ac_rfl)

/-- Distribution loop header + body (`+724 -> +668`, `0x2d4 -> 0x29c`). -/
theorem encode_bytes_dist_entry {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (heven : msg.length % 2 = 0)
    (hpos : 0 < msg.length)
    (hmax : msg.length < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 (msg.length / 2))
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0)
    (Frame : SepProp)
    (hpc : s.pc = (contractProg b ext).fnAddr encodeBytesName + 724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 msg.length - 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr encodeBytesName + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal 0 msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hlt64 : msg.length < 2 ^ 64 := by omega
  have htot_bv : ((BitVec.ofNat 64 msg.length - 2#64) >>> 1#64) + 1#64 = BitVec.ofNat 64 (msg.length / 2) :=
    totalChunks_bv_eq msg.length heven hpos hlt64
  have htot_bv_nat : ((BitVec.ofNat 64 msg.length - 2#64) >>> 1) + 1#64 = BitVec.ofNat 64 (msg.length / 2) :=
    totalChunks_bv_eq_nat msg.length heven hpos hlt64
  refine seq_clean
    (mid := (contractProg b ext).fnAddr encodeBytesName + 784#64)
    (P_mid := pointListPinAt A (fsp + 72#64) pins pts ∗ bytesAt msgRO msgPtr msg ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = s0.readReg64 .x8 ∧
      sm.readReg64 .x20 = msgPtr ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 0 ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 (msg.length / 2) ∧
      sm.readReg64 .x24 = 24#64 ∧
      sm.readReg64 .x25 = fsp + 72#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · encode_bytes_fetches_range b (Rust.withPanics ext) 724 24
    dsimp only [contractProg, encodeBytesName, BitVec.ofNat_eq_ofNat] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr
      "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
      ⟨Entails.refl _, by simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx8, htrace, hvregs, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, htot_bv, htot_bv_nat, and_self]⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
    exact encode_bytes_dist_loop msg s0 s1 fsp msgPtr hfsp_align msgRO
      0 (msg.length / 2) heven hpos (by omega) (by omega)
      pins pts hpins_len hpts_len hpins_cap hpts_bound Frame
      hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htrace1 hvregs1

/-! ## Relocatable `[LibsignalPlacement]` Distribution Loop (Block `417`) -/

open CryptoVerification.SpqrV1.Alloc

theorem encode_bytes_panic_824_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_417).base + 824#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeBytesOnPanic s0 sf ∗ R)) := by
  have hpan_err :
      ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext)).externAt?
        (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by rfl) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simpa only [wp_norm] using hpan_err) fun hm => ?_
  simpa only [encodeBytesOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

theorem encode_bytes_dist_load_chunk_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64) (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat) (hi : i < 2 ^ 64)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 792#64) s
      (bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = BitVec.ofNat 64 (i % 16) ∧
        sm.readReg64 .x27 = (c1 ++ c0).zeroExtend 64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 i ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  cases msgRO
  · rw [bytesAt_pair_rw]
    wp_steps
    rw [bv_and_15_eq_mod_16 i hi]
    wp_done
  · rw [bytesAt_pair_ro]
    wp_steps
    rw [bv_and_15_eq_mod_16 i hi]
    wp_done

theorem encode_bytes_dist_step_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool) (c0 c1 : BitVec 8)
    (i totalChunks : Nat)
    (hilt : i < totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (if i + 1 = totalChunks then
        (blkPl_417).base + 668#64
       else
        (blkPl_417).base + 784#64)
      s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i [c0, c1] pts) ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr + 2#64 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hi_lt : i < 2 ^ 64 := by omega
  have htot_lt : totalChunks < 2 ^ 64 := by omega
  have hpoly_lt16 : i % 16 < 16 := Nat.mod_lt i (by decide)
  have hpoly_pts : i % 16 < pts.length := by rw [hpts_len]; exact hpoly_lt16
  have hpoly_pins : i % 16 < pins.length := by rw [hpins_len]; exact hpoly_lt16
  have hlen_eq : pins.length = pts.length := by rw [hpins_len, hpts_len]
  let pin := pins[i % 16]'hpoly_pins
  let pt := pts[i % 16]'hpoly_pts
  let gf := GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
  have hdist_one : distributeMsgChunksTotal i [c0, c1] pts =
      pts.set (i % 16) { value := pt.value ++ [gf] } := by
    have hpt_some : pts[i % 16]? = some pt :=
      List.getElem?_eq_some_iff.mpr ⟨hpoly_pts, rfl⟩
    simp [distributeMsgChunksTotal, hpt_some, gf]
  have hpin_cap : pin.cap = BitVec.ofNat 64 totalChunks :=
    hpins_cap pin (List.getElem_mem hpoly_pins)
  have hpt_le_i : pt.value.length ≤ i :=
    hpts_bound pt (List.getElem_mem hpoly_pts)
  have hpt_lt_tot : pt.value.length < totalChunks := by omega
  let FrameSlots :=
    pointListPinAt A (fsp + 72#64) (pins.take (i % 16)) (pts.take (i % 16)) ∗
      pointListPinAt A ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16 + 1)))
        (pins.drop (i % 16 + 1)) (pts.drop (i % 16 + 1))
  refine seq_clean
    (mid := (blkPl_417).base + 792#64)
    (P_mid := bytesAt msgRO msgPtr [c0, c1] ∗ (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = BitVec.ofNat 64 (i % 16) ∧
      sm.readReg64 .x27 = (c1 ++ c0).zeroExtend 64 ∧
      sm.readReg64 .x19 = s0.readReg64 .x8 ∧
      sm.readReg64 .x20 = msgPtr ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 i ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
      sm.readReg64 .x24 = 24#64 ∧
      sm.readReg64 .x25 = fsp + 72#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · rw [show pointListPinAt A (fsp + 72#64) pins pts ∗ bytesAt msgRO msgPtr [c0, c1] ∗ Frame =
          bytesAt msgRO msgPtr [c0, c1] ∗ (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame) by ac_rfl]
    exact encode_bytes_dist_load_chunk_placed s0 s fsp msgPtr msgRO c0 c1 i totalChunks hi_lt
      (pointListPinAt A (fsp + 72#64) pins pts ∗ Frame)
      hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
  · intro s1 hpc1 hrun1 ⟨hsp1, hx8_1, hx27_1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
    rw [pointListPinAt_split_at A (fsp + 72#64) pins pts (i % 16) hlen_eq hpoly_pts]
    have hopen :
        bytesAt msgRO msgPtr [c0, c1] ∗
          ((pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗ Frame) ⊢
        ∃∗ d : BitVec 16,
          (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ d) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) := by
      rw [show bytesAt msgRO msgPtr [c0, c1] ∗ ((pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗ Frame) =
            pointPinAt A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ (FrameSlots ∗ bytesAt msgRO msgPtr [c0, c1] ∗ Frame) by ac_rfl]
      refine Entails.trans (sepConj_mono_left (pointPinAt_open_push A pin pt ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) totalChunks hpin_cap hpt_lt_tot hmax)) ?_
      rw [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro d
      refine Entails.sepExists_right d ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.weaken_pre hopen ?_
    apply SepWP.exists_left; intro d16
    have hbne : (BitVec.ofNat 64 pt.value.length != BitVec.ofNat 64 totalChunks) = true :=
      bne_cap_of_lt hpt_lt_tot htot_lt
    have hclose :
        (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i [c0, c1] pts) ∗
          bytesAt msgRO msgPtr [c0, c1] ∗ Frame := by
      rw [hdist_one, ← pointListPinAt_set_eq A (fsp + 72#64) pins pts (i % 16) { value := pt.value ++ [gf] } hlen_eq hpoly_pts]
      change (((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ↦₆₄ BitVec.ofNat 64 totalChunks) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 8#64) ↦₆₄ pin.ptr) ∗
          ((((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) + 16#64) ↦₆₄ BitVec.ofNat 64 (pt.value.length + 1)) ∗
          ((pin.ptr + BitVec.ofNat 64 (2 * pt.value.length)) ↦₁₆ gf.value) ∗
          (pointPushRest A pin pt totalChunks ∗ FrameSlots ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        (pointPinAt A pin { value := pt.value ++ [gf] } ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) ∗ FrameSlots) ∗
          bytesAt msgRO msgPtr [c0, c1] ∗ Frame
      rw [sepConj_assoc (pointPinAt A pin { value := pt.value ++ [gf] } ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))))]
      exact Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_left (pointPinAt_close_push A pin pt gf ((fsp + 72#64) + BitVec.ofNat 64 (24 * (i % 16))) totalChunks hpin_cap hpt_lt_tot hmax))
    dsimp only [gf] at hclose
    by_cases hdone : i + 1 = totalChunks
    · have hbeq : (BitVec.ofNat 64 totalChunks == BitVec.ofNat 64 (i + 1)) = true := by
        rw [hdone]; exact beq_total_of_eq
      simp only [hdone, ↓reduceIte]
      wp_steps
      refine align_pre hclose ?_
      wp_done
    · have hlt_next : i + 1 < totalChunks := by omega
      have hbeq : (BitVec.ofNat 64 totalChunks == BitVec.ofNat 64 (i + 1)) = false :=
        beq_total_false_of_lt hlt_next htot_lt
      simp only [hdone, ↓reduceIte]
      wp_steps
      refine align_pre hclose ?_
      wp_done

theorem encode_bytes_dist_loop_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (i totalChunks : Nat)
    (hrem_even : msg.length % 2 = 0)
    (hrem_pos : 0 < msg.length)
    (hi_rem : i + msg.length / 2 = totalChunks)
    (hmax : totalChunks * 2 < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 totalChunks)
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ i)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 784#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 i)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalChunks)
    (hx24 : s.readReg64 .x24 = 24#64)
    (hx25 : s.readReg64 .x25 = fsp + 72#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal i msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  match msg with
  | [] => simp at hrem_pos
  | [_] => simp at hrem_even
  | [c0, c1] =>
    have hdone : i + 1 = totalChunks := by simp at hi_rem; omega
    have hilt : i < totalChunks := by omega
    have hstep := encode_bytes_dist_step_placed (A := A) (ext := ext) s0 s fsp msgPtr hfsp_align msgRO c0 c1 i totalChunks
      hilt hmax pins pts hpins_len hpts_len hpins_cap hpts_bound Frame
      hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
    simp only [hdone, ↓reduceIte] at hstep
    exact SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hsp', hx19', _, _, _, _, _, htr', hvr'⟩ =>
      ⟨hPm, hsp', hx19', htr', hvr'⟩
  | c0 :: c1 :: d0 :: rest =>
    have hrest_even : (d0 :: rest).length % 2 = 0 := by
      simp only [List.length_cons] at hrem_even ⊢; omega
    have hrest_pos : 0 < (d0 :: rest).length := by simp
    have hi_next : (i + 1) + (d0 :: rest).length / 2 = totalChunks := by
      simp only [List.length_cons] at hi_rem ⊢; omega
    have hilt : i < totalChunks := by omega
    have hnot_done : ¬(i + 1 = totalChunks) := by
      simp only [List.length_cons] at hi_rem hrem_even; omega
    let pts' := distributeMsgChunksTotal i [c0, c1] pts
    have hev2 : ([c0, c1] : List (BitVec 8)).length % 2 = 0 := by simp
    have hpts'_len : pts'.length = 16 :=
      (distributeMsgChunks_eq_ok [c0, c1] i pts hev2 hpts_len).2
    have hpts'_bound : ∀ pt ∈ pts', pt.value.length ≤ i + 1 := by
      simpa using distributeMsgChunksTotal_value_length_le [c0, c1] i pts hev2 hpts_len hpts_bound
    refine seq_clean
      (mid := (blkPl_417).base + 784#64)
      (P_mid := pointListPinAt A (fsp + 72#64) pins pts' ∗
        bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ (bytesAt msgRO msgPtr [c0, c1] ∗ Frame))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.readReg64 .x20 = msgPtr + 2#64 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (i + 1) ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 totalChunks ∧
        sm.readReg64 .x24 = 24#64 ∧
        sm.readReg64 .x25 = fsp + 72#64 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · rw [bytesAt_cons_cons msgRO msgPtr c0 c1 (d0 :: rest)]
      rw [show pointListPinAt A (fsp + 72#64) pins pts ∗
            (bytesAt msgRO msgPtr [c0, c1] ∗ bytesAt msgRO (msgPtr + 2#64) (d0 :: rest)) ∗ Frame =
          pointListPinAt A (fsp + 72#64) pins pts ∗
            bytesAt msgRO msgPtr [c0, c1] ∗ (bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ Frame) by ac_rfl]
      have hstep := encode_bytes_dist_step_placed (A := A) (ext := ext) s0 s fsp msgPtr hfsp_align msgRO c0 c1 i totalChunks
        hilt hmax pins pts hpins_len hpts_len hpins_cap hpts_bound
        (bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ Frame)
        hpc hrun hsp hx19 hx20 hx22 hx23 hx24 hx25 htrace hvregs
      simp only [hnot_done, ↓reduceIte] at hstep
      refine SepWP.mono hstep fun sm Pm _ _ ⟨hPm, hQ⟩ => ⟨?_, hQ⟩
      refine Entails.trans hPm ?_
      exact Entails.of_eq (by ac_rfl)
    · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
      have ih := encode_bytes_dist_loop_placed (A := A) (ext := ext) (d0 :: rest) s0 s1 fsp (msgPtr + 2#64) hfsp_align msgRO
        (i + 1) totalChunks hrest_even hrest_pos hi_next hmax pins pts'
        hpins_len hpts'_len hpins_cap hpts'_bound
        (bytesAt msgRO msgPtr [c0, c1] ∗ Frame)
        hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htrace1 hvregs1
      refine SepWP.mono ih fun sm Pm _ _ ⟨hPm, hQ⟩ => ⟨?_, hQ⟩
      refine Entails.trans hPm ?_
      rw [bytesAt_cons_cons msgRO msgPtr c0 c1 (d0 :: rest)]
      change pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal (i + 1) (d0 :: rest) pts') ∗
          bytesAt msgRO (msgPtr + 2#64) (d0 :: rest) ∗ (bytesAt msgRO msgPtr [c0, c1] ∗ Frame) ⊢
        pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal (i + 1) (d0 :: rest) pts') ∗
          (bytesAt msgRO msgPtr [c0, c1] ∗ bytesAt msgRO (msgPtr + 2#64) (d0 :: rest)) ∗ Frame
      exact Entails.of_eq (by ac_rfl)

theorem encode_bytes_dist_entry_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (msg : List (BitVec 8))
    (s0 s : State) (fsp msgPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgRO : Bool)
    (heven : msg.length % 2 = 0)
    (hpos : 0 < msg.length)
    (hmax : msg.length < 2 ^ 63)
    (pins : List VecPin) (pts : List Point)
    (hpins_len : pins.length = 16)
    (hpts_len : pts.length = 16)
    (hpins_cap : ∀ pin ∈ pins, pin.cap = BitVec.ofNat 64 (msg.length / 2))
    (hpts_bound : ∀ pt ∈ pts, pt.value.length ≤ 0)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 msg.length - 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x8)
    (hx20 : s.readReg64 .x20 = msgPtr)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s
      (pointListPinAt A (fsp + 72#64) pins pts ∗
        bytesAt msgRO msgPtr msg ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          pointListPinAt A (fsp + 72#64) pins (distributeMsgChunksTotal 0 msg pts) ∗
            bytesAt msgRO msgPtr msg ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = s0.readReg64 .x8 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hlt64 : msg.length < 2 ^ 64 := by omega
  have htot_bv : ((BitVec.ofNat 64 msg.length - 2#64) >>> 1#64) + 1#64 = BitVec.ofNat 64 (msg.length / 2) :=
    totalChunks_bv_eq msg.length heven hpos hlt64
  have htot_bv_nat : ((BitVec.ofNat 64 msg.length - 2#64) >>> 1) + 1#64 = BitVec.ofNat 64 (msg.length / 2) :=
    totalChunks_bv_eq_nat msg.length heven hpos hlt64
  refine seq_clean
    (mid := (blkPl_417).base + 784#64)
    (P_mid := pointListPinAt A (fsp + 72#64) pins pts ∗ bytesAt msgRO msgPtr msg ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = s0.readReg64 .x8 ∧
      sm.readReg64 .x20 = msgPtr ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 0 ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 (msg.length / 2) ∧
      sm.readReg64 .x24 = 24#64 ∧
      sm.readReg64 .x25 = fsp + 72#64 ∧
      sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
      ⟨Entails.refl _, by simp only [wp_norm, arm64_norm, hsp, hx19, hx20, hx8, htrace, hvregs, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, htot_bv, htot_bv_nat, and_self]⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, htrace1, hvregs1⟩
    exact encode_bytes_dist_loop_placed (A := A) (ext := ext) msg s0 s1 fsp msgPtr hfsp_align msgRO
      0 (msg.length / 2) heven hpos (by omega) (by omega)
      pins pts hpins_len hpts_len hpins_cap hpts_bound Frame
      hpc1 hrun1 hsp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 htrace1 hvregs1

end CryptoVerification.SpqrV1.Poly.EncodeBytes

