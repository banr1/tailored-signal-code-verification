/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prog
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`: Definitions and Specifications

**Checked by Lean.**

Pure totality (`encodeBytesResult`) and AArch64 separation-logic specifications (`encodeBytesSpec`,
`encodeBytesSpecX`) for `<PolyEncoder as Encoder>::encode_bytes` (`0x6b6b8`, Block `417`).
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

/-! ## Symbol Name and Stack Budgets -/

abbrev encodeBytesName : String :=
  "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"

/-- Own stack frame of `encode_bytes` (`0x60 + 0x1d0 = 0x230 = 560` bytes) + `allocHookStack` (`4096` bytes). -/
abbrev encodeBytesStack : Nat := 560 + allocHookStack

/-- Own stack frame of `encode_bytes` (`560` bytes) + `extHookStack` (`16384` bytes). -/
abbrev encodeBytesStackX : Nat := 560 + extHookStack

/-! ## Read-Only / Read-Write Byte Slice Helper -/

/-- Byte slice permission at `p`: read-only (`p ↦ᵣ bs`) when `ro = true`, read-write (`p ↦ₛ bs`)
    when `ro = false`. -/
def bytesAt (ro : Bool) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if ro then p ↦ᵣ bs else p ↦ₛ bs

@[simp] theorem bytesAt_true (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt true p bs = (p ↦ᵣ bs) := rfl

@[simp] theorem bytesAt_false (p : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt false p bs = (p ↦ₛ bs) := rfl

/-! ## Pure Total Characterization of `PolyEncoder.encodeBytes` -/

/-- Total version of `PolyEncoder.distributeMsgChunks` for `pts.length = 16` and even-length `msg`. -/
def distributeMsgChunksTotal : Nat → List (BitVec 8) → List Point → List Point
  | _, [], pts => pts
  | _, [ _ ], pts => pts
  | i, c0 :: c1 :: rest, pts =>
    let poly := i % 16
    let pt := pts[poly]?.getD { value := [] }
    let gf := GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set poly { value := pt.value ++ [gf] }
    distributeMsgChunksTotal (i + 1) rest pts'

/-- Total pure result of `PolyEncoder.encodeBytes msg` (`PolyEncoder.encodeBytes` never panics). -/
def encodeBytesResult (msg : List (BitVec 8)) : Except EncodingError PolyEncoder :=
  if msg.length % 2 != 0 then
    .error (.polynomialError .messageLengthEven)
  else if msg.length > (1 <<< 16) * NUM_POLYS then
    .error (.polynomialError .messageLengthTooLong)
  else
    let initPts : List Point := List.replicate NUM_POLYS { value := [] }
    let pts := distributeMsgChunksTotal 0 msg initPts
    .ok { idx := 0#32, s := .points pts }

theorem distributeMsgChunks_eq_ok :
    ∀ (msg : List (BitVec 8)) (i : Nat) (pts : List Point),
      msg.length % 2 = 0 →
      pts.length = 16 →
      PolyEncoder.distributeMsgChunks i msg pts = .ok (distributeMsgChunksTotal i msg pts) ∧
        (distributeMsgChunksTotal i msg pts).length = 16
  | [], _, pts, _, hpts => by
    simp [PolyEncoder.distributeMsgChunks, distributeMsgChunksTotal, hpts]
  | [ _ ], _, _, hlen, _ => by
    simp at hlen
  | c0 :: c1 :: rest, i, pts, hlen, hpts => by
    have hrest : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hlen
      omega
    have hpoly_lt : i % 16 < pts.length := by
      rw [hpts]
      exact Nat.mod_lt i (by decide)
    let pt := pts[i % 16]
    have hpt : pts[i % 16]? = some pt :=
      List.getElem?_eq_some_iff.mpr ⟨hpoly_lt, rfl⟩
    have hpts' : (pts.set (i % 16) { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] }).length = 16 := by
      rw [List.length_set, hpts]
    have ih := distributeMsgChunks_eq_ok rest (i + 1)
      (pts.set (i % 16) { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] })
      hrest hpts'
    simp only [PolyEncoder.distributeMsgChunks, distributeMsgChunksTotal, hpts, hpt, Option.getD_some]
    exact ih

/-- `PolyEncoder.encodeBytes msg` always returns `.ok (encodeBytesResult msg)` (never `.error PolyPanic`). -/
@[simp] theorem encodeBytes_eq_ok (msg : List (BitVec 8)) :
    PolyEncoder.encodeBytes msg = .ok (encodeBytesResult msg) := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase encodeBytesResult
  split_ifs with hodd hlong
  · rfl
  · rfl
  · simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd
    have hinit : (List.replicate NUM_POLYS ({ value := [] } : Point)).length = 16 := by
      simp [NUM_POLYS, CHUNK_SIZE]
    have hd := (distributeMsgChunks_eq_ok msg 0 (List.replicate NUM_POLYS { value := [] }) hodd hinit).1
    simp [hd, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]

/-- Every `Point` in `distributeMsgChunksTotal i msg pts` has length bounded by `i + msg.length / 2`
    whenever every initial `pt ∈ pts` has `pt.value.length ≤ i`. -/
theorem distributeMsgChunksTotal_value_length_le :
    ∀ (msg : List (BitVec 8)) (i : Nat) (pts : List Point),
      msg.length % 2 = 0 →
      pts.length = 16 →
      (∀ pt ∈ pts, pt.value.length ≤ i) →
      ∀ pt ∈ distributeMsgChunksTotal i msg pts, pt.value.length ≤ i + msg.length / 2
  | [], i, pts, _, _, hbound => by
    intro pt hpt
    simpa [distributeMsgChunksTotal] using hbound pt hpt
  | [ _ ], _, _, hlen, _, _ => by
    simp at hlen
  | c0 :: c1 :: rest, i, pts, hlen, hpts, hbound => by
    have hrest : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hlen
      omega
    have hpoly_lt : i % 16 < pts.length := by
      rw [hpts]
      exact Nat.mod_lt i (by decide)
    have hpt0 : pts[i % 16]? = some pts[i % 16] :=
      List.getElem?_eq_some_iff.mpr ⟨hpoly_lt, rfl⟩
    let pt0 := pts[i % 16]
    let gf := GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)
    let pts' := pts.set (i % 16) { value := pt0.value ++ [gf] }
    have hpts' : pts'.length = 16 := by
       dsimp [pts']; rw [List.length_set, hpts]
    have hbound' : ∀ pt ∈ pts', pt.value.length ≤ i + 1 := by
      intro pt hpt
      rcases List.mem_or_eq_of_mem_set hpt with hmem | rfl
      · exact Nat.le_succ_of_le (hbound pt hmem)
      · have hpt0_mem : pt0 ∈ pts := List.mem_of_getElem? hpt0
        have hle0 := hbound pt0 hpt0_mem
        simp only [List.length_append, List.length_singleton]
        omega
    have ih := distributeMsgChunksTotal_value_length_le rest (i + 1) pts' hrest hpts' hbound'
    intro pt hpt
    simp only [distributeMsgChunksTotal, hpt0, Option.getD_some] at hpt
    have h1 := ih pt hpt
    have hdiv : (c0 :: c1 :: rest).length / 2 = rest.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    omega

/-! ## Pinned-to-Unpinned Representation Bridge Lemmas -/

theorem pointPinAt_entails_pointOf (A : RustAlloc) (pin : VecPin) (pt : Point) (v : BitVec 64) :
    pointPinAt A pin pt v ⊢ pointOf A v pt := by
  unfold pointPinAt pointAt pointOf vecOf
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem pointListPinAt_entails_pointListOf (A : RustAlloc) :
    ∀ (base : BitVec 64) (pins : List VecPin) (pts : List Point),
      pointListPinAt A base pins pts ⊢ pointListOf A base pts
  | _, _, [] => by
    simp [pointListPinAt, pointListOf, arrayAt]
    exact Entails.refl _
  | _, [], _ :: _ => by
    simp only [pointListPinAt]
    exact Entails.pure_left_only fun h => False.elim h
  | base, pin :: pins, pt :: pts => by
    simp only [pointListPinAt, pointListOf, arrayAt]
    exact sepConj_mono (pointPinAt_entails_pointOf A pin pt base)
      (pointListPinAt_entails_pointListOf A (base + 24#64) pins pts)

theorem polyPinAt_entails_polyOf (A : RustAlloc) (pin : VecPin) (p : LibsignalSpqrV1.Poly) (v : BitVec 64) :
    polyPinAt A pin p v ⊢ polyOf A v p := by
  unfold polyPinAt polyAt polyOf vecOf
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem polyListPinAt_entails_polyListOf (A : RustAlloc) :
    ∀ (base : BitVec 64) (pins : List VecPin) (ps : List LibsignalSpqrV1.Poly),
      polyListPinAt A base pins ps ⊢ polyListOf A base ps
  | _, _, [] => by
    simp [polyListPinAt, polyListOf, arrayAt]
    exact Entails.refl _
  | _, [], _ :: _ => by
    simp only [polyListPinAt]
    exact Entails.pure_left_only fun h => False.elim h
  | base, pin :: pins, p :: ps => by
    simp only [polyListPinAt, polyListOf, arrayAt]
    exact sepConj_mono (polyPinAt_entails_polyOf A pin p base)
      (polyListPinAt_entails_polyListOf A (base + 24#64) pins ps)

theorem encoderStatePinnedAt_entails_encoderStateAt (A : RustAlloc) (g : PolyEncoderGhost)
    (a : BitVec 64) (s : EncoderState) :
    encoderStatePinnedAt A g a s ⊢ encoderStateAt A a s := by
  cases s with
  | points pts =>
    simp only [encoderStatePinnedAt, encoderStateAt]
    refine Entails.pure_left fun ⟨hpts, _, hbounds⟩ => ?_
    exact Entails.pure_right ⟨hpts, hbounds⟩
      (sepConj_mono_right (pointListPinAt_entails_pointListOf A (a + polyEncoderVecsOff) g.pins pts))
  | polys polys =>
    simp only [encoderStatePinnedAt, encoderStateAt]
    refine Entails.pure_left fun ⟨hpolys, _⟩ => ?_
    exact Entails.pure_right hpolys
      (sepConj_mono_right (polyListPinAt_entails_polyListOf A (a + polyEncoderVecsOff) g.pins polys))

theorem polyEncoderPinnedAt_entails_polyEncoderAt (A : RustAlloc) (g : PolyEncoderGhost)
    (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderPinnedAt A g a enc ⊢ polyEncoderAt A a enc := by
  unfold polyEncoderPinnedAt polyEncoderAt
  exact sepConj_mono_left (encoderStatePinnedAt_entails_encoderStateAt A g a enc.s)

theorem resultPolyEncoderPinnedAt_entails_resultPolyEncoderAt (A : RustAlloc) (g : PolyEncoderGhost)
    (a : BitVec 64) (res : Except EncodingError PolyEncoder) :
    resultPolyEncoderPinnedAt A g a res ⊢ resultPolyEncoderAt A a res := by
  cases res with
  | ok enc => exact polyEncoderPinnedAt_entails_polyEncoderAt A g a enc
  | error err => exact Entails.refl _

/-! ## Specification of `<PolyEncoder as Encoder>::encode_bytes` (`0x6b6b8`) -/

/-- Ghost arguments of `<PolyEncoder as Encoder>::encode_bytes` (`0x6b6b8`). -/
structure EncodeBytesGhost where
  /-- Sret pointer (`x8`, 400-byte `Result<PolyEncoder, EncodingError>` output). -/
  out : BitVec 64
  /-- Whether `msg` is read-only (`true` → `↦ᵣ`) or read-write (`false` → `↦ₛ`). -/
  msgRO : Bool
  /-- Message slice pointer (`x0`). -/
  msgA : BitVec 64
  /-- Message bytes (`x1 = BitVec.ofNat 64 msg.length`). -/
  msg : List (BitVec 8)

/-- Specification of `<PolyEncoder as Encoder>::encode_bytes` (`0x6b6b8`): reads `bytesAt x.msgRO x.msgA x.msg` (`x0 = msgA`, `x1 = msg.length`) and writes `resultPolyEncoderAt A out (encodeBytesResult x.msg)` to `x8 = out` (or panics on OOM). -/
def encodeBytesSpec (A : RustAlloc) : Spec EncodeBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.msg.length ∧
      x.msg.length < 2 ^ 64⌝ ∗
      memRegion x.out polyEncoderSize ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool ∗ stackAt s.sp encodeBytesStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderAt A x.out (encodeBytesResult x.msg) ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool ∗ stackAt s0.sp encodeBytesStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Extended-stack variant of `encodeBytesSpec` (`encodeBytesStackX = 560 + extHookStack`). -/
def encodeBytesSpecX (A : RustAlloc) : Spec EncodeBytesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.msg.length ∧
      x.msg.length < 2 ^ 64⌝ ∗
      memRegion x.out polyEncoderSize ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool ∗ stackAt s.sp encodeBytesStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderAt A x.out (encodeBytesResult x.msg) ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool ∗ stackAt s0.sp encodeBytesStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def EncodeBytesOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg b ext)
    ((contractProg b ext).fnAddr encodeBytesName)
    (encodeBytesSpec A)

def EncodeBytesOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr encodeBytesName)
    ((encodeBytesSpecX A).inImage img)

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_blk_417 (pl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve pl encodeBytesName = pl.base 417 :=
  ls_resolve_block (by decide +kernel)

def EncodeBytesPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
    ((blkPl_417).base)
    (encodeBytesSpec A)

def EncodeBytesPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
    ((blkPl_417).base)
    (encodeBytesSpecX A)

/-! ## Instruction Decode Tree and Fetch Macro (`0x6b6b8..0x6b9fc`) -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

gen_decodes libsignalSessionCode_tree spqrEncodeBytesBin
  [0x662c0 → 0x66604]

@[simp, arm64_norm] theorem encodeBytes_fnOff :
    libsignalSessionCode.fnOff encodeBytesName = 0x662c0 :=
  libsignalSessionCode_fnOff_0x662c0

macro "encode_bytes_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrEncodeBytesBin $b $H libsignalSessionCode_fnOff_0x662c0 0x662c0 $k0 $len)

/-! ## Shared Pure & Separation-Logic Helpers for `encode_bytes` -/

theorem sepWPp_pure_mid {prog : Program} {target_pc : BitVec 64}
    {s : State} {L1 L2 R : SepProp} {φ : Prop}
    {Q Q_panic : State → SepProp → Prop}
    (h : φ → SepWPp prog target_pc s (L1 ∗ L2 ∗ R) Q Q_panic) :
    SepWPp prog target_pc s (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) Q Q_panic := by
  have heq : (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) = (⌜φ⌝ ∗ (L1 ∗ L2 ∗ R)) := by ac_rfl
  rw [heq]
  exact SepWPp.pure_left h

@[scoped arm64_norm, scoped wp_norm] theorem exists_pow_two_eq_two :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[scoped arm64_norm, scoped wp_norm]
theorem bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem sepWP_cells_succ {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog ret s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) post) :
    SepWP prog ret s (cells a (k + 1) ∗ Rest) post := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact SepWP.exists_left h

theorem sepWP_cells_zero {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog ret s Rest post) :
    SepWP prog ret s (cells a 0 ∗ Rest) post := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

theorem pointPinAt_empty (A : RustAlloc) (addr : BitVec 64) :
    ((addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 2#64) ∗ ((addr + 16#64) ↦₆₄ 0#64)) ⊢
      pointPinAt A ⟨0#64, 2#64⟩ { value := [] } addr := by
  unfold pointPinAt pointAt vecAt vecHeader vecBuf
  have hp : ([] : List GF16).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧
      (2#64 : BitVec 64) ≠ 0 := by decide
  have hite :
      (if (0#64 : BitVec 64) = 0 then emp
       else A.live 2#64 ((0#64 : BitVec 64).toNat * 2) gf16Align ∗
         arrayAt gf16At 2 2#64 [] ∗
         memRegion (2#64 + BitVec.ofNat 64 (([] : List GF16).length * 2))
           (((0#64 : BitVec 64).toNat - ([] : List GF16).length) * 2)) = emp := rfl
  rw [hite, sepConj_emp,
      sepConj_comm (P := (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 2#64) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List GF16).length))]
  exact Entails.pure_right hp (Entails.refl _)

theorem pointPinAt_empty_off (A : RustAlloc) (fsp : BitVec 64) (off : Nat) :
    (((fsp + BitVec.ofNat 64 off) ↦₆₄ 0#64) ∗
      ((fsp + BitVec.ofNat 64 (off + 8)) ↦₆₄ 2#64) ∗
      ((fsp + BitVec.ofNat 64 (off + 16)) ↦₆₄ 0#64)) ⊢
      pointPinAt A ⟨0#64, 2#64⟩ { value := [] } (fsp + BitVec.ofNat 64 off) := by
  simpa only [bv_add_add_lit, BitVec.ofNat_eq_ofNat] using
    pointPinAt_empty A (fsp + BitVec.ofNat 64 off)

theorem lsr_one_nat_eq_div_two (n : Nat) :
    (BitVec.ofNat 64 n) >>> 1 = BitVec.ofNat 64 ((n % 2 ^ 64) / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem lsr_one_eq_div_two (n : Nat) :
    (BitVec.ofNat 64 n) >>> 1#64 = BitVec.ofNat 64 ((n % 2 ^ 64) / 2) :=
  lsr_one_nat_eq_div_two n

theorem pointPinAt_fresh (A : RustAlloc) (addr ptr : BitVec 64) (msgLen : Nat)
    (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hne : ptr ≠ 0) :
    ((addr ↦₆₄ BitVec.ofNat 64 (msgLen / 2)) ∗
      ((addr + 8#64) ↦₆₄ ptr) ∗
      ((addr + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr msgLen 2 ∗ memRegion ptr msgLen) ⊢
      pointPinAt A ⟨BitVec.ofNat 64 (msgLen / 2), ptr⟩ { value := [] } addr := by
  unfold pointPinAt pointAt vecAt vecHeader vecBuf gf16Stride gf16Align
  dsimp only
  have htoNat : (BitVec.ofNat 64 (msgLen / 2)).toNat = msgLen / 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmul : (BitVec.ofNat 64 (msgLen / 2)).toNat * 2 = msgLen := by
    rw [htoNat]; omega
  have hcap_ne : BitVec.ofNat 64 (msgLen / 2) ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [htoNat] at ht
    change msgLen / 2 = 0 at ht
    omega
  have hcap_ne64 : BitVec.ofNat 64 (msgLen / 2) ≠ 0#64 := hcap_ne
  have hp : ([] : List GF16).length ≤ (BitVec.ofNat 64 (msgLen / 2)).toNat ∧
      (BitVec.ofNat 64 (msgLen / 2)).toNat * 2 < 2 ^ 63 ∧
      ptr ≠ 0 := by
    refine ⟨Nat.zero_le _, by rw [hmul]; omega, hne⟩
  have hite :
      (if BitVec.ofNat 64 (msgLen / 2) = 0 then emp
       else A.live ptr ((BitVec.ofNat 64 (msgLen / 2)).toNat * 2) 2 ∗
         arrayAt gf16At 2 ptr [] ∗
         memRegion (ptr + BitVec.ofNat 64 (([] : List GF16).length * 2))
           (((BitVec.ofNat 64 (msgLen / 2)).toNat - ([] : List GF16).length) * 2)) =
      (A.live ptr msgLen 2 ∗ memRegion ptr msgLen) := by
    simp only [hcap_ne64, ↓reduceIte, arrayAt, List.length_nil, Nat.zero_mul,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero, hmul, emp_sepConj]
  rw [hite]
  have hassoc :
      (addr ↦₆₄ BitVec.ofNat 64 (msgLen / 2)) ∗
        ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ 0#64) ∗
        A.live ptr msgLen 2 ∗ memRegion ptr msgLen =
      ((addr ↦₆₄ BitVec.ofNat 64 (msgLen / 2)) ∗
        ((addr + 8#64) ↦₆₄ ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List GF16).length)) ∗
        (A.live ptr msgLen 2 ∗ memRegion ptr msgLen) := by
    dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
    ac_rfl
  rw [hassoc]
  exact sepConj_mono_right (Entails.pure_right hp (Entails.refl _))

theorem pointPinAt_fresh_off (A : RustAlloc) (fsp ptr : BitVec 64) (msgLen off : Nat)
    (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hne : ptr ≠ 0) :
    (((fsp + BitVec.ofNat 64 off) ↦₆₄ BitVec.ofNat 64 (msgLen / 2)) ∗
      ((fsp + BitVec.ofNat 64 (off + 8)) ↦₆₄ ptr) ∗
      ((fsp + BitVec.ofNat 64 (off + 16)) ↦₆₄ 0#64) ∗
      A.live ptr msgLen 2 ∗ memRegion ptr msgLen) ⊢
      pointPinAt A ⟨BitVec.ofNat 64 (msgLen / 2), ptr⟩ { value := [] } (fsp + BitVec.ofNat 64 off) := by
  simpa only [bv_add_add_lit, BitVec.ofNat_eq_ofNat, sepConj_assoc] using
    pointPinAt_fresh A (fsp + BitVec.ofNat 64 off) ptr msgLen heven hpos hle hne

theorem cells_succ_entails (base : BitVec 64) (off k : Nat) (v : BitVec 64) (Rest : SepProp)
    (h : Rest ⊢ cells (base + BitVec.ofNat 64 (off + 8)) k) :
    ((base + BitVec.ofNat 64 off) ↦₆₄ v) ∗ Rest ⊢ cells (base + BitVec.ofNat 64 off) (k + 1) := by
  rw [ProofLib.cells_succ, bv_add_add_lit]
  exact Entails.sepExists_right v (sepConj_mono_right h)

theorem cells9_fsp_entails (fsp v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 64) :
    (fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
      ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
      ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ⊢
      cells fsp 9 := by
  rw [ProofLib.cells_succ]
  refine Entails.sepExists_right v0 (sepConj_mono_right ?_)
  refine cells_succ_entails fsp 8 7 v1 _ ?_
  refine cells_succ_entails fsp 16 6 v2 _ ?_
  refine cells_succ_entails fsp 24 5 v3 _ ?_
  refine cells_succ_entails fsp 32 4 v4 _ ?_
  refine cells_succ_entails fsp 40 3 v5 _ ?_
  refine cells_succ_entails fsp 48 2 v6 _ ?_
  refine cells_succ_entails fsp 56 1 v7 _ ?_
  have h0 := cells_succ_entails fsp 64 0 v8 emp (by rw [ProofLib.cells_zero]; exact Entails.refl _)
  simpa only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp] using h0

/-- The 12 saved register cells at `s0.sp - 96#64 .. s0.sp - 8#64`. -/
def savedCells (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
  ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗
  ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
  ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
  ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
  ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
  ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

theorem stackAt_encodeBytes_split_96 (sp : BitVec 64) :
    stackAt sp encodeBytesStack =
      stackAt (sp - 96#64) (allocHookStack + 464) ∗ cells (sp - 96#64) 12 := by
  have hEq : encodeBytesStack = (allocHookStack + 464) + 8 * 12 := rfl
  rw [hEq]
  exact ProofLib.stackAt_split_cells sp (allocHookStack + 464) 12 (by decide)

theorem stackAt_96_split_464 (sp : BitVec 64) :
    stackAt (sp - 96#64) (allocHookStack + 464) =
      stackAt (sp - 560#64) allocHookStack ∗ memRegion (sp - 560#64) 464 := by
  simp only [stackAt]
  rw [memRegion_split ((sp - 96#64) - BitVec.ofNat 64 (allocHookStack + 464))
    allocHookStack 464 (by decide)]
  have h1 : (sp - 96#64) - BitVec.ofNat 64 (allocHookStack + 464) =
      (sp - 560#64) - BitVec.ofNat 64 allocHookStack := by
    change (sp - 96#64) - 4560#64 = (sp - 560#64) - 4096#64
    bv_omega
  have h2 : (sp - 96#64) - BitVec.ofNat 64 (allocHookStack + 464) + BitVec.ofNat 64 allocHookStack =
      sp - 560#64 := by
    change (sp - 96#64) - 4560#64 + 4096#64 = sp - 560#64
    bv_omega
  rw [h2, h1]

theorem memRegion_464_split (fsp : BitVec 64) :
    memRegion fsp 464 =
      cells fsp 9 ∗ memRegion (fsp + 72#64) 384 ∗ memRegion (fsp + 456#64) 8 := by
  rw [ProofLib.memRegion_split' (b := fsp) (n := 72) (k := 392)
        (b' := fsp + 72#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 72#64) (n := 384) (k := 8)
        (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells fsp 9 (by decide)]

theorem savedCells_entails_cells12 (s0 : State) :
    savedCells s0 ⊢ cells (s0.sp - 96#64) 12 := by
  unfold savedCells
  refine cells_sub_succ_entails 96 12 ?_
  refine cells_sub_succ_entails 88 11 ?_
  refine cells_sub_succ_entails 80 10 ?_
  refine cells_sub_succ_entails 72 9 ?_
  refine cells_sub_succ_entails 64 8 ?_
  refine cells_sub_succ_entails 56 7 ?_
  refine cells_sub_succ_entails 48 6 ?_
  refine cells_sub_succ_entails 40 5 ?_
  refine cells_sub_succ_entails 32 4 ?_
  refine cells_sub_succ_entails 24 3 ?_
  refine cells_sub_succ_entails 16 2 ?_
  rw [cells_sub_succ s0.sp 8 1 (by decide) (by decide), cells_zero]
  simp only [sepConj_emp]
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) (Entails.refl _)

theorem savedCells_restore_stack (s0 : State) (R : SepProp) :
    savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ R ⊢
      R ∗ stackAt s0.sp encodeBytesStack := by
  rw [stackAt_encodeBytes_split_96 s0.sp]
  refine Entails.trans (sepConj_mono_left (savedCells_entails_cells12 s0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_out_err_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d8 : BitVec 8,
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₈ d8) ∗ memRegion (out + 9#64) 391 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 391)
        (b' := out + 9#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_one (out + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d8
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d8 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_out_ok_open (out : BitVec 64) :
    memRegion out polyEncoderSize ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d392 : BitVec 32,
        (out ↦₆₄ d0) ∗ memRegion (out + 8#64) 384 ∗
          ((out + 392#64) ↦₃₂ d392) ∗ memRegion (out + 396#64) 4 := by
  change memRegion out 400 ⊢ _
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 392)
        (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 384) (k := 8)
        (b' := out + 392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 392#64) (n := 4) (k := 4)
        (b' := out + 396#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight out, ProofLib.memRegion_four (out + 392#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d392
  apply Entails.sepExists_elim; intro d0
  refine Entails.sepExists_right d0 (Entails.sepExists_right d392 ?_)
  exact Entails.of_eq (by ac_rfl)

@[scoped arm64_norm, scoped wp_norm] theorem bv384_toNat : (384#64 : BitVec 64).toNat = 384 := rfl

theorem memRegion_464_split_560 (sp : BitVec 64) :
    memRegion (sp - 560#64) 464 =
      cells (sp - 560#64) 9 ∗ memRegion (sp - 488#64) 384 ∗ memRegion (sp - 104#64) 8 := by
  rw [memRegion_464_split (sp - 560#64)]
  have h1 : (sp - 560#64) + 72#64 = sp - 488#64 := by bv_omega
  have h2 : (sp - 560#64) + 456#64 = sp - 104#64 := by bv_omega
  rw [h1, h2]

theorem sepWPp_cells_succ {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {Q Q_panic : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWPp prog ret s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) Q Q_panic) :
    SepWPp prog ret s (cells a (k + 1) ∗ Rest) Q Q_panic := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact SepWPp.exists_elim h

theorem sepWPp_cells_zero {prog : Program} {ret : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {Q Q_panic : State → SepProp → Prop}
    (h : SepWPp prog ret s Rest Q Q_panic) :
    SepWPp prog ret s (cells a 0 ∗ Rest) Q Q_panic := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

theorem sepWPp_seq_clean {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Q_panic : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQm⟩ =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hQm))

theorem tbnz_bit0_of_odd (n : Nat) (hodd : n % 2 != 0) :
    ((BitVec.ofNat 64 n).truncate 32 &&& (1#32 <<< 0) != 0#32) = true := by
  simp only [bne_iff_ne] at hodd
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_zero,
    Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod] at ht
  omega

theorem tbnz_bit0_of_even (n : Nat) (heven : n % 2 = 0) :
    ((BitVec.ofNat 64 n).truncate 32 &&& (1#32 <<< 0) != 0#32) = false := by
  rw [bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_zero,
    Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod]
  omega

theorem tbnz64_bit0_of_odd (n : Nat) (hodd : n % 2 != 0) :
    ((BitVec.ofNat 64 n) &&& (1#64 <<< 0) != 0#64) = true := by
  simp only [bne_iff_ne] at hodd
  rw [bne_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_zero,
    Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod] at ht
  omega

theorem tbnz64_bit0_of_even (n : Nat) (heven : n % 2 = 0) :
    ((BitVec.ofNat 64 n) &&& (1#64 <<< 0) != 0#64) = false := by
  rw [bne_eq_false_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_zero,
    Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod]
  omega

theorem bv_ule_1048576_of_le (n : Nat) (hle : n ≤ 1048576) :
    (BitVec.ofNat 64 n).ule 1048576#64 = true := by
  rw [BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem bv_ule_1048576_of_gt (n : Nat) (hgt : 1048576 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).ule 1048576#64 = false := by
  rw [Bool.eq_false_iff, ne_eq, BitVec.ule_iff_toNat_le, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem bv_ne_zero_of_pos (n : Nat) (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

theorem shiftLeft_8_eq_mul_256 (x : BitVec 16) : x <<< 8 = x * 256#16 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_mul, Nat.shiftLeft_eq]

@[scoped arm64_norm, scoped wp_norm]
theorem rev16_pair_eq_gf16 (c0 c1 : BitVec 8) :
    ((rev16_64 ((c1 ++ c0).zeroExtend 64)).setWidth 32).setWidth 16 =
      (GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)).value := by
  change ((rev16_64 ((c1 ++ c0).zeroExtend 64)).setWidth 32).setWidth 16 =
    (c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16
  have h1 : ((rev16_64 ((c1 ++ c0).zeroExtend 64)).setWidth 32).setWidth 16 = c0 ++ c1 := by
    unfold rev16_64
    bv_slice
  have h_lo : (c0 ++ c1).extractLsb' 0 8 = c1 := by bv_slice
  have h_hi : (c0 ++ c1).extractLsb' 8 8 = c0 := by bv_slice
  have hlt : (c0 ++ c1).toNat < 65536 := (c0 ++ c1).isLt
  have h_lo_nat : ((c0 ++ c1).extractLsb' 0 8).toNat = (c0 ++ c1).toNat % 256 := by
    rw [BitVec.extractLsb'_toNat]
    simp
  rw [h_lo] at h_lo_nat
  have h_hi_nat : ((c0 ++ c1).extractLsb' 8 8).toNat = (c0 ++ c1).toNat / 256 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    change ((c0 ++ c1).toNat / 256) % 256 = (c0 ++ c1).toNat / 256
    omega
  rw [h_hi] at h_hi_nat
  rw [h1, shiftLeft_8_eq_mul_256]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, h_lo_nat, h_hi_nat]
  change (c0 ++ c1).toNat = (((c0 ++ c1).toNat / 256 % 65536 * 256) % 65536 +
    (c0 ++ c1).toNat % 256 % 65536) % 65536
  omega

theorem bv_and_15_eq_mod_16 (i : Nat) (hi : i < 2 ^ 64) :
    BitVec.ofNat 64 i &&& 15#64 = BitVec.ofNat 64 (i % 16) := by
  apply BitVec.eq_of_toNat_eq
  have hmod : (i % 16) < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hmod]
  change i &&& (2 ^ 4 - 1) = i % 16
  rw [Nat.and_two_pow_sub_one_eq_mod]

@[scoped arm64_norm, scoped wp_norm]
theorem umaddl_poly_24 (base : BitVec 64) (i : Nat) :
    base + ((BitVec.ofNat 64 (i % 16)).setWidth 32).zeroExtend 64 * 24#64 =
      base + BitVec.ofNat 64 (24 * (i % 16)) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hpoly : i % 16 < 16 := Nat.mod_lt i (by decide)
  have h1 : (((BitVec.ofNat 64 (i % 16)).setWidth 32).zeroExtend 64).toNat = i % 16 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have h2 : (24#64 : BitVec 64).toNat = 24 := rfl
  rw [BitVec.toNat_mul, h1, h2, BitVec.toNat_ofNat]
  omega

@[scoped arm64_norm, scoped wp_norm]
theorem shiftLeft_one_nat_eq_mul_two (len : Nat) :
    BitVec.ofNat 64 len <<< 1 = BitVec.ofNat 64 (2 * len) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.pow_one]
  omega

@[scoped arm64_norm, scoped wp_norm]
theorem shiftLeft_one_eq_mul_two (len : Nat) :
    BitVec.ofNat 64 len <<< 1#64 = BitVec.ofNat 64 (2 * len) :=
  shiftLeft_one_nat_eq_mul_two len

theorem bne_cap_of_lt {len cap : Nat} (hlt : len < cap) (hcap : cap < 2 ^ 64) :
    (BitVec.ofNat 64 len != BitVec.ofNat 64 cap) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hcap] at ht
  omega

theorem beq_total_of_eq {n : Nat} :
    (BitVec.ofNat 64 n == BitVec.ofNat 64 n) = true := by
  simp

theorem beq_total_false_of_lt {i total : Nat} (hlt : i < total) (htot : total < 2 ^ 64) :
    (BitVec.ofNat 64 total == BitVec.ofNat 64 i) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt htot, Nat.mod_eq_of_lt (by omega)] at ht
  omega

@[scoped arm64_norm, scoped wp_norm]
theorem ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [BitVec.ofNat_add]

theorem bytesAt_append (ro : Bool) (p : BitVec 64) (bs1 bs2 : List (BitVec 8)) :
    bytesAt ro p (bs1 ++ bs2) =
      bytesAt ro p bs1 ∗ bytesAt ro (p + BitVec.ofNat 64 bs1.length) bs2 := by
  cases ro
  · simp [bytesAt, pointsToBytes_append]
  · simp [bytesAt, pointsToBytesRO_append]

theorem bytesAt_pair_ro (p : BitVec 64) (c0 c1 : BitVec 8) :
    bytesAt true p [c0, c1] = (p ↦₁₆ᵣ (c1 ++ c0)) := by
  rw [bytesAt_true, pointsToBytesRO2_eq_pointsTo16RO]

theorem bytesAt_pair_rw (p : BitVec 64) (c0 c1 : BitVec 8) :
    bytesAt false p [c0, c1] = (p ↦₁₆ (c1 ++ c0)) := by
  rw [bytesAt_false, pointsToBytes2_eq_pointsTo16]

theorem bytesAt_cons_cons (ro : Bool) (p : BitVec 64) (c0 c1 : BitVec 8) (rest : List (BitVec 8)) :
    bytesAt ro p (c0 :: c1 :: rest) =
      bytesAt ro p [c0, c1] ∗ bytesAt ro (p + 2#64) rest := by
  change bytesAt ro p ([c0, c1] ++ rest) = _
  rw [bytesAt_append]
  rfl

theorem pointListPinAt_split_at (A : RustAlloc)
    (base : BitVec 64) (pins : List VecPin) (pts : List Point) (k : Nat)
    (hlen : pins.length = pts.length) (hk : k < pts.length) :
    pointListPinAt A base pins pts =
      pointPinAt A (pins[k]'(by omega)) (pts[k]'hk) (base + BitVec.ofNat 64 (24 * k)) ∗
        (pointListPinAt A base (pins.take k) (pts.take k) ∗
         pointListPinAt A (base + BitVec.ofNat 64 (24 * (k + 1))) (pins.drop (k + 1)) (pts.drop (k + 1))) := by
  induction pts generalizing base pins k with
  | nil => simp at hk
  | cons pt pts ih =>
    cases pins with
    | nil => simp at hlen
    | cons pin pins =>
      cases k with
      | zero =>
        simp only [Nat.mul_zero, BitVec.add_zero, List.getElem_cons_zero,
          List.take_zero, List.drop_succ_cons, List.drop_zero, pointListPinAt, emp_sepConj,
          Nat.zero_add, Nat.mul_one]
      | succ k =>
        have hlen' : pins.length = pts.length := by simpa using hlen
        have hk' : k < pts.length := by simpa using hk
        have ihk := ih (base + 24#64) pins k hlen' hk'
        have haddr1 : (base + 24#64) + BitVec.ofNat 64 (24 * k) =
            base + BitVec.ofNat 64 (24 * (k + 1)) := by
          have h1 : 24 * (k + 1) = 24 + 24 * k := by omega
          rw [BitVec.add_assoc, h1, BitVec.ofNat_add]
        have haddr2 : (base + 24#64) + BitVec.ofNat 64 (24 * (k + 1)) =
            base + BitVec.ofNat 64 (24 * (k + 1 + 1)) := by
          have h1 : 24 * (k + 1 + 1) = 24 + 24 * (k + 1) := by omega
          rw [BitVec.add_assoc, h1, BitVec.ofNat_add]
        simp only [pointListPinAt, List.getElem_cons_succ, List.take_succ_cons, List.drop_succ_cons]
        rw [ihk, haddr1, haddr2]
        ac_rfl

theorem pointListPinAt_set_eq (A : RustAlloc) (base : BitVec 64)
    (pins : List VecPin) (pts : List Point) (k : Nat) (pt' : Point)
    (hlen : pins.length = pts.length) (hk : k < pts.length) :
    pointPinAt A (pins[k]'(by omega)) pt' (base + BitVec.ofNat 64 (24 * k)) ∗
      (pointListPinAt A base (pins.take k) (pts.take k) ∗
       pointListPinAt A (base + BitVec.ofNat 64 (24 * (k + 1))) (pins.drop (k + 1)) (pts.drop (k + 1))) =
      pointListPinAt A base pins (pts.set k pt') := by
  induction pts generalizing base pins k with
  | nil => simp at hk
  | cons pt pts ih =>
    cases pins with
    | nil => simp at hlen
    | cons pin pins =>
      cases k with
      | zero =>
        simp only [Nat.mul_zero, BitVec.add_zero, List.getElem_cons_zero,
          List.take_zero, List.drop_succ_cons, List.drop_zero, List.set_cons_zero,
          pointListPinAt, emp_sepConj, Nat.zero_add, Nat.mul_one]
      | succ k =>
        have hlen' : pins.length = pts.length := by simpa using hlen
        have hk' : k < pts.length := by simpa using hk
        have ihk := ih (base + 24#64) pins k hlen' hk'
        have haddr1 : (base + 24#64) + BitVec.ofNat 64 (24 * k) =
            base + BitVec.ofNat 64 (24 * (k + 1)) := by
          have h1 : 24 * (k + 1) = 24 + 24 * k := by omega
          rw [BitVec.add_assoc, h1, BitVec.ofNat_add]
        have haddr2 : (base + 24#64) + BitVec.ofNat 64 (24 * (k + 1)) =
            base + BitVec.ofNat 64 (24 * (k + 1 + 1)) := by
          have h1 : 24 * (k + 1 + 1) = 24 + 24 * (k + 1) := by omega
          rw [BitVec.add_assoc, h1, BitVec.ofNat_add]
        simp only [pointListPinAt, List.getElem_cons_succ, List.take_succ_cons, List.drop_succ_cons,
          List.set_cons_succ]
        rw [← ihk, haddr1, haddr2]
        ac_rfl

theorem sp_sub_96_sub_464 (sp : BitVec 64) : (sp - 96#64) - 464#64 = sp - 560#64 := by bv_omega
theorem sp_sub_560_add_464 (sp : BitVec 64) : (sp - 560#64) + 464#64 = sp - 96#64 := by bv_omega
theorem sp_sub_96_add_8 (sp : BitVec 64) : (sp - 96#64) + 8#64 = sp - 88#64 := by bv_omega
theorem sp_sub_96_add_16 (sp : BitVec 64) : (sp - 96#64) + 16#64 = sp - 80#64 := by bv_omega
theorem sp_sub_96_add_24 (sp : BitVec 64) : (sp - 96#64) + 24#64 = sp - 72#64 := by bv_omega
theorem sp_sub_96_add_32 (sp : BitVec 64) : (sp - 96#64) + 32#64 = sp - 64#64 := by bv_omega
theorem sp_sub_96_add_40 (sp : BitVec 64) : (sp - 96#64) + 40#64 = sp - 56#64 := by bv_omega
theorem sp_sub_96_add_48 (sp : BitVec 64) : (sp - 96#64) + 48#64 = sp - 48#64 := by bv_omega
theorem sp_sub_96_add_56 (sp : BitVec 64) : (sp - 96#64) + 56#64 = sp - 40#64 := by bv_omega
theorem sp_sub_96_add_64 (sp : BitVec 64) : (sp - 96#64) + 64#64 = sp - 32#64 := by bv_omega
theorem sp_sub_96_add_72 (sp : BitVec 64) : (sp - 96#64) + 72#64 = sp - 24#64 := by bv_omega
theorem sp_sub_96_add_80 (sp : BitVec 64) : (sp - 96#64) + 80#64 = sp - 16#64 := by bv_omega
theorem sp_sub_96_add_88 (sp : BitVec 64) : (sp - 96#64) + 88#64 = sp - 8#64 := by bv_omega
theorem sp_sub_96_add_96 (sp : BitVec 64) : (sp - 96#64) + 96#64 = sp := by bv_omega
theorem sp_sub_88_add_8 (sp : BitVec 64) : (sp - 88#64) + 8#64 = sp - 80#64 := by bv_omega
theorem sp_sub_80_add_8 (sp : BitVec 64) : (sp - 80#64) + 8#64 = sp - 72#64 := by bv_omega
theorem sp_sub_72_add_8 (sp : BitVec 64) : (sp - 72#64) + 8#64 = sp - 64#64 := by bv_omega
theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
theorem sp_sub_56_add_8 (sp : BitVec 64) : (sp - 56#64) + 8#64 = sp - 48#64 := by bv_omega
theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
theorem sp_sub_40_add_8 (sp : BitVec 64) : (sp - 40#64) + 8#64 = sp - 32#64 := by bv_omega
theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
theorem sp_sub_24_add_8 (sp : BitVec 64) : (sp - 24#64) + 8#64 = sp - 16#64 := by bv_omega
theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega

theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

/-- `encodeBytesSpec A` entails `encodeBytesSpecX A` by framing the unused bottom stack region. -/
theorem encodeBytesSpecX_of_encodeBytesSpec {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (encodeBytesSpec A)) :
    subroutine_ok P addr (encodeBytesSpecX A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre' : s0.mem ⊨ (encodeBytesSpec A).pre x s0 ∗ R' := by
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [encodeBytesSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hpost).elim

theorem seq_clean {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hPm, hQ⟩ =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hQ)

section PlacedEpilogue
variable [LibsignalPlacement]

theorem encode_bytes_epilogue_placed {ext : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 692#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align
  unfold savedCells; wp_steps
  refine align_pre (by
    change savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame ⊢
      Frame ∗ stackAt s0.sp encodeBytesStack
    exact savedCells_restore_stack s0 Frame) ?_
  wp_done

theorem encode_bytes_err_odd_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 72#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.error (.polynomialError .messageLengthEven)) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d8
  refine seq_clean (mid := (blkPl_417).base + 692#64)
    (P_mid := savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
      (resultPolyEncoderAt A out (.error (.polynomialError .messageLengthEven)) ∗ Frame))
    (Q := fun sm => sm.sp = s0.sp - 560#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine align_pre (by
      dsimp only [resultPolyEncoderAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        encodingErrorByte, polynomialErrorByte, resultPolyEncoderErrTailSize]
      exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htrace1, hvregs1⟩
    simpa only [sepConj_assoc] using
      encode_bytes_epilogue_placed s0 s1
        (resultPolyEncoderAt A out (.error (.polynomialError .messageLengthEven)) ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 htrace1 hvregs1

theorem encode_bytes_err_too_long_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 52#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.error (.polynomialError .messageLengthTooLong)) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (sepConj_mono_left (memRegion_out_err_open out)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro d0; apply SepWP.exists_left; intro d8
  refine seq_clean (mid := (blkPl_417).base + 692#64)
    (P_mid := savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗
      (resultPolyEncoderAt A out (.error (.polynomialError .messageLengthTooLong)) ∗ Frame))
    (Q := fun sm => sm.sp = s0.sp - 560#64 ∧ sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · wp_steps
    refine align_pre (by
      dsimp only [resultPolyEncoderAt, polyEncoderNicheTag, resultPolyEncoderErrByteOff,
        encodingErrorByte, polynomialErrorByte, resultPolyEncoderErrTailSize]
      exact Entails.of_eq (by ac_rfl)) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htrace1, hvregs1⟩
    simpa only [sepConj_assoc] using
      encode_bytes_epilogue_placed s0 s1
        (resultPolyEncoderAt A out (.error (.polynomialError .messageLengthTooLong)) ∗ Frame)
        hsp0_align hpc1 hrun1 hsp1 htrace1 hvregs1

end PlacedEpilogue

end CryptoVerification.SpqrV1.Poly.EncodeBytes

