/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SliceArray
public import ProofLib.SepLogic.WP.ControlTactics
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Hooks

/-!
# `ByteSlice`, `pointsToArray`, `addr_norm`, and WP Control Tactic Tests

Positive and negative regression tests for `ByteSlice` window splitting and little-endian updates,
`pointsToArray` and `sepRange` focusing, `stackFrameAt`, `[addr_norm]`, `wp_by_cases`, `wp_cases`,
`wp_conv_post`, and `declare_rebased_program`.
-/

open Arm64 ProofLib

namespace Examples.Testing.ProofLib.SliceArrayAndTactics

example (base : BitVec 64) (buf src : List (BitVec 8)) (off : Nat)
    (h : off + src.length ≤ buf.length) :
    (((base + BitVec.ofNat 64 off) ↦ₛ src) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + src.length)) ↦ₛ buf.drop (off + src.length)))) =
    (base ↦ₛ ByteSlice.write buf off src) :=
  pointsToBytes_write base buf src off h

example (bs : List (BitVec 8)) (off k j : Nat) :
    ByteSlice.readLE bs off (k + j) =
      ByteSlice.readLE bs off k ||| (ByteSlice.readLE bs (off + k) j <<< (8 * k)) :=
  ByteSlice.readLE_add bs off k j

example (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat) (v : BitVec 64)
    (h : off + 8 ≤ bs.length) :
    (((base + BitVec.ofNat 64 off) ↦₆₄ v) ∗
      ((base ↦ₛ bs.take off) ∗
       ((base + BitVec.ofNat 64 (off + 8)) ↦ₛ bs.drop (off + 8)))) =
    (base ↦ₛ ByteSlice.write64 bs off v) :=
  pointsToBytes_update64 base bs off v h

example (ptr : BitVec 64) (xs : List (BitVec 64)) (idx : BitVec 64) (x' : BitVec 64)
    (hi : idx.toNat < xs.length) (hs : (2 ^ 3) * idx.toNat < 2 ^ 64) :
    (((ptr + (idx <<< 3)) ↦₆₄ x') ∗
      (pointsToArray (2 ^ 3) (· ↦₆₄ ·) ptr (xs.take idx.toNat) ∗
       pointsToArray (2 ^ 3) (· ↦₆₄ ·)
         (ptr + BitVec.ofNat 64 ((2 ^ 3) * (idx.toNat + 1)))
         (xs.drop (idx.toNat + 1)))) =
    pointsToArray (2 ^ 3) (· ↦₆₄ ·) ptr (xs.set idx.toNat x') :=
  pointsToArray_update_shift 3 (· ↦₆₄ ·) ptr xs idx x' hi hs

example (base : BitVec 64) (a b : Nat) :
    base + BitVec.ofNat 64 a + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) := by
  simp only [addr_norm]

example {w : Nat} (base : BitVec w) (a b : Nat) (h : b ≤ a) :
    base - BitVec.ofNat w a + BitVec.ofNat w b = base - BitVec.ofNat w (a - b) := by
  simp only [addr_norm, h]

example {w : Nat} (base : BitVec w) (a b : Nat) :
    base - BitVec.ofNat w a - BitVec.ofNat w b = base - BitVec.ofNat w (a + b) := by
  simp only [addr_norm]

example (base : BitVec 64) (idx : BitVec 32) (off : Nat)
    (h1 : idx.toNat + off < 2 ^ 64) (h2 : off + idx.toNat < 2 ^ 64) :
    base + idx.setWidth 64 + BitVec.ofNat 64 off = base + BitVec.ofNat 64 (idx.toNat + off) ∧
    base + BitVec.ofNat 64 off + idx.setWidth 64 = base + BitVec.ofNat 64 (off + idx.toNat) := by
  simp only [addr_norm, h1, h2, and_self]

example {w : Nat} (a : BitVec w) (b : Nat) :
    BitVec.ofNat w (a.toNat + b) = a + BitVec.ofNat w b := by
  simp only [addr_norm]

example (dst v : BitVec 64) :
    Arm64.evalBitfield .W64 .SBFM dst v 0 31 = (v.setWidth 32).signExtend 64 := by
  simp only [width_norm]

example {w : Nat} (v : BitVec w) (k m : Nat) (hw : 0 < w) (h : v.toNat < 2 ^ (w - 1)) :
    v.sshiftRight k = v >>> k ∧ (v.toNat >>> k) % m = (v.toNat / 2 ^ k) % m :=
  ⟨BitVec.sshiftRight_of_lt_sign v k hw h, BitVec.toNat_shiftRight_mod_pow2 v k m⟩

example (base : BitVec 64) (idx : BitVec 32) (off : Nat)
    (h : base.toNat + idx.toNat + off < 2 ^ 64) :
    base ≤ base + idx.setWidth 64 + BitVec.ofNat 64 off := by
  bv_nat

example (x : BitVec 32) (b c : BitVec 8) :
    ((BitVec.setWidth 64 x = 0#64) ↔ (x = 0#32)) ∧
    ((BitVec.setWidth 64 b = BitVec.setWidth 64 c) ↔ (b = c)) := by
  simp (disch := first | decide | omega) only [wp_branch]
  exact ⟨trivial, trivial⟩

-- Negative test: `sub_ofNat_add_ofNat_of_le` requires `b ≤ a`.
/--
error: unsolved goals
w : Nat
base : BitVec w
a b : Nat
⊢ b ≤ a
-/
#guard_msgs in
example {w : Nat} (base : BitVec w) (a b : Nat) :
    base - BitVec.ofNat w a + BitVec.ofNat w b = base - BitVec.ofNat w (a - b) := by
  rw [BitVec.sub_ofNat_add_ofNat_of_le base]

-- Negative test: `add_setWidth_add_ofNat` requires non-overflow `idx.toNat + off < 2 ^ 64`.
/--
error: unsolved goals
base : BitVec 64
idx : BitVec 32
off : Nat
⊢ idx.toNat + off < 2 ^ 64
-/
#guard_msgs in
example (base : BitVec 64) (idx : BitVec 32) (off : Nat) :
    base + idx.setWidth 64 + BitVec.ofNat 64 off = base + BitVec.ofNat 64 (idx.toNat + off) := by
  rw [BitVec.add_setWidth_add_ofNat base idx off]

-- Negative test: `sshiftRight_of_lt_sign` requires sign-bit clear bound `v.toNat < 2 ^ (w - 1)`.
/--
error: unsolved goals
v : BitVec 64
k : Nat
⊢ v.toNat < 2 ^ (64 - 1)
-/
#guard_msgs in
example (v : BitVec 64) (k : Nat) :
    v.sshiftRight k = v >>> k := by
  rw [BitVec.sshiftRight_of_lt_sign v k (by decide)]

example (ptr : BitVec 64) (n : Nat) (hb : 8 * n ≤ 2 ^ 64) :
    stackFrameAt (ptr + BitVec.ofNat 64 (8 * n)) (8 * n) =
      ∃∗ ws : List (BitVec 64), ⌜ws.length = n⌝ ∗ (ptr ↦₆₄* ws) :=
  stackFrameAt_eq_pointsToWords64 ptr n hb

example (prog : Program) (pc : BitVec 64) (s : State) (c : Bool) (P : SepProp)
    (Q1 Q2 : State → SepProp → Prop)
    (h1 : c = true → SepWP prog pc s P Q1)
    (h2 : c = false → SepWP prog pc s P Q2) :
    SepWP prog pc s P (fun s' R => if c then Q1 s' R else Q2 s' R) := by
  wp_by_cases hc : c
  · exact h1 hc
  · exact h2 hc

-- Negative test: `pointsToBytes_write` requires in-bounds proof `off + src.length ≤ buf.length`.
/--
error: unsolved goals
base : BitVec 64
buf src : List (BitVec 8)
off : Nat
⊢ off + src.length ≤ buf.length
-/
#guard_msgs in
example (base : BitVec 64) (buf src : List (BitVec 8)) (off : Nat) :
    (((base + BitVec.ofNat 64 off) ↦ₛ src) ∗
      ((base ↦ₛ buf.take off) ∗
       ((base + BitVec.ofNat 64 (off + src.length)) ↦ₛ buf.drop (off + src.length)))) =
    (base ↦ₛ ByteSlice.write buf off src) := by
  rw [pointsToBytes_write base buf src off]

example (lo n i : Nat) (f : Nat → SepProp) (P : SepProp) (hi : i < n) :
    (sepRange lo i f ∗ (P ∗ sepRange (lo + i + 1) (n - i - 1) f)) =
      sepRange lo n (fun j => if j = lo + i then P else f j) := by
  rw [← sepRange_update lo n i f P hi]
  ac_rfl

example (ptr : BitVec 64) (ws : List (BitVec 64)) (idx : BitVec 64)
    (hi : idx.toNat < ws.length) :
    (ptr ↦₆₄* ws) =
      (((ptr + BitVec.ofNat 64 8 * idx) ↦₆₄ ws.getD idx.toNat default) ∗
        (pointsToArray 8 (· ↦₆₄ ·) ptr (ws.take idx.toNat) ∗
         pointsToArray 8 (· ↦₆₄ ·) (ptr + BitVec.ofNat 64 (8 * (idx.toNat + 1)))
           (ws.drop (idx.toNat + 1)))) := by
  rw [pointsToWords64_eq_pointsToArray, pointsToArray_focus_mul 8 (· ↦₆₄ ·) ptr ws idx hi]

example (ptr : BitVec 64) (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) =
      sepRange 0 bs.length (fun i => (ptr + BitVec.ofNat 64 (1 * i)) ↦₈ bs.getD i default) := by
  rw [pointsToBytes_eq_pointsToArray, pointsToArray_eq_sepRange]

-- Negative test: `sepRange_focus` requires in-bounds proof `i < n`.
/--
error: unsolved goals
lo n i : Nat
f : Nat → SepProp
⊢ i < n
-/
#guard_msgs in
example (lo n i : Nat) (f : Nat → SepProp) :
    sepRange lo n f = (f (lo + i) ∗ (sepRange lo i f ∗ sepRange (lo + i + 1) (n - i - 1) f)) := by
  rw [sepRange_focus lo n i f]

-- Negative test: `pointsToArray_focus_mul` requires in-bounds proof `idx.toNat < xs.length`.
/--
error: unsolved goals
ptr : BitVec 64
xs : List (BitVec 64)
idx : BitVec 64
⊢ idx.toNat < xs.length
-/
#guard_msgs in
example (ptr : BitVec 64) (xs : List (BitVec 64)) (idx : BitVec 64) :
    pointsToArray 8 (· ↦₆₄ ·) ptr xs =
      (((ptr + BitVec.ofNat 64 8 * idx) ↦₆₄ xs.getD idx.toNat default) ∗
        (pointsToArray 8 (· ↦₆₄ ·) ptr (xs.take idx.toNat) ∗
         pointsToArray 8 (· ↦₆₄ ·) (ptr + BitVec.ofNat 64 (8 * (idx.toNat + 1)))
           (xs.drop (idx.toNat + 1)))) := by
  rw [pointsToArray_focus_mul 8 (· ↦₆₄ ·) ptr xs idx]

example (v32 : BitVec 32) (v64 : BitVec 64) :
    (ByteSlice.unpackLE 4 v32).length = 4 ∧
    ByteSlice.write32 = ByteSlice.writeLE (w := 32) 4 ∧
    ByteSlice.write64 = ByteSlice.writeLE (w := 64) 8 ∧
    ByteSlice.readLE (ByteSlice.unpackLE 8 v64) 0 8 = v64 :=
  ⟨ByteSlice.unpackLE_length 4 v32, ByteSlice.write32_eq_writeLE,
   ByteSlice.write64_eq_writeLE, ByteSlice.readLE_unpackLE_64 8 v64 (by omega)⟩

example (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) (off k n : Nat)
    (h8 : off + 8 ≤ bs.length) (hk : k ≤ bs.length) (hread : m.readBytes a n = bs) :
    ((a ↦ₛ ProofLib.ByteSlice.slice bs off 1) = (a ↦₈ (ByteSlice.readLE bs off 1).setWidth 8)) ∧
    ((a ↦ₛ ProofLib.ByteSlice.slice bs off 2) = (a ↦₁₆ (ByteSlice.readLE bs off 2).setWidth 16)) ∧
    ((a ↦ₛ ProofLib.ByteSlice.slice bs off 4) = (a ↦₃₂ (ByteSlice.readLE bs off 4).setWidth 32)) ∧
    ((a ↦ₛ ProofLib.ByteSlice.slice bs off 8) = (a ↦₆₄ ByteSlice.readLE bs off 8)) ∧
    ((a ↦ₛ bs) = ((a ↦ₛ bs.take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop k))) ∧
    (m.readLE a n = ByteSlice.readLE bs 0 n) :=
  ⟨pointsToBytes_slice_eq_pointsTo8 a bs off (by omega),
   pointsToBytes_slice_eq_pointsTo16 a bs off (by omega),
   pointsToBytes_slice_eq_pointsTo32 a bs off (by omega),
   pointsToBytes_slice_eq_pointsTo64 a bs off h8,
   pointsToBytes_partition a bs k hk,
   Memory.readLE_of_readBytes m a bs n hread⟩

-- Negative test: `pointsToBytes_slice_eq_pointsTo32` requires `off + 4 ≤ bs.length`.
/--
error: unsolved goals
a : BitVec 64
bs : List (BitVec 8)
off : Nat
⊢ off + 4 ≤ bs.length
-/
#guard_msgs in
example (a : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    (a ↦ₛ ProofLib.ByteSlice.slice bs off 4) = (a ↦₃₂ (ByteSlice.readLE bs off 4).setWidth 32) := by
  rw [pointsToBytes_slice_eq_pointsTo32 a bs off]

/-! ## `wp_cases`, `wp_conv_post`, `subroutine_ok_mono_sp`, and `declare_rebased_program` -/

example (prog : Program) (pc : BitVec 64) (s : State) (P : SepProp)
    (Q : State → SepProp → Prop)
    (h : SepWP prog pc s P (fun sf R => Q sf (R ∗ emp))) :
    SepWP prog pc s P Q := by
  wp_conv_post =>
    ext sf R
    rw [← sepConj_emp R]
  exact h

example (prog : Program) (ret pc1 pc2 : BitVec 64) (s : State) (c : Bool) (P : SepProp)
    (Q1 Q2 : State → SepProp → Prop)
    (h1 : SepWP prog ret { s with pc := pc1 } P Q1)
    (h2 : SepWP prog ret { s with pc := pc2 } P Q2) :
    SepWP prog ret { s with pc := if c then pc1 else pc2 } P
      (fun s' R => if c then Q1 s' R else Q2 s' R) := by
  wp_cases
  · exact h1
  · exact h2

example (prog : Program) (pc : BitVec 64) (s : State) (c : Bool) (P : SepProp)
    (Q1 Q2 : State → SepProp → Prop)
    (h1 : c = true → SepWP prog pc s P Q1)
    (h2 : c = false → SepWP prog pc s P Q2) :
    SepWP prog pc s P (fun s' R => if c then Q1 s' R else Q2 s' R) := by
  wp_cases hc : c
  · exact h1 hc
  · exact h2 hc

example {prog : Program} {entry : BitVec 64} {spec : Spec Unit}
    (hok : subroutine_ok prog entry spec) :
    subroutine_ok prog entry spec :=
  subroutine_ok_mono_sp hok (fun _ _ => Entails.refl _) (fun _ _ _ _ => Entails.refl _)

private def sampleRawProg : Program := { code := [] }

declare_rebased_program sampleFixedRebased (0x100000#64 : BitVec 64) sampleRawProg

-- Negative test: `declare_rebased_program` rejects invalid argument types.
/--
error: declare_rebased_program: expected `(baseConst : BitVec 64) (rawProgram : Program)` or `(rawProgram : Program) (linkedImage : Obj.LinkedImage)`, got arguments of types `Nat` and `Nat`
-/
#guard_msgs in
declare_rebased_program badRebased (0 : Nat) (1 : Nat)

example (sp : BitVec 64) (m n : Nat) (hmn : m + n ≤ 2 ^ 64) :
    stackFrameAt sp (m + n) = (stackFrameAt sp m ∗ stackFrameAt (sp - BitVec.ofNat 64 m) n) :=
  stackFrameAt_split sp m n hmn

example (sp : BitVec 64) (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    stackFrameAt sp (8 * n) =
      ∃∗ ws : List (BitVec 64), ⌜ws.length = n⌝ ∗ ((sp - BitVec.ofNat 64 (8 * n)) ↦₆₄* ws) :=
  stackFrameAt_eq_exists_pointsToWords64 sp n hn

example (sp : BitVec 64) (n : Nat) (hn : n ≤ 2 ^ 64) :
    stackAt sp n = stackFrameAt sp n :=
  stackAt_eq_stackFrameAt sp n hn

example (sp : BitVec 64) (n : Nat) (hsp : (sp &&& 15#64 == 0#64) = true) (hdvd : 16 ∣ n) :
    ((sp - BitVec.ofNat 64 n) &&& 15#64 == 0#64) = true :=
  spAligned_sub_of_dvd sp n hsp hdvd

-- Negative test: `spAligned_sub_of_dvd` requires `16 ∣ n` and rejects unaligned byte counts.
/--
error: could not synthesize default value for parameter 'hdvd' using tactics
---
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
-/
#guard_msgs in
example (sp : BitVec 64) (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp - BitVec.ofNat 64 24) &&& 15#64 == 0#64) = true := by
  apply spAligned_sub_of_dvd sp 24 hsp

end Examples.Testing.ProofLib.SliceArrayAndTactics
