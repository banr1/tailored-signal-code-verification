/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbHelpers
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap

/-!
# Specifications and Helper Lemmas for `<spqr::chain::Chain>::into_pb`

Specifications (`chainIntoPbPinnedSpec`, `chainIntoPbSpec`, and `*X` variants), stride-112
`umulh` division by 7 (`0x2492492492492493#64`), 4-byte-shifted 52-byte cell rewrites for the
unaligned `recv` header copy, and separation-logic bridges between `Chain` and `ChainPB`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Stack Budgets, Ghost Conversions, and Specifications -/

abbrev chainIntoPbName : String :=
  "<spqr::chain::Chain>::into_pb"

/-- `<spqr::chain::Chain>::into_pb` frame (`0x120 = 288` B) + `dropStack32` (`32 + allocHookStack`). -/
abbrev chainIntoPbStack : Nat := 288 + dropStack32

/-- `<spqr::chain::Chain>::into_pb` frame (`0x120 = 288` B) + `extHookStack`. -/
abbrev chainIntoPbStackX : Nat := 288 + extHookStack

def toEpochDirectionPBGhost (g : ChainEpochDirectionGhost) : EpochDirectionPBGhost :=
  { next := ⟨g.next.cap, g.next.ptr⟩
    prev := ⟨g.prev.cap, g.prev.ptr⟩ }

def toChainEpochPBGhost (g : ChainEpochGhost) : ChainEpochPBGhost :=
  { send := toEpochDirectionPBGhost g.send
    recv := toEpochDirectionPBGhost g.recv }

def chainEpochIntoPb (ce : ChainEpoch) : ChainEpochPB :=
  { send := some ce.send.intoPb
    recv := some ce.recv.intoPb }

theorem chainIntoPb_links_eq (c : Chain) :
    c.intoPb.links = c.links.map chainEpochIntoPb := rfl

/-- Ghost arguments of `<spqr::chain::Chain>::into_pb` (`0x60514`). -/
structure ChainIntoPbCall where
  /-- Sret pointer `x8` (80-byte `pqrpb::Chain` output slot). -/
  out : BitVec 64
  /-- `self: Chain` pointer `x0` (88-byte input struct moved in by pointer). -/
  chainPtr : BitVec 64
  /-- Ghost pins of `self`. -/
  gChain : ChainGhost
  /-- Pure `Chain` value. -/
  chain : Chain

/-- Pinned spec of `<spqr::chain::Chain>::into_pb` (`0x60514`, 239 instructions) with tight stack
budget `chainIntoPbStack` (`288 + dropStack32`), preserving the per-epoch and `next_root` ghost
pins via `Top.ChainFrom.chainPBAt`. -/
def chainIntoPbPinnedSpec (A : RustAlloc) : Spec ChainIntoPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr⌝ ∗
      memRegion x.out 80 ∗ chainAt A x.chainPtr x.gChain x.chain ∗
      A.pool ∗ stackAt s.sp chainIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ linksPtr : BitVec 64,
        chainPBAt A
          ⟨BitVec.ofNat 64 x.chain.links.length, linksPtr,
            x.gChain.epochs.map toChainEpochPBGhost, x.gChain.nextRoot⟩
          x.out x.chain.intoPb) ∗
      memRegion x.chainPtr 88 ∗
      A.pool ∗ stackAt s0.sp chainIntoPbStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned `ProtoRepr.chainPBAt` spec of `<spqr::chain::Chain>::into_pb` (`0x60514`, 239 instructions)
with tight stack budget `chainIntoPbStack`. -/
def chainIntoPbSpec (A : RustAlloc) : Spec ChainIntoPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr⌝ ∗
      memRegion x.out 80 ∗ chainAt A x.chainPtr x.gChain x.chain ∗
      A.pool ∗ stackAt s.sp chainIntoPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A x.out x.chain.intoPb ∗
      memRegion x.chainPtr 88 ∗
      A.pool ∗ stackAt s0.sp chainIntoPbStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Pinned spec of `<spqr::chain::Chain>::into_pb` (`0x60514`, 239 instructions) with stack
budget `chainIntoPbStackX` (`288 + extHookStack`). -/
def chainIntoPbPinnedSpecX (A : RustAlloc) : Spec ChainIntoPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr⌝ ∗
      memRegion x.out 80 ∗ chainAt A x.chainPtr x.gChain x.chain ∗
      A.pool ∗ stackAt s.sp chainIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ linksPtr : BitVec 64,
        chainPBAt A
          ⟨BitVec.ofNat 64 x.chain.links.length, linksPtr,
            x.gChain.epochs.map toChainEpochPBGhost, x.gChain.nextRoot⟩
          x.out x.chain.intoPb) ∗
      memRegion x.chainPtr 88 ∗
      A.pool ∗ stackAt s0.sp chainIntoPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Unpinned `ProtoRepr.chainPBAt` spec of `<spqr::chain::Chain>::into_pb` (`0x60514`, 239 instructions)
with stack budget `chainIntoPbStackX` (`288 + extHookStack`). -/
def chainIntoPbSpecX (A : RustAlloc) : Spec ChainIntoPbCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.chainPtr⌝ ∗
      memRegion x.out 80 ∗ chainAt A x.chainPtr x.gChain x.chain ∗
      A.pool ∗ stackAt s.sp chainIntoPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.ProtoRepr.chainPBAt A x.out x.chain.intoPb ∗
      memRegion x.chainPtr 88 ∗
      A.pool ∗ stackAt s0.sp chainIntoPbStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def ChainIntoPbPinnedOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName)
    (chainIntoPbPinnedSpec A)

def ChainIntoPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr chainIntoPbName)
    (chainIntoPbSpec A)

def ChainIntoPbPinnedOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainIntoPbName)
    ((chainIntoPbPinnedSpecX A).inImage img)

def ChainIntoPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chainIntoPbName)
    ((chainIntoPbSpecX A).inImage img)

/-! ## Stride-112 Arithmetic and Magic Constant `0x2492492492492493#64` -/

theorem ofNat_len_ule_max_112 {n : Nat} (hn : n * 112 < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 n) 0x0124924924924924#64 = true := by
  have hn64 : n < 18446744073709551616 := by omega
  have hmax : (0x0124924924924924#64).toNat = 82351536043346212 := rfl
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64, hmax, decide_eq_true_eq]
  omega

theorem mul_112_beq_zero_false {n : Nat} (hne : n ≠ 0) (hn : n * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (n * 112) == 0#64) = false := by
  have hn64 : n * 112 < 18446744073709551616 := by omega
  rw [beq_eq_false_iff_ne]
  intro h0
  have htn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at htn
  omega

theorem ofNat_beq_zero_false_of_lt {n : Nat} (hne : n ≠ 0) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  have hn64 : n < 18446744073709551616 := by omega
  rw [beq_eq_false_iff_ne]
  intro h0
  have htn := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at htn
  omega

theorem ofNat_mul_112_sub_112_lsr_4 {n : Nat} (hpos : 1 ≤ n) (hn : n * 112 < 2 ^ 63) :
    ((BitVec.ofNat 64 (n * 112) - 112#64) >>> 4#64) =
      BitVec.ofNat 64 ((n - 1) * 7) := by
  have hn64 : n * 112 < 18446744073709551616 := by omega
  have hsub64 : (n - 1) * 112 < 18446744073709551616 := by omega
  have hk7 : (n - 1) * 7 < 18446744073709551616 := by omega
  change (BitVec.ofNat 64 (n * 112) - 112#64) >>> 4 = BitVec.ofNat 64 ((n - 1) * 7)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.shiftRight_eq_div_pow]
  have hsub : (18446744073709551616 - 112 + n * 112) % 18446744073709551616 = (n - 1) * 112 := by
    omega
  rw [hsub]
  omega

/-- LLVM magic-constant `umulh` division by 7 (`0x6062c` and `0x606f8`):
For `k * 112 < 2^63`, `umulh(k * 7, 0x2492492492492493) = k`. -/
theorem umulh_mul7_magic {k : Nat} (hk : k * 112 < 2 ^ 63) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (BitVec.ofNat 64 (k * 7)) *
        BitVec.zeroExtend 128 0x2492492492492493#64) >>> 64) =
      BitVec.ofNat 64 k := by
  have hk7 : k * 7 < 18446744073709551616 := by omega
  have hk64 : k < 18446744073709551616 := by omega
  have hm : (BitVec.zeroExtend 128 0x2492492492492493#64).toNat = 2635249153387078803 := rfl
  have hx128 : (BitVec.zeroExtend 128 (BitVec.ofNat 64 (k * 7))).toNat = k * 7 := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk7,
      Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hlt128 : k * 7 * 2635249153387078803 < 2 ^ 128 := by omega
  have hdiv : k * 7 * 2635249153387078803 / 2 ^ 64 = k := by omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, hx128, hm,
    Nat.mod_eq_of_lt hlt128, Nat.shiftRight_eq_div_pow, hdiv, BitVec.toNat_ofNat]

theorem umulh_div112_sub_112 {n : Nat} (hpos : 1 ≤ n) (hn : n * 112 < 2 ^ 63) :
    BitVec.truncate 64
      ((BitVec.zeroExtend 128 (((BitVec.ofNat 64 (n * 112) - 112#64) >>> 4#64)) *
        BitVec.zeroExtend 128 0x2492492492492493#64) >>> 64) =
      BitVec.ofNat 64 (n - 1) := by
  rw [ofNat_mul_112_sub_112_lsr_4 hpos hn]
  exact umulh_mul7_magic (by omega)

theorem ofNat_sub_one_add_one {n : Nat} (hpos : 1 ≤ n) :
    BitVec.ofNat 64 (n - 1) + 1#64 = BitVec.ofNat 64 n := by
  have heq : n = (n - 1) + 1 := by omega
  conv_rhs => rw [heq, BitVec.ofNat_add]

/-! ## 52-Byte 4-Byte-Shifted Cell Equality (`shift52_eq`) -/

def shift52_u0 (pad : BitVec 32) (w0 : BitVec 64) : BitVec 64 :=
  w0.extractLsb' 0 32 ++ pad

def shift52_u1 (w0 w1 : BitVec 64) : BitVec 64 :=
  w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32

def shift52_u2 (w1 w2 : BitVec 64) : BitVec 64 :=
  w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32

def shift52_u3 (w2 w3 : BitVec 64) : BitVec 64 :=
  w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32

def shift52_u4 (w3 w4 : BitVec 64) : BitVec 64 :=
  w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32

def shift52_u5 (w4 w5 : BitVec 64) : BitVec 64 :=
  w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32

def shift52_u6 (w5 : BitVec 64) : BitVec 32 :=
  w5.extractLsb' 32 32

theorem shift52_eq (a : BitVec 64) (pad : BitVec 32) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₃₂ pad) ∗
      ((a + 4#64) ↦₆₄ w0) ∗
      ((a + 12#64) ↦₆₄ w1) ∗
      ((a + 20#64) ↦₆₄ w2) ∗
      ((a + 28#64) ↦₆₄ w3) ∗
      ((a + 36#64) ↦₆₄ w4) ∗
      ((a + 44#64) ↦₆₄ w5) =
    (a ↦₆₄ shift52_u0 pad w0) ∗
      ((a + 8#64) ↦₆₄ shift52_u1 w0 w1) ∗
      ((a + 16#64) ↦₆₄ shift52_u2 w1 w2) ∗
      ((a + 24#64) ↦₆₄ shift52_u3 w2 w3) ∗
      ((a + 32#64) ↦₆₄ shift52_u4 w3 w4) ∗
      ((a + 40#64) ↦₆₄ shift52_u5 w4 w5) ∗
      ((a + 48#64) ↦₃₂ shift52_u6 w5) := by
  unfold shift52_u0 shift52_u1 shift52_u2 shift52_u3 shift52_u4 shift52_u5 shift52_u6
  rw [pointsTo64_split32 (a + 4#64) w0,
      pointsTo64_split32 (a + 12#64) w1,
      pointsTo64_split32 (a + 20#64) w2,
      pointsTo64_split32 (a + 28#64) w3,
      pointsTo64_split32 (a + 36#64) w4,
      pointsTo64_split32 (a + 44#64) w5,
      ← pointsTo32_pair a pad (w0.extractLsb' 0 32),
      ← pointsTo32_pair (a + 8#64) (w0.extractLsb' 32 32) (w1.extractLsb' 0 32),
      ← pointsTo32_pair (a + 16#64) (w1.extractLsb' 32 32) (w2.extractLsb' 0 32),
      ← pointsTo32_pair (a + 24#64) (w2.extractLsb' 32 32) (w3.extractLsb' 0 32),
      ← pointsTo32_pair (a + 32#64) (w3.extractLsb' 32 32) (w4.extractLsb' 0 32),
      ← pointsTo32_pair (a + 40#64) (w4.extractLsb' 32 32) (w5.extractLsb' 0 32)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem shift52_stack_eq (sp : BitVec 64) (pad : BitVec 32) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 260#64) ↦₃₂ pad) ∗
      ((sp - 256#64) ↦₆₄ w0) ∗
      ((sp - 248#64) ↦₆₄ w1) ∗
      ((sp - 240#64) ↦₆₄ w2) ∗
      ((sp - 232#64) ↦₆₄ w3) ∗
      ((sp - 224#64) ↦₆₄ w4) ∗
      ((sp - 216#64) ↦₆₄ w5) =
    ((sp - 260#64) ↦₆₄ shift52_u0 pad w0) ∗
      ((sp - 252#64) ↦₆₄ shift52_u1 w0 w1) ∗
      ((sp - 244#64) ↦₆₄ shift52_u2 w1 w2) ∗
      ((sp - 236#64) ↦₆₄ shift52_u3 w2 w3) ∗
      ((sp - 228#64) ↦₆₄ shift52_u4 w3 w4) ∗
      ((sp - 220#64) ↦₆₄ shift52_u5 w4 w5) ∗
      ((sp - 212#64) ↦₃₂ shift52_u6 w5) := by
  have h := shift52_eq (sp - 260#64) pad w0 w1 w2 w3 w4 w5
  simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg] using h

theorem shift52_dst_eq (dst : BitVec 64) (pad : BitVec 32) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((dst + 52#64) ↦₆₄ shift52_u0 pad w0) ∗
      ((dst + 60#64) ↦₆₄ shift52_u1 w0 w1) ∗
      ((dst + 68#64) ↦₆₄ shift52_u2 w1 w2) ∗
      ((dst + 76#64) ↦₆₄ shift52_u3 w2 w3) ∗
      ((dst + 84#64) ↦₆₄ shift52_u4 w3 w4) ∗
      ((dst + 92#64) ↦₆₄ shift52_u5 w4 w5) ∗
      ((dst + 100#64) ↦₃₂ shift52_u6 w5) =
    ((dst + 52#64) ↦₃₂ pad) ∗
      ((dst + 56#64) ↦₆₄ w0) ∗
      ((dst + 64#64) ↦₆₄ w1) ∗
      ((dst + 72#64) ↦₆₄ w2) ∗
      ((dst + 80#64) ↦₆₄ w3) ∗
      ((dst + 88#64) ↦₆₄ w4) ∗
      ((dst + 96#64) ↦₆₄ w5) := by
  have h := (shift52_eq (dst + 52#64) pad w0 w1 w2 w3 w4 w5).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-! ## Loop-Element (`chainEpochAt` / `chainEpochPBAt`) Unpack and Repack Bridges -/

theorem chainEpochDirectionAt_eq_epochDirectionPBAt (A : RustAlloc)
    (a : BitVec 64) (g : ChainEpochDirectionGhost) (d : ChainEpochDirection) :
    chainEpochDirectionAt A a g d =
      epochDirectionPBAt A (toEpochDirectionPBGhost g) a d.intoPb := rfl

theorem chainEpochAt_eq_chainEpochPBAt (A : RustAlloc)
    (g : ChainEpochGhost) (ce : ChainEpoch) (a : BitVec 64) :
    chainEpochAt A (g, ce) a =
      chainEpochPBAt A (toChainEpochPBGhost g, chainEpochIntoPb ce) a := rfl

/-- Unpack `chainEpochAt A (g, ce) src` into all 14 word/dword cells at `src` plus the 4 `vecU8BufAt`
heap buffers and the two 4-byte padding regions. -/
theorem chainEpochAt_unpack_cells (A : RustAlloc) (g : ChainEpochGhost) (ce : ChainEpoch)
    (src : BitVec 64) :
    chainEpochAt A (g, ce) src ⊢
      ⌜ce.send.next.length ≤ g.send.next.cap.toNat ∧ g.send.next.cap.toNat < 2 ^ 63 ∧
        g.send.next.ptr ≠ 0 ∧ ce.send.prev.data.length ≤ g.send.prev.cap.toNat ∧
        g.send.prev.cap.toNat < 2 ^ 63 ∧ g.send.prev.ptr ≠ 0 ∧
        ce.recv.next.length ≤ g.recv.next.cap.toNat ∧ g.recv.next.cap.toNat < 2 ^ 63 ∧
        g.recv.next.ptr ≠ 0 ∧ ce.recv.prev.data.length ≤ g.recv.prev.cap.toNat ∧
        g.recv.prev.cap.toNat < 2 ^ 63 ∧ g.recv.prev.ptr ≠ 0⌝ ∗
      (src ↦₆₄ g.send.next.cap) ∗ ((src + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((src + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      ((src + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((src + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((src + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
      ((src + 48#64) ↦₃₂ ce.send.ctr) ∗ memRegion (src + 52#64) 4 ∗
      ((src + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((src + 64#64) ↦₆₄ g.recv.next.ptr) ∗
      ((src + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
      ((src + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((src + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
      ((src + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length) ∗
      ((src + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (src + 108#64) 4 ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data := by
  rw [chainEpochAt_eq_chainEpochPBAt]
  dsimp only [chainEpochPBAt, CryptoVerification.SpqrV1.ProtoRepr.chainEpochPBPinnedAt,
    toChainEpochPBGhost, chainEpochIntoPb]
  refine Entails.trans
    (sepConj_mono
      (optEpochDirectionPBAt_some_unpack A (toEpochDirectionPBGhost g.send) src ce.send.intoPb)
      (optEpochDirectionPBAt_some_unpack A (toEpochDirectionPBGhost g.recv) (src + 56#64) ce.recv.intoPb)) ?_
  unfold epochDirPBCellsAt toEpochDirectionPBGhost ChainEpochDirection.intoPb
  dsimp only
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [show
    (⌜ce.send.next.length ≤ g.send.next.cap.toNat ∧ g.send.next.cap.toNat < 2 ^ 63 ∧
        g.send.next.ptr ≠ 0 ∧ ce.send.prev.data.length ≤ g.send.prev.cap.toNat ∧
        g.send.prev.cap.toNat < 2 ^ 63 ∧ g.send.prev.ptr ≠ 0⌝ ∗
      (src ↦₆₄ g.send.next.cap ∗ (src + 8#64) ↦₆₄ g.send.next.ptr ∗
        (src + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length ∗
        (src + 24#64) ↦₆₄ g.send.prev.cap ∗ (src + 32#64) ↦₆₄ g.send.prev.ptr ∗
        (src + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length ∗
        (src + 48#64) ↦₃₂ ce.send.ctr ∗ memRegion (src + 52#64) 4) ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data) ∗
    (⌜ce.recv.next.length ≤ g.recv.next.cap.toNat ∧ g.recv.next.cap.toNat < 2 ^ 63 ∧
        g.recv.next.ptr ≠ 0 ∧ ce.recv.prev.data.length ≤ g.recv.prev.cap.toNat ∧
        g.recv.prev.cap.toNat < 2 ^ 63 ∧ g.recv.prev.ptr ≠ 0⌝ ∗
      ((src + 56#64) ↦₆₄ g.recv.next.cap ∗ (src + 64#64) ↦₆₄ g.recv.next.ptr ∗
        (src + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length ∗
        (src + 80#64) ↦₆₄ g.recv.prev.cap ∗ (src + 88#64) ↦₆₄ g.recv.prev.ptr ∗
        (src + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length ∗
        (src + 104#64) ↦₃₂ ce.recv.ctr ∗ memRegion (src + 108#64) 4) ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data) =
    ⌜ce.send.next.length ≤ g.send.next.cap.toNat ∧ g.send.next.cap.toNat < 2 ^ 63 ∧
        g.send.next.ptr ≠ 0 ∧ ce.send.prev.data.length ≤ g.send.prev.cap.toNat ∧
        g.send.prev.cap.toNat < 2 ^ 63 ∧ g.send.prev.ptr ≠ 0⌝ ∗
    ⌜ce.recv.next.length ≤ g.recv.next.cap.toNat ∧ g.recv.next.cap.toNat < 2 ^ 63 ∧
        g.recv.next.ptr ≠ 0 ∧ ce.recv.prev.data.length ≤ g.recv.prev.cap.toNat ∧
        g.recv.prev.cap.toNat < 2 ^ 63 ∧ g.recv.prev.ptr ≠ 0⌝ ∗
    (src ↦₆₄ g.send.next.cap ∗ (src + 8#64) ↦₆₄ g.send.next.ptr ∗
      (src + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length ∗
      (src + 24#64) ↦₆₄ g.send.prev.cap ∗ (src + 32#64) ↦₆₄ g.send.prev.ptr ∗
      (src + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length ∗
      (src + 48#64) ↦₃₂ ce.send.ctr ∗ memRegion (src + 52#64) 4 ∗
      (src + 56#64) ↦₆₄ g.recv.next.cap ∗ (src + 64#64) ↦₆₄ g.recv.next.ptr ∗
      (src + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length ∗
      (src + 80#64) ↦₆₄ g.recv.prev.cap ∗ (src + 88#64) ↦₆₄ g.recv.prev.ptr ∗
      (src + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length ∗
      (src + 104#64) ↦₃₂ ce.recv.ctr ∗ memRegion (src + 108#64) 4 ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data) by ac_rfl]
  refine Entails.pure_left fun ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ => ?_
  refine Entails.pure_left fun ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ => ?_
  exact Entails.pure_right ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
    (Entails.refl _)

/-- Fold the 14 read cells + 2 padding regions at `src` back into `memRegion src 112`. -/
theorem chainEpochSrcCells_entails_memRegion_112 (src : BitVec 64)
    (w0 w1 w2 w3 w4 w5 r0 r1 r2 r3 r4 r5 : BitVec 64) (c0 c1 : BitVec 32) :
    (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
      ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗
      ((src + 48#64) ↦₃₂ c0) ∗ memRegion (src + 52#64) 4 ∗
      ((src + 56#64) ↦₆₄ r0) ∗ ((src + 64#64) ↦₆₄ r1) ∗ ((src + 72#64) ↦₆₄ r2) ∗
      ((src + 80#64) ↦₆₄ r3) ∗ ((src + 88#64) ↦₆₄ r4) ∗ ((src + 96#64) ↦₆₄ r5) ∗
      ((src + 104#64) ↦₃₂ c1) ∗ memRegion (src + 108#64) 4 ⊢
      memRegion src 112 := by
  have hs := epochDirPBCellsAt_entails_memRegion_56 src ⟨⟨w0, w1⟩, ⟨w3, w4⟩⟩
    ⟨c0, List.replicate w2.toNat 0, List.replicate w5.toNat 0⟩
  have hr := epochDirPBCellsAt_entails_memRegion_56 (src + 56#64) ⟨⟨r0, r1⟩, ⟨r3, r4⟩⟩
    ⟨c1, List.replicate r2.toNat 0, List.replicate r5.toNat 0⟩
  unfold epochDirPBCellsAt at hs hr
  dsimp only at hs hr
  simp only [List.length_replicate, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_assoc, BitVec.reduceAdd] at hs hr
  refine Entails.trans ?_ (memRegion_56_56_to_112 src)
  rw [show
    (src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
      ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗
      ((src + 48#64) ↦₃₂ c0) ∗ memRegion (src + 52#64) 4 ∗
      ((src + 56#64) ↦₆₄ r0) ∗ ((src + 64#64) ↦₆₄ r1) ∗ ((src + 72#64) ↦₆₄ r2) ∗
      ((src + 80#64) ↦₆₄ r3) ∗ ((src + 88#64) ↦₆₄ r4) ∗ ((src + 96#64) ↦₆₄ r5) ∗
      ((src + 104#64) ↦₃₂ c1) ∗ memRegion (src + 108#64) 4 =
    ((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
      ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₆₄ w4) ∗ ((src + 40#64) ↦₆₄ w5) ∗
      ((src + 48#64) ↦₃₂ c0) ∗ memRegion (src + 52#64) 4) ∗
    (((src + 56#64) ↦₆₄ r0) ∗ ((src + 64#64) ↦₆₄ r1) ∗ ((src + 72#64) ↦₆₄ r2) ∗
      ((src + 80#64) ↦₆₄ r3) ∗ ((src + 88#64) ↦₆₄ r4) ∗ ((src + 96#64) ↦₆₄ r5) ∗
      ((src + 104#64) ↦₃₂ c1) ∗ memRegion (src + 108#64) 4) by ac_rfl]
  exact sepConj_mono hs hr

/-- Split `memRegion dst 112` into the exact cells written by the loop body at `dst`. -/
theorem memRegion_112_split_dst (dst : BitVec 64) :
    memRegion dst 112 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (dst + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (dst + 32#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (dst + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 32, (dst + 48#64) ↦₃₂ d6) ∗ (∃∗ u0 : BitVec 64, (dst + 52#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (dst + 60#64) ↦₆₄ u1) ∗ (∃∗ u2 : BitVec 64, (dst + 68#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (dst + 76#64) ↦₆₄ u3) ∗ (∃∗ u4 : BitVec 64, (dst + 84#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (dst + 92#64) ↦₆₄ u5) ∗ (∃∗ u6 : BitVec 32, (dst + 100#64) ↦₃₂ u6) ∗
      (∃∗ u7 : BitVec 32, (dst + 104#64) ↦₃₂ u7) ∗ memRegion (dst + 108#64) 4 := by
  rw [ProofLib.memRegion_split' (b := dst) (n := 8) (k := 104) (b' := dst + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := dst + 8#64) (n := 8) (k := 96) (b' := dst + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 16#64) (n := 8) (k := 88) (b' := dst + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 24#64) (n := 8) (k := 80) (b' := dst + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 32#64) (n := 8) (k := 72) (b' := dst + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 40#64) (n := 8) (k := 64) (b' := dst + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 48#64) (n := 4) (k := 60) (b' := dst + 52#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 52#64) (n := 8) (k := 52) (b' := dst + 60#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 60#64) (n := 8) (k := 44) (b' := dst + 68#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 68#64) (n := 8) (k := 36) (b' := dst + 76#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 76#64) (n := 8) (k := 28) (b' := dst + 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 84#64) (n := 8) (k := 20) (b' := dst + 92#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 92#64) (n := 8) (k := 12) (b' := dst + 100#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 100#64) (n := 4) (k := 8) (b' := dst + 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := dst + 104#64) (n := 4) (k := 4) (b' := dst + 108#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight dst, ProofLib.memRegion_eight (dst + 8#64),
      ProofLib.memRegion_eight (dst + 16#64), ProofLib.memRegion_eight (dst + 24#64),
      ProofLib.memRegion_eight (dst + 32#64), ProofLib.memRegion_eight (dst + 40#64),
      ProofLib.memRegion_four (dst + 48#64), ProofLib.memRegion_eight (dst + 52#64),
      ProofLib.memRegion_eight (dst + 60#64), ProofLib.memRegion_eight (dst + 68#64),
      ProofLib.memRegion_eight (dst + 76#64), ProofLib.memRegion_eight (dst + 84#64),
      ProofLib.memRegion_eight (dst + 92#64), ProofLib.memRegion_four (dst + 100#64),
      ProofLib.memRegion_four (dst + 104#64)]

/-- Repack the written cells at `dst` (using `shift52_dst_eq`) plus the 4 `vecU8BufAt` buffers
into `chainEpochPBAt A (toChainEpochPBGhost g, chainEpochIntoPb ce) dst`. -/
theorem chainEpochPBAt_repack_dst (A : RustAlloc) (dst : BitVec 64)
    (g : ChainEpochGhost) (ce : ChainEpoch) (pad : BitVec 32)
    (hs1 : ce.send.next.length ≤ g.send.next.cap.toNat) (hs2 : g.send.next.cap.toNat < 2 ^ 63)
    (hs3 : g.send.next.ptr ≠ 0) (hs4 : ce.send.prev.data.length ≤ g.send.prev.cap.toNat)
    (hs5 : g.send.prev.cap.toNat < 2 ^ 63) (hs6 : g.send.prev.ptr ≠ 0)
    (hr1 : ce.recv.next.length ≤ g.recv.next.cap.toNat) (hr2 : g.recv.next.cap.toNat < 2 ^ 63)
    (hr3 : g.recv.next.ptr ≠ 0) (hr4 : ce.recv.prev.data.length ≤ g.recv.prev.cap.toNat)
    (hr5 : g.recv.prev.cap.toNat < 2 ^ 63) (hr6 : g.recv.prev.ptr ≠ 0) :
    (dst ↦₆₄ g.send.next.cap) ∗ ((dst + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      ((dst + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((dst + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
      ((dst + 48#64) ↦₃₂ ce.send.ctr) ∗
      (((dst + 52#64) ↦₆₄ shift52_u0 pad g.recv.next.cap) ∗
        ((dst + 60#64) ↦₆₄ shift52_u1 g.recv.next.cap g.recv.next.ptr) ∗
        ((dst + 68#64) ↦₆₄ shift52_u2 g.recv.next.ptr (BitVec.ofNat 64 ce.recv.next.length)) ∗
        ((dst + 76#64) ↦₆₄ shift52_u3 (BitVec.ofNat 64 ce.recv.next.length) g.recv.prev.cap) ∗
        ((dst + 84#64) ↦₆₄ shift52_u4 g.recv.prev.cap g.recv.prev.ptr) ∗
        ((dst + 92#64) ↦₆₄ shift52_u5 g.recv.prev.ptr (BitVec.ofNat 64 ce.recv.prev.data.length)) ∗
        ((dst + 100#64) ↦₃₂ shift52_u6 (BitVec.ofNat 64 ce.recv.prev.data.length))) ∗
      ((dst + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (dst + 108#64) 4 ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data ⊢
      chainEpochPBAt A (toChainEpochPBGhost g, chainEpochIntoPb ce) dst := by
  rw [shift52_dst_eq dst pad g.recv.next.cap g.recv.next.ptr
      (BitVec.ofNat 64 ce.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
      (BitVec.ofNat 64 ce.recv.prev.data.length),
    ← chainEpochAt_eq_chainEpochPBAt]
  have hpad : ((dst + 52#64) ↦₃₂ pad) ⊢ memRegion (dst + 52#64) 4 :=
    ProofLib.pointsTo32_entails_memRegion (dst + 52#64) pad
  have hsend := epochDirPBCellsAt_repack_ced A dst (toEpochDirectionPBGhost g.send) ce.send.intoPb
    hs1 hs2 hs3 hs4 hs5 hs6
  have hrecv := epochDirPBCellsAt_repack_ced A (dst + 56#64) (toEpochDirectionPBGhost g.recv) ce.recv.intoPb
    hr1 hr2 hr3 hr4 hr5 hr6
  unfold epochDirPBCellsAt toEpochDirectionPBGhost toChainEpochDirectionGhost
    ChainEpochDirection.intoPb at hsend hrecv
  dsimp only at hsend hrecv
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsend hrecv
  unfold chainEpochAt
  dsimp only
  rw [show
    (dst ↦₆₄ g.send.next.cap) ∗ ((dst + 8#64) ↦₆₄ g.send.next.ptr) ∗
      ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
      ((dst + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((dst + 32#64) ↦₆₄ g.send.prev.ptr) ∗
      ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
      ((dst + 48#64) ↦₃₂ ce.send.ctr) ∗
      (((dst + 52#64) ↦₃₂ pad) ∗ ((dst + 56#64) ↦₆₄ g.recv.next.cap) ∗
        ((dst + 64#64) ↦₆₄ g.recv.next.ptr) ∗
        ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
        ((dst + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((dst + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
        ((dst + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length)) ∗
      ((dst + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (dst + 108#64) 4 ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data =
    (((dst ↦₆₄ g.send.next.cap) ∗ ((dst + 8#64) ↦₆₄ g.send.next.ptr) ∗
        ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 ce.send.next.length) ∗
        ((dst + 24#64) ↦₆₄ g.send.prev.cap) ∗ ((dst + 32#64) ↦₆₄ g.send.prev.ptr) ∗
        ((dst + 40#64) ↦₆₄ BitVec.ofNat 64 ce.send.prev.data.length) ∗
        ((dst + 48#64) ↦₃₂ ce.send.ctr) ∗ ((dst + 52#64) ↦₃₂ pad)) ∗
      vecU8BufAt A g.send.next.cap g.send.next.ptr ce.send.next ∗
      vecU8BufAt A g.send.prev.cap g.send.prev.ptr ce.send.prev.data) ∗
    ((((dst + 56#64) ↦₆₄ g.recv.next.cap) ∗ ((dst + 64#64) ↦₆₄ g.recv.next.ptr) ∗
        ((dst + 72#64) ↦₆₄ BitVec.ofNat 64 ce.recv.next.length) ∗
        ((dst + 80#64) ↦₆₄ g.recv.prev.cap) ∗ ((dst + 88#64) ↦₆₄ g.recv.prev.ptr) ∗
        ((dst + 96#64) ↦₆₄ BitVec.ofNat 64 ce.recv.prev.data.length) ∗
        ((dst + 104#64) ↦₃₂ ce.recv.ctr) ∗ memRegion (dst + 108#64) 4) ∗
      vecU8BufAt A g.recv.next.cap g.recv.next.ptr ce.recv.next ∗
      vecU8BufAt A g.recv.prev.cap g.recv.prev.ptr ce.recv.prev.data) by ac_rfl]
  refine sepConj_mono ?_ hrecv
  refine Entails.trans ?_ hsend
  exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hpad)))))))

theorem arrayAt_chainEpochPBAt_snoc (A : RustAlloc) (ptr : BitVec 64)
    (prefG : List ChainEpochGhost) (pref : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (hlen : prefG.length = pref.length) :
    arrayAt (chainEpochPBAt A) 112 ptr
        ((prefG.map toChainEpochPBGhost).zip (pref.map chainEpochIntoPb)) ∗
      chainEpochPBAt A (toChainEpochPBGhost g, chainEpochIntoPb ep)
        (ptr + BitVec.ofNat 64 (pref.length * 112)) ⊢
      arrayAt (chainEpochPBAt A) 112 ptr
        (((prefG ++ [g]).map toChainEpochPBGhost).zip ((pref ++ [ep]).map chainEpochIntoPb)) := by
  have h1 := arrayAt_chainEpochAt_snoc A ptr prefG pref g ep hlen
  have hconv : ∀ (gs : List ChainEpochGhost) (es : List ChainEpoch) (base : BitVec 64),
      arrayAt (chainEpochPBAt A) 112 base
        ((gs.map toChainEpochPBGhost).zip (es.map chainEpochIntoPb)) =
      arrayAt (chainEpochAt A) 112 base (gs.zip es) := by
    intro gs
    induction gs with
    | nil => intro es base; simp [arrayAt]
    | cons g0 gst ih =>
      intro es base
      cases es with
      | nil => simp [arrayAt]
      | cons e0 est =>
        change chainEpochPBAt A (toChainEpochPBGhost g0, chainEpochIntoPb e0) base ∗
            arrayAt (chainEpochPBAt A) 112 (base + 112#64)
              ((gst.map toChainEpochPBGhost).zip (est.map chainEpochIntoPb)) =
          chainEpochAt A (g0, e0) base ∗ arrayAt (chainEpochAt A) 112 (base + 112#64) (gst.zip est)
        rw [← chainEpochAt_eq_chainEpochPBAt A g0 e0 base, ih est (base + 112#64)]
  rw [hconv prefG pref ptr, hconv (prefG ++ [g]) (pref ++ [ep]) ptr,
      ← chainEpochAt_eq_chainEpochPBAt A g ep]
  exact h1

/-! ## `chainAt` and `vecDequeRingBuf` Unpacking and `chainPBAt` Packing -/

/-- All 88 bytes of `Chain` header cells at `a`. -/
def chainHeaderCellsAt (a : BitVec 64) (g : ChainGhost) (c : Chain) : SepProp :=
  (a ↦₆₄ g.linksCap) ∗ ((a + 8#64) ↦₆₄ g.linksPtr) ∗
  ((a + 16#64) ↦₆₄ g.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
  ((a + 32#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ g.nextRoot.ptr) ∗
  ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
  ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
  ((a + 72#64) ↦₃₂ c.params.maxJump) ∗ ((a + 76#64) ↦₃₂ c.params.maxOooKeys) ∗
  ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ memRegion (a + 84#64) 4

theorem chainHeaderCellsAt_entails_memRegion_88 (a : BitVec 64) (g : ChainGhost) (c : Chain) :
    chainHeaderCellsAt a g c ⊢ memRegion a 88 := by
  unfold chainHeaderCellsAt
  have htl := chainTail_entails_memRegion_32 a c
  unfold chainParamsAt directionAt at htl
  have hp : (a + 72#64) + 4#64 = a + 76#64 := by bv_omega
  rw [hp] at htl
  have hnr : ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ⊢ memRegion (a + 48#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion _ _
  have h40 :
      ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        (((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
          (((a + 72#64) ↦₃₂ c.params.maxJump) ∗ ((a + 76#64) ↦₃₂ c.params.maxOooKeys)) ∗
          ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ memRegion (a + 84#64) 4) ⊢
      memRegion (a + 48#64) 40 := by
    rw [ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 32)
          (b' := a + 56#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hnr htl
  refine Entails.trans ?_ (chainHeaders_entails_memRegion_88 a g.linksCap g.linksPtr g.linksHead
    (BitVec.ofNat 64 c.links.length) g.nextRoot.cap g.nextRoot.ptr)
  unfold vecDequeHeader
  rw [show
    (a ↦₆₄ g.linksCap) ∗ ((a + 8#64) ↦₆₄ g.linksPtr) ∗ ((a + 16#64) ↦₆₄ g.linksHead) ∗
      ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.cap) ∗
      ((a + 40#64) ↦₆₄ g.nextRoot.ptr) ∗ ((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
      ((a + 72#64) ↦₃₂ c.params.maxJump) ∗ ((a + 76#64) ↦₃₂ c.params.maxOooKeys) ∗
      ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ memRegion (a + 84#64) 4 =
    ((a ↦₆₄ g.linksCap) ∗ ((a + 8#64) ↦₆₄ g.linksPtr) ∗ ((a + 16#64) ↦₆₄ g.linksHead) ∗
      ((a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length)) ∗
    ((a + 32#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ g.nextRoot.ptr) ∗
    (((a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      (((a + 56#64) ↦₆₄ c.currentEpoch) ∗ ((a + 64#64) ↦₆₄ c.sendEpoch) ∗
        (((a + 72#64) ↦₃₂ c.params.maxJump) ∗ ((a + 76#64) ↦₃₂ c.params.maxOooKeys)) ∗
        ((a + 80#64) ↦₃₂ c.dir.toI32) ∗ memRegion (a + 84#64) 4)) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h40))

/-- Unpack `chainAt A a g c` into `chainHeaderCellsAt a g c`, `vecDequeRingBuf`, and `vecU8BufAt`. -/
theorem chainAt_unpack (A : RustAlloc) (a : BitVec 64) (g : ChainGhost) (c : Chain) :
    chainAt A a g c ⊢
      ⌜g.epochs.length = c.links.length ∧ c.links.length ≤ g.linksCap.toNat ∧
        g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0 ∧
        (if g.linksCap = 0 then g.linksHead = 0 else g.linksHead.toNat < g.linksCap.toNat) ∧
        c.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
        g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
      chainHeaderCellsAt a g c ∗
      (if g.linksCap = 0 then emp
       else A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
         vecDequeSlotsAt (chainEpochAt A) 112 g.linksCap.toNat g.linksHead.toNat
           g.linksPtr (g.epochs.zip c.links) 0 g.linksCap.toNat) ∗
      vecU8BufAt A g.nextRoot.cap g.nextRoot.ptr c.nextRoot := by
  unfold chainAt vecDequeAt vecDequeHeader vecDequeRingBuf vecU8At vecHeader
    chainParamsAt directionAt chainHeaderCellsAt vecU8BufAt chainEpochSize chainEpochAlign
  refine Entails.pure_left fun hlen => ?_
  have hzlen : (g.epochs.zip c.links).length = c.links.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  rw [hzlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [show
    ((a ↦₆₄ g.linksCap ∗ (a + 8#64) ↦₆₄ g.linksPtr ∗ (a + 16#64) ↦₆₄ g.linksHead ∗
        (a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      ⌜c.links.length ≤ g.linksCap.toNat ∧ g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0 ∧
          if g.linksCap = 0 then g.linksHead = 0 else g.linksHead.toNat < g.linksCap.toNat⌝ ∗
      if g.linksCap = 0 then emp
      else A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 g.linksCap.toNat g.linksHead.toNat g.linksPtr
          (g.epochs.zip c.links) 0 g.linksCap.toNat) ∗
    (((a + 32#64) ↦₆₄ g.nextRoot.cap ∗ (a + 40#64) ↦₆₄ g.nextRoot.ptr ∗
        (a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ⌜c.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
      if g.nextRoot.cap = 0 then emp
      else A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
        memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
          (g.nextRoot.cap.toNat - c.nextRoot.length)) ∗
    (a + 56#64) ↦₆₄ c.currentEpoch ∗ (a + 64#64) ↦₆₄ c.sendEpoch ∗
    ((a + 72#64) ↦₃₂ c.params.maxJump ∗ (a + 76#64) ↦₃₂ c.params.maxOooKeys) ∗
    (a + 80#64) ↦₃₂ c.dir.toI32 ∗ memRegion (a + 84#64) 4 =
    ⌜c.links.length ≤ g.linksCap.toNat ∧ g.linksCap.toNat * 112 < 2 ^ 63 ∧ g.linksPtr ≠ 0 ∧
        if g.linksCap = 0 then g.linksHead = 0 else g.linksHead.toNat < g.linksCap.toNat⌝ ∗
    ⌜c.nextRoot.length ≤ g.nextRoot.cap.toNat ∧ g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
    ((a ↦₆₄ g.linksCap ∗ (a + 8#64) ↦₆₄ g.linksPtr ∗ (a + 16#64) ↦₆₄ g.linksHead ∗
        (a + 24#64) ↦₆₄ BitVec.ofNat 64 c.links.length ∗ (a + 32#64) ↦₆₄ g.nextRoot.cap ∗
        (a + 40#64) ↦₆₄ g.nextRoot.ptr ∗ (a + 48#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length ∗
        (a + 56#64) ↦₆₄ c.currentEpoch ∗ (a + 64#64) ↦₆₄ c.sendEpoch ∗
        (a + 72#64) ↦₃₂ c.params.maxJump ∗ (a + 76#64) ↦₃₂ c.params.maxOooKeys ∗
        (a + 80#64) ↦₃₂ c.dir.toI32 ∗ memRegion (a + 84#64) 4) ∗
      (if g.linksCap = 0 then emp
       else A.live g.linksPtr (g.linksCap.toNat * 112) 8 ∗
         vecDequeSlotsAt (chainEpochAt A) 112 g.linksCap.toNat g.linksHead.toNat g.linksPtr
           (g.epochs.zip c.links) 0 g.linksCap.toNat) ∗
      (if g.nextRoot.cap = 0 then emp
       else A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
         memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
           (g.nextRoot.cap.toNat - c.nextRoot.length))) by ac_rfl]
  refine Entails.pure_left fun ⟨hl1, hl2, hl3, hl4⟩ => ?_
  refine Entails.pure_left fun ⟨hn1, hn2, hn3⟩ => ?_
  exact Entails.pure_right ⟨hlen, hl1, hl2, hl3, hl4, hn1, hn2, hn3⟩ (Entails.refl _)

/-- When `c.links = []`, the old `VecDeque` buffer is immediately ready for deallocation. -/
theorem vecDequeSlots_nil_entails_dealloc (A : RustAlloc)
    (cap ptr head : BitVec 64) (epochs : List ChainEpochGhost) (links : List ChainEpoch)
    (hnil : links = []) (hcap_lt : cap.toNat * 112 < 2 ^ 63) :
    (if cap = 0 then emp
     else A.live ptr (cap.toNat * 112) 8 ∗
       vecDequeSlotsAt (chainEpochAt A) 112 cap.toNat head.toNat ptr (epochs.zip links) 0 cap.toNat) ⊢
    if (cap == 0#64) = true then emp
    else A.live ptr (cap.toNat * 112) 8 ∗ memRegion ptr (cap.toNat * 112) := by
  subst hnil
  rw [List.zip_nil_right]
  by_cases hc : cap = 0
  · subst hc; simp only [↓reduceIte, beq_self_eq_true]; exact Entails.refl _
  · have hcb : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
    simp only [hc, hcb, ↓reduceIte, Bool.false_eq_true]
    exact sepConj_mono_right
      (vecDequeSlotsAt_nil_entails_memRegion (chainEpochAt A) 112 cap.toNat head.toNat ptr hcap_lt)

/-- Non-wrapping `VecDeque` slot decomposition (`xs.length ≤ cap - head`). -/
theorem vecDequeSlots_nonwrap_split (A : RustAlloc)
    (cap head : Nat) (ptr : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    (hcap_lt : cap * 112 < 2 ^ 63) (hhead_lt : head < cap) (hlen_le : xs.length ≤ cap - head) :
    vecDequeSlotsAt (chainEpochAt A) 112 cap head ptr xs 0 cap ⊢
      arrayAt (chainEpochAt A) 112 (ptr + BitVec.ofNat 64 (head * 112)) xs ∗
      memRegion ptr (head * 112) ∗
      memRegion (ptr + BitVec.ofNat 64 ((head + xs.length) * 112)) ((cap - head - xs.length) * 112) := by
  have hsplit : cap = head + (xs.length + (cap - head - xs.length)) := by omega
  have hunocc1 : ∀ k < head, ¬(vecDequeLogIdx head cap (0 + k) < xs.length) := by
    intro k hk; unfold vecDequeLogIdx; split <;> omega
  have hunocc2 : ∀ k < cap - head - xs.length,
      ¬(vecDequeLogIdx head cap ((head + xs.length) + k) < xs.length) := by
    intro k hk; unfold vecDequeLogIdx; split <;> omega
  have h1 := vecDequeSlotsAt_unoccupied_entails_memRegion (chainEpochAt A) 112 cap head ptr xs
    head 0 (by omega) hunocc1
  have h3 := vecDequeSlotsAt_unoccupied_entails_memRegion (chainEpochAt A) 112 cap head ptr xs
    (cap - head - xs.length) (head + xs.length) (by omega) hunocc2
  simp only [Nat.zero_mul, BitVec.add_zero] at h1
  have h2 :
      vecDequeSlotsAt (chainEpochAt A) 112 cap head ptr xs head xs.length =
        arrayAt (chainEpochAt A) 112 (ptr + BitVec.ofNat 64 (head * 112)) xs := by
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap head ptr xs
      head 0 xs.length (by omega) (by intro k _; unfold vecDequeLogIdx; split <;> omega)]
    simp
  conv_lhs => arg 8; rw [hsplit]
  rw [vecDequeSlotsAt_add (chainEpochAt A) 112 cap head ptr xs 0 head (xs.length + (cap - head - xs.length)),
      Nat.zero_add,
      vecDequeSlotsAt_add (chainEpochAt A) 112 cap head ptr xs head xs.length (cap - head - xs.length),
      h2]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right h3)) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Wrapping `VecDeque` slot decomposition (`cap - head < xs.length`). -/
theorem vecDequeSlots_wrap_split (A : RustAlloc)
    (cap head : Nat) (ptr : BitVec 64) (xs : List (ChainEpochGhost × ChainEpoch))
    (hcap_lt : cap * 112 < 2 ^ 63) (hhead_lt : head < cap)
    (hlen_le : xs.length ≤ cap) (hlen_gt : cap - head < xs.length) :
    vecDequeSlotsAt (chainEpochAt A) 112 cap head ptr xs 0 cap ⊢
      arrayAt (chainEpochAt A) 112 (ptr + BitVec.ofNat 64 (head * 112)) (xs.take (cap - head)) ∗
      arrayAt (chainEpochAt A) 112 ptr (xs.drop (cap - head)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length - (cap - head)) * 112))
        ((head - (xs.length - (cap - head))) * 112) := by
  let m₂ := xs.length - (cap - head)
  have hm2_le : m₂ ≤ head := by omega
  have hsplit : cap = m₂ + ((head - m₂) + (cap - head)) := by omega
  have hunocc : ∀ k < head - m₂, ¬(vecDequeLogIdx head cap (m₂ + k) < xs.length) := by
    intro k hk; unfold vecDequeLogIdx; split <;> omega
  have hmid := vecDequeSlotsAt_unoccupied_entails_memRegion (chainEpochAt A) 112 cap head ptr xs
    (head - m₂) m₂ (by omega) hunocc
  have hback :
      vecDequeSlotsAt (chainEpochAt A) 112 cap head ptr xs 0 m₂ =
        arrayAt (chainEpochAt A) 112 ptr (xs.drop (cap - head)) := by
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap head ptr xs
      0 (cap - head) m₂ (by omega) (by intro k hk; unfold vecDequeLogIdx; split <;> omega)]
    have htake : (xs.drop (cap - head)).take m₂ = xs.drop (cap - head) :=
      List.take_of_length_le (by rw [List.length_drop])
    simp [htake]
  have hfront :
      vecDequeSlotsAt (chainEpochAt A) 112 cap head ptr xs head (cap - head) =
        arrayAt (chainEpochAt A) 112 (ptr + BitVec.ofNat 64 (head * 112)) (xs.take (cap - head)) := by
    rw [vecDequeSlotsAt_occupied_eq_arrayAt (chainEpochAt A) 112 cap head ptr xs
      head 0 (cap - head) (by omega) (by intro k _; unfold vecDequeLogIdx; split <;> omega)]
    simp
  conv_lhs => arg 8; rw [hsplit]
  rw [vecDequeSlotsAt_add (chainEpochAt A) 112 cap head ptr xs 0 m₂ ((head - m₂) + (cap - head)),
      Nat.zero_add,
      vecDequeSlotsAt_add (chainEpochAt A) 112 cap head ptr xs m₂ (head - m₂) (cap - head),
      show m₂ + (head - m₂) = head by omega,
      hback, hfront]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hmid)) ?_
  dsimp only [m₂]
  exact Entails.of_eq (by ac_rfl)

/-- Split `memRegion out 80` into the 8 `↦₆₄` cells and 4 `↦₃₂` cells of `ChainPB`. -/
theorem memRegion_80_split_out (out : BitVec 64) :
    memRegion out 80 =
      (∃∗ d0 : BitVec 64, out ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (out + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (out + 16#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (out + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (out + 32#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (out + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (out + 48#64) ↦₆₄ d6) ∗ (∃∗ d7 : BitVec 64, (out + 56#64) ↦₆₄ d7) ∗
      (∃∗ p0 : BitVec 32, (out + 64#64) ↦₃₂ p0) ∗ (∃∗ p1 : BitVec 32, (out + 68#64) ↦₃₂ p1) ∗
      (∃∗ p2 : BitVec 32, (out + 72#64) ↦₃₂ p2) ∗ (∃∗ p3 : BitVec 32, (out + 76#64) ↦₃₂ p3) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 72) (b' := out + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 64) (b' := out + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 56) (b' := out + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 24#64) (n := 8) (k := 48) (b' := out + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 32#64) (n := 8) (k := 40) (b' := out + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 40#64) (n := 8) (k := 32) (b' := out + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 48#64) (n := 8) (k := 24) (b' := out + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 56#64) (n := 8) (k := 16) (b' := out + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 64#64) (n := 4) (k := 12) (b' := out + 68#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 68#64) (n := 4) (k := 8) (b' := out + 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 72#64) (n := 4) (k := 4) (b' := out + 76#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight out, ProofLib.memRegion_eight (out + 8#64),
      ProofLib.memRegion_eight (out + 16#64), ProofLib.memRegion_eight (out + 24#64),
      ProofLib.memRegion_eight (out + 32#64), ProofLib.memRegion_eight (out + 40#64),
      ProofLib.memRegion_eight (out + 48#64), ProofLib.memRegion_eight (out + 56#64),
      ProofLib.memRegion_four (out + 64#64), ProofLib.memRegion_four (out + 68#64),
      ProofLib.memRegion_four (out + 72#64), ProofLib.memRegion_four (out + 76#64)]

/-- Pack the `out` cells + `arrayAt (chainEpochPBAt A)` + `linksRawAllocAt` + `vecU8BufAt`
into `chainPBAt A ⟨BitVec.ofNat 64 c.links.length, newLinksPtr, g.epochs.map toChainEpochPBGhost, g.nextRoot⟩ out c.intoPb`. -/
theorem chainPBAt_pack_out (A : RustAlloc) (out newLinksPtr : BitVec 64)
    (g : ChainGhost) (c : Chain)
    (hlen : g.epochs.length = c.links.length)
    (hl_lt : c.links.length * 112 < 2 ^ 63)
    (hl_ne : newLinksPtr ≠ 0)
    (hn1 : c.nextRoot.length ≤ g.nextRoot.cap.toNat)
    (hn2 : g.nextRoot.cap.toNat < 2 ^ 63)
    (hn3 : g.nextRoot.ptr ≠ 0) :
    (out ↦₆₄ BitVec.ofNat 64 c.links.length) ∗ ((out + 8#64) ↦₆₄ newLinksPtr) ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      ((out + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((out + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((out + 40#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 48#64) ↦₆₄ c.currentEpoch) ∗ ((out + 56#64) ↦₆₄ c.sendEpoch) ∗
      ((out + 64#64) ↦₃₂ 1#32) ∗ ((out + 68#64) ↦₃₂ c.params.maxJump) ∗
      ((out + 72#64) ↦₃₂ c.params.maxOooKeys) ∗ ((out + 76#64) ↦₃₂ c.dir.toI32) ∗
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 c.links.length) newLinksPtr c.links.length ∗
      vecU8BufAt A g.nextRoot.cap g.nextRoot.ptr c.nextRoot ⊢
      chainPBAt A
        ⟨BitVec.ofNat 64 c.links.length, newLinksPtr,
          g.epochs.map toChainEpochPBGhost, g.nextRoot⟩
        out c.intoPb := by
  unfold chainPBAt vecAt vecBuf vecU8At vecHeader optChainParamsPBAt
    linksRawAllocAt vecU8BufAt Chain.intoPb chainEpochSize chainEpochAlign
  dsimp only
  have hlen_map : (g.epochs.map toChainEpochPBGhost).length = (c.links.map chainEpochIntoPb).length := by
    simp [hlen]
  have hzlen : ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)).length = c.links.length := by
    rw [List.length_zip, hlen_map, List.length_map, Nat.min_self]
  change _ ⊢
    ⌜(g.epochs.map toChainEpochPBGhost).length = (c.links.map chainEpochIntoPb).length⌝ ∗
      (((out ↦₆₄ BitVec.ofNat 64 c.links.length ∗ (out + 8#64) ↦₆₄ newLinksPtr ∗
          (out + 16#64) ↦₆₄ BitVec.ofNat 64 ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)).length) ∗
        ⌜((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)).length ≤ (BitVec.ofNat 64 c.links.length).toNat ∧
            (BitVec.ofNat 64 c.links.length).toNat * 112 < 2 ^ 63 ∧ newLinksPtr ≠ 0⌝ ∗
        if BitVec.ofNat 64 c.links.length = 0 then emp
        else
          A.live newLinksPtr ((BitVec.ofNat 64 c.links.length).toNat * 112) 8 ∗
            arrayAt (chainEpochPBAt A) 112 newLinksPtr
              ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
            memRegion (newLinksPtr + BitVec.ofNat 64 (((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)).length * 112))
              (((BitVec.ofNat 64 c.links.length).toNat - ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)).length) * 112)) ∗
      (((out + 24#64) ↦₆₄ g.nextRoot.cap ∗ (out + 24#64 + 8#64) ↦₆₄ g.nextRoot.ptr ∗
          (out + 24#64 + 16#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
        ⌜c.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
            g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
        if g.nextRoot.cap = 0 then emp
        else
          A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
            memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
              (g.nextRoot.cap.toNat - c.nextRoot.length)) ∗
      (out + 48#64) ↦₆₄ c.currentEpoch ∗ (out + 56#64) ↦₆₄ c.sendEpoch ∗
      ((out + 64#64) ↦₃₂ 1#32 ∗ ((out + 64#64 + 4#64) ↦₃₂ c.params.maxJump ∗
        (out + 64#64 + 8#64) ↦₃₂ c.params.maxOooKeys)) ∗
      (out + 76#64) ↦₃₂ c.dir.toI32)
  rw [hzlen]
  have htn : (BitVec.ofNat 64 c.links.length).toNat = c.links.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [htn, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.pure_right hlen_map ?_
  have hlinks :
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
      (if BitVec.ofNat 64 c.links.length = 0 then emp
       else
         A.live newLinksPtr (c.links.length * 112) 8 ∗
           memRegion (newLinksPtr + BitVec.ofNat 64 (c.links.length * 112))
             ((c.links.length - c.links.length) * 112)) ⊢
      ⌜c.links.length ≤ c.links.length ∧ c.links.length * 112 < 2 ^ 63 ∧ newLinksPtr ≠ 0⌝ ∗
      (if BitVec.ofNat 64 c.links.length = 0 then emp
       else
         A.live newLinksPtr (c.links.length * 112) 8 ∗
           arrayAt (chainEpochPBAt A) 112 newLinksPtr
             ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
           memRegion (newLinksPtr + BitVec.ofNat 64 (c.links.length * 112))
             ((c.links.length - c.links.length) * 112)) := by
    refine Entails.pure_right ⟨Nat.le_refl _, hl_lt, hl_ne⟩ ?_
    by_cases hc : BitVec.ofNat 64 c.links.length = 0
    · have hlen0 : c.links.length = 0 := by
        have := congrArg BitVec.toNat hc
        simpa [htn] using this
      have hnil : c.links = [] := List.eq_nil_of_length_eq_zero hlen0
      rw [hc]
      simp only [hnil, List.map_nil, List.zip_nil_right, arrayAt, ↓reduceIte, sepConj_emp]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
  have hnr :
      (if g.nextRoot.cap = 0 then emp
       else
         A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
           memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
             (g.nextRoot.cap.toNat - c.nextRoot.length)) ⊢
      ⌜c.nextRoot.length ≤ g.nextRoot.cap.toNat ∧
          g.nextRoot.cap.toNat < 2 ^ 63 ∧ g.nextRoot.ptr ≠ 0⌝ ∗
      (if g.nextRoot.cap = 0 then emp
       else
         A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
           memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
             (g.nextRoot.cap.toNat - c.nextRoot.length)) :=
    Entails.pure_right ⟨hn1, hn2, hn3⟩ (Entails.refl _)
  rw [show
    (out ↦₆₄ BitVec.ofNat 64 c.links.length) ∗ ((out + 8#64) ↦₆₄ newLinksPtr) ∗
      ((out + 16#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      ((out + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((out + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      ((out + 40#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      ((out + 48#64) ↦₆₄ c.currentEpoch) ∗ ((out + 56#64) ↦₆₄ c.sendEpoch) ∗
      ((out + 64#64) ↦₃₂ 1#32) ∗ ((out + 68#64) ↦₃₂ c.params.maxJump) ∗
      ((out + 72#64) ↦₃₂ c.params.maxOooKeys) ∗ ((out + 76#64) ↦₃₂ c.dir.toI32) ∗
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
      (if BitVec.ofNat 64 c.links.length = 0 then emp
       else
         A.live newLinksPtr (c.links.length * 112) 8 ∗
           memRegion (newLinksPtr + BitVec.ofNat 64 (c.links.length * 112))
             ((c.links.length - c.links.length) * 112)) ∗
      (if g.nextRoot.cap = 0 then emp
       else
         A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
           memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
             (g.nextRoot.cap.toNat - c.nextRoot.length)) =
    ((out ↦₆₄ BitVec.ofNat 64 c.links.length ∗ (out + 8#64) ↦₆₄ newLinksPtr ∗
        (out + 16#64) ↦₆₄ BitVec.ofNat 64 c.links.length) ∗
      (arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((g.epochs.map toChainEpochPBGhost).zip (c.links.map chainEpochIntoPb)) ∗
        if BitVec.ofNat 64 c.links.length = 0 then emp
        else
          A.live newLinksPtr (c.links.length * 112) 8 ∗
            memRegion (newLinksPtr + BitVec.ofNat 64 (c.links.length * 112))
              ((c.links.length - c.links.length) * 112))) ∗
    (((out + 24#64) ↦₆₄ g.nextRoot.cap ∗ (out + 32#64) ↦₆₄ g.nextRoot.ptr ∗
        (out + 40#64) ↦₆₄ BitVec.ofNat 64 c.nextRoot.length) ∗
      if g.nextRoot.cap = 0 then emp
      else
        A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗ g.nextRoot.ptr ↦ₛ c.nextRoot ∗
          memRegion (g.nextRoot.ptr + BitVec.ofNat 64 c.nextRoot.length)
            (g.nextRoot.cap.toNat - c.nextRoot.length)) ∗
    (out + 48#64) ↦₆₄ c.currentEpoch ∗ (out + 56#64) ↦₆₄ c.sendEpoch ∗
    ((out + 64#64) ↦₃₂ 1#32 ∗ ((out + 68#64) ↦₃₂ c.params.maxJump ∗
      (out + 72#64) ↦₃₂ c.params.maxOooKeys)) ∗
    (out + 76#64) ↦₃₂ c.dir.toI32 by ac_rfl]
  exact sepConj_mono (sepConj_mono_right hlinks) (sepConj_mono_left (sepConj_mono_right hnr))

/-! ## Stack Frame Split and Join (`chainIntoPbStack = 4416` B) -/

theorem stackAt_chainIntoPb_split (sp : BitVec 64) :
    stackAt sp chainIntoPbStack =
      stackAt (sp - 288#64) dropStack32 ∗
      (∃∗ s00 : BitVec 64, (sp - 288#64) ↦₆₄ s00) ∗ (∃∗ s08 : BitVec 64, (sp - 280#64) ↦₆₄ s08) ∗
      (∃∗ s10 : BitVec 64, (sp - 272#64) ↦₆₄ s10) ∗ memRegion (sp - 264#64) 4 ∗
      (∃∗ s1c : BitVec 32, (sp - 260#64) ↦₃₂ s1c) ∗ (∃∗ s20 : BitVec 64, (sp - 256#64) ↦₆₄ s20) ∗
      (∃∗ s28 : BitVec 64, (sp - 248#64) ↦₆₄ s28) ∗ (∃∗ s30 : BitVec 64, (sp - 240#64) ↦₆₄ s30) ∗
      (∃∗ s38 : BitVec 64, (sp - 232#64) ↦₆₄ s38) ∗ (∃∗ s40 : BitVec 64, (sp - 224#64) ↦₆₄ s40) ∗
      (∃∗ s48 : BitVec 64, (sp - 216#64) ↦₆₄ s48) ∗ (∃∗ s50 : BitVec 64, (sp - 208#64) ↦₆₄ s50) ∗
      (∃∗ s58 : BitVec 64, (sp - 200#64) ↦₆₄ s58) ∗ (∃∗ s60 : BitVec 64, (sp - 192#64) ↦₆₄ s60) ∗
      (∃∗ s68 : BitVec 64, (sp - 184#64) ↦₆₄ s68) ∗ (∃∗ s70 : BitVec 64, (sp - 176#64) ↦₆₄ s70) ∗
      (∃∗ s78 : BitVec 64, (sp - 168#64) ↦₆₄ s78) ∗ (∃∗ s80 : BitVec 64, (sp - 160#64) ↦₆₄ s80) ∗
      (∃∗ s88 : BitVec 64, (sp - 152#64) ↦₆₄ s88) ∗ (∃∗ s90 : BitVec 64, (sp - 144#64) ↦₆₄ s90) ∗
      (∃∗ s98 : BitVec 64, (sp - 136#64) ↦₆₄ s98) ∗ (∃∗ sa0 : BitVec 64, (sp - 128#64) ↦₆₄ sa0) ∗
      (∃∗ sa8 : BitVec 64, (sp - 120#64) ↦₆₄ sa8) ∗ memRegion (sp - 112#64) 16 ∗
      (∃∗ sc0 : BitVec 64, (sp - 96#64) ↦₆₄ sc0) ∗ (∃∗ sc8 : BitVec 64, (sp - 88#64) ↦₆₄ sc8) ∗
      (∃∗ sd0 : BitVec 64, (sp - 80#64) ↦₆₄ sd0) ∗ (∃∗ sd8 : BitVec 64, (sp - 72#64) ↦₆₄ sd8) ∗
      (∃∗ se0 : BitVec 64, (sp - 64#64) ↦₆₄ se0) ∗ (∃∗ se8 : BitVec 64, (sp - 56#64) ↦₆₄ se8) ∗
      (∃∗ sf0 : BitVec 64, (sp - 48#64) ↦₆₄ sf0) ∗ (∃∗ sf8 : BitVec 64, (sp - 40#64) ↦₆₄ sf8) ∗
      (∃∗ s100 : BitVec 64, (sp - 32#64) ↦₆₄ s100) ∗ (∃∗ s108 : BitVec 64, (sp - 24#64) ↦₆₄ s108) ∗
      (∃∗ s110 : BitVec 64, (sp - 16#64) ↦₆₄ s110) ∗ (∃∗ s118 : BitVec 64, (sp - 8#64) ↦₆₄ s118) := by
  unfold stackAt
  change memRegion (sp - 4416#64) 4416 = memRegion (sp - 288#64 - 4128#64) 4128 ∗ _
  have hsub : sp - 288#64 - 4128#64 = sp - 4416#64 := by bv_omega
  rw [hsub,
    ProofLib.memRegion_split' (b := sp - 4416#64) (n := 4128) (k := 288) (b' := sp - 288#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 288#64) (n := 8) (k := 280) (b' := sp - 280#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 280#64) (n := 8) (k := 272) (b' := sp - 272#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 8) (k := 264) (b' := sp - 264#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 264#64) (n := 4) (k := 260) (b' := sp - 260#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 260#64) (n := 4) (k := 256) (b' := sp - 256#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 256#64) (n := 8) (k := 248) (b' := sp - 248#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 248#64) (n := 8) (k := 240) (b' := sp - 240#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 8) (k := 232) (b' := sp - 232#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 232#64) (n := 8) (k := 224) (b' := sp - 224#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 224#64) (n := 8) (k := 216) (b' := sp - 216#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 216#64) (n := 8) (k := 208) (b' := sp - 208#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 8) (k := 200) (b' := sp - 200#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 200#64) (n := 8) (k := 192) (b' := sp - 192#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 192#64) (n := 8) (k := 184) (b' := sp - 184#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 184#64) (n := 8) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 168#64) (n := 8) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 152) (b' := sp - 152#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 152#64) (n := 8) (k := 144) (b' := sp - 144#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 136) (b' := sp - 136#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 128) (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120) (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 112) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 112#64) (n := 16) (k := 96) (b' := sp - 96#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 72) (b' := sp - 72#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 56#64) (n := 8) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40) (b' := sp - 40#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 40#64) (n := 8) (k := 32) (b' := sp - 32#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24) (b' := sp - 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16) (b' := sp - 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8) (b' := sp - 8#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_eight (sp - 288#64), ProofLib.memRegion_eight (sp - 280#64),
    ProofLib.memRegion_eight (sp - 272#64), ProofLib.memRegion_four (sp - 260#64),
    ProofLib.memRegion_eight (sp - 256#64), ProofLib.memRegion_eight (sp - 248#64),
    ProofLib.memRegion_eight (sp - 240#64), ProofLib.memRegion_eight (sp - 232#64),
    ProofLib.memRegion_eight (sp - 224#64), ProofLib.memRegion_eight (sp - 216#64),
    ProofLib.memRegion_eight (sp - 208#64), ProofLib.memRegion_eight (sp - 200#64),
    ProofLib.memRegion_eight (sp - 192#64), ProofLib.memRegion_eight (sp - 184#64),
    ProofLib.memRegion_eight (sp - 176#64), ProofLib.memRegion_eight (sp - 168#64),
    ProofLib.memRegion_eight (sp - 160#64), ProofLib.memRegion_eight (sp - 152#64),
    ProofLib.memRegion_eight (sp - 144#64), ProofLib.memRegion_eight (sp - 136#64),
    ProofLib.memRegion_eight (sp - 128#64), ProofLib.memRegion_eight (sp - 120#64),
    ProofLib.memRegion_eight (sp - 96#64), ProofLib.memRegion_eight (sp - 88#64),
    ProofLib.memRegion_eight (sp - 80#64), ProofLib.memRegion_eight (sp - 72#64),
    ProofLib.memRegion_eight (sp - 64#64), ProofLib.memRegion_eight (sp - 56#64),
    ProofLib.memRegion_eight (sp - 48#64), ProofLib.memRegion_eight (sp - 40#64),
    ProofLib.memRegion_eight (sp - 32#64), ProofLib.memRegion_eight (sp - 24#64),
    ProofLib.memRegion_eight (sp - 16#64), ProofLib.memRegion_eight (sp - 8#64)]

theorem stackAt_chainIntoPb_join (sp : BitVec 64)
    (s00 s08 s10 : BitVec 64) (s1c : BitVec 32)
    (s20 s28 s30 s38 s40 s48 s50 s58 s60 s68 s70 s78 s80 s88 s90 s98 sa0 sa8 : BitVec 64)
    (sc0 sc8 sd0 sd8 se0 se8 sf0 sf8 s100 s108 s110 s118 : BitVec 64) :
    stackAt (sp - 288#64) dropStack32 ∗
      ((sp - 288#64) ↦₆₄ s00) ∗ ((sp - 280#64) ↦₆₄ s08) ∗
      ((sp - 272#64) ↦₆₄ s10) ∗ memRegion (sp - 264#64) 4 ∗
      ((sp - 260#64) ↦₃₂ s1c) ∗ ((sp - 256#64) ↦₆₄ s20) ∗
      ((sp - 248#64) ↦₆₄ s28) ∗ ((sp - 240#64) ↦₆₄ s30) ∗
      ((sp - 232#64) ↦₆₄ s38) ∗ ((sp - 224#64) ↦₆₄ s40) ∗
      ((sp - 216#64) ↦₆₄ s48) ∗ ((sp - 208#64) ↦₆₄ s50) ∗
      ((sp - 200#64) ↦₆₄ s58) ∗ ((sp - 192#64) ↦₆₄ s60) ∗
      ((sp - 184#64) ↦₆₄ s68) ∗ ((sp - 176#64) ↦₆₄ s70) ∗
      ((sp - 168#64) ↦₆₄ s78) ∗ ((sp - 160#64) ↦₆₄ s80) ∗
      ((sp - 152#64) ↦₆₄ s88) ∗ ((sp - 144#64) ↦₆₄ s90) ∗
      ((sp - 136#64) ↦₆₄ s98) ∗ ((sp - 128#64) ↦₆₄ sa0) ∗
      ((sp - 120#64) ↦₆₄ sa8) ∗ memRegion (sp - 112#64) 16 ∗
      ((sp - 96#64) ↦₆₄ sc0) ∗ ((sp - 88#64) ↦₆₄ sc8) ∗
      ((sp - 80#64) ↦₆₄ sd0) ∗ ((sp - 72#64) ↦₆₄ sd8) ∗
      ((sp - 64#64) ↦₆₄ se0) ∗ ((sp - 56#64) ↦₆₄ se8) ∗
      ((sp - 48#64) ↦₆₄ sf0) ∗ ((sp - 40#64) ↦₆₄ sf8) ∗
      ((sp - 32#64) ↦₆₄ s100) ∗ ((sp - 24#64) ↦₆₄ s108) ∗
      ((sp - 16#64) ↦₆₄ s110) ∗ ((sp - 8#64) ↦₆₄ s118) ⊢
      stackAt sp chainIntoPbStack := by
  rw [stackAt_chainIntoPb_split sp]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_right s00 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s08 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s10 (Entails.refl _)) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_right s1c (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s20 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s28 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s30 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s38 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s40 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s48 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s50 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s58 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s60 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s68 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s70 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s78 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s80 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s88 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s90 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s98 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sa0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sa8 (Entails.refl _)) (sepConj_mono_right ?_)
  refine sepConj_mono (Entails.sepExists_right sc0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sc8 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sd0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sd8 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right se0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right se8 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sf0 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right sf8 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s100 (Entails.refl _)) ?_
  refine sepConj_mono (Entails.sepExists_right s108 (Entails.refl _)) ?_
  exact sepConj_mono (Entails.sepExists_right s110 (Entails.refl _))
    (Entails.sepExists_right s118 (Entails.refl _))

theorem stackAt_chainIntoPbX_split (sp : BitVec 64) :
    stackAt sp chainIntoPbStackX =
      memRegion (sp - 16672#64) 12256 ∗ stackAt sp chainIntoPbStack :=
  stackAt_split_bottom sp chainIntoPbStack 12256 (by decide)

end CryptoVerification.SpqrV1.ChainProofs
