/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib
public import ProofLib.SepLogic.CFG
public import ProofLib.SepLogic.LoopTactics
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Byte-Region and Loop Invariant Tests

Unit tests for `ProofLib.SepLogic.ByteRegion`, `wp_sep_access` on symbolic byte slices and
symbolic offsets, `wp_bv_omega` register-context pruning, and `wp_loop_measure` over byte-fill
and word/byte-copy loops.
-/

@[expose] public section

namespace Testing.ByteRegion

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## `byte_region_len` and `byte_region_eq` -/

section byte_region_tactic_tests

variable (bs old src : List (BitVec 8)) (b : BitVec 8) (k : Nat)

example (h : k + 1 ≤ bs.length) :
    k + 1 ≤ (ByteSlice.write8 (ByteSlice.fillPrefix bs b k) k b).length := by
  byte_region_len

example (h : k + 1 ≤ bs.length) :
    ByteSlice.write8 (ByteSlice.fillPrefix bs b k) k b = ByteSlice.fillPrefix bs b (k + 1) := by
  byte_region_eq

example (h : k + 8 ≤ old.length) :
    ByteSlice.write64 (ByteSlice.copyPrefix old src k) k (ByteSlice.readLE src k 8) =
      ByteSlice.copyPrefix old src (k + 8) := by
  byte_region_eq

example (_h : k + 2 ≤ bs.length) : True := by
  fail_if_success
    have : ByteSlice.write8 (ByteSlice.fillPrefix bs b k) k b =
        ByteSlice.fillPrefix bs b (k + 2) := by byte_region_eq
  trivial

example : True := by
  fail_if_success have : k + 1 ≤ (ByteSlice.fillPrefix bs b k).length := by byte_region_len
  trivial

end byte_region_tactic_tests

/-! ## `wp_sep_access` on Byte Lists at Symbolic Offsets -/

section sep_access_bytes_tests

variable (dst srcPtr v : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8) (k : Nat) (R : SepProp)

example (hk : k + 1 ≤ bs.length) :
    SepStore8 (dst + BitVec.ofNat 64 k) b ((dst ↦ₛ bs) ∗ R)
      ((dst ↦ₛ ByteSlice.write8 bs k b) ∗ R) := by
  wp_sep_access

example (hk : k + 16 ≤ bs.length) :
    SepLoad64 (dst + BitVec.ofNat 64 k + 8#64) (R ∗ (dst ↦ₛ bs)) (ByteSlice.readLE bs (k + 8) 8) := by
  wp_sep_access

example (n : BitVec 64) (hlen : bs.length = n.toNat) (h8 : 8 ≤ n.toNat) :
    SepStore64 (dst + n - 8#64) v (dst ↦ₛ bs) (dst ↦ₛ ByteSlice.write64 bs (n.toNat - 8) v) := by
  wp_sep_access

example (hk : k + 1 ≤ bs.length) :
    SepLoad8 (srcPtr + BitVec.ofNat 64 k) ((srcPtr ↦ᵣ bs) ∗ R) (bs.getD k 0#8) := by
  wp_sep_access

example (h : 4 ≤ bs.length) : SepLoad8 (dst + 3#64) (dst ↦ₛ bs) (bs.getD 3 0#8) := by
  wp_sep_access

example (v16 : BitVec 16) (hk : k + 4 ≤ bs.length) :
    SepStore16 (dst + BitVec.ofNat 64 k + 2#64) v16 (dst ↦ₛ bs)
      (dst ↦ₛ ByteSlice.write16 bs (k + 2) v16) := by
  wp_sep_access

example (v32 : BitVec 32) (hk : k + 8 ≤ bs.length) :
    SepStore32 (dst + BitVec.ofNat 64 k + 4#64) v32 (R ∗ (dst ↦ₛ bs))
      (R ∗ (dst ↦ₛ ByteSlice.write32 bs (k + 4) v32)) := by
  wp_sep_access

example (hk : k + 4 ≤ bs.length) :
    SepLoad32 (srcPtr + BitVec.ofNat 64 k) (srcPtr ↦ᵣ bs)
      (pack32 (bs.getD k 0#8) (bs.getD (k + 1) 0#8) (bs.getD (k + 2) 0#8)
        (bs.getD (k + 3) 0#8)) := by
  wp_sep_access

example (_hk32 : 32 ≤ k) (hk : k + 8 ≤ bs.length) :
    SepLoad64 (dst + BitVec.ofNat 64 k - 32#64 + 32#64) (dst ↦ₛ bs)
      (ByteSlice.readLE bs k 8) := by
  wp_sep_access

set_option maxHeartbeats 400000 in
example (st : State) (old : List (BitVec 8)) (n : BitVec 64) (p : Nat)
    (_hx0 : st.readReg64 .x0 = dst) (_hx3 : st.readReg64 .x3 = dst + BitVec.ofNat 64 p - 16#64)
    (_hx4 : st.readReg64 .x4 = srcPtr + n) (_hx5 : st.readReg64 .x5 = dst + n)
    (_hlen : old.length = n.toNat) (hslen : bs.length = n.toNat) (_hn63 : n.toNat ≤ 2 ^ 63)
    (_hp : p + 64 ≤ n.toNat) (_hcov : n.toNat ≤ p + 128) :
    SepLoad64 (srcPtr + n - 16#64)
      ((dst ↦ₛ ByteSlice.write64 (ByteSlice.write64 old p v) (p + 8) v) ∗ (srcPtr ↦ᵣ bs))
      (ByteSlice.readLE bs (n.toNat - 16) 8) := by
  wp_sep_access

example (old : List (BitVec 8)) (n : BitVec 64) (p : Nat) (hlen : old.length = n.toNat)
    (hp : p + 64 ≤ n.toNat) :
    SepStore64 (dst + n - 8#64) v
      (dst ↦ₛ ByteSlice.write64 (ByteSlice.write64 (ByteSlice.copySet old bs fun i => decide (i < p))
        p v) (p + 8) v)
      (dst ↦ₛ ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
        (ByteSlice.copySet old bs fun i => decide (i < p)) p v) (p + 8) v) (n.toNat - 8) v) := by
  wp_sep_access

example (n m : Nat) (hslen : bs.length = n) (hm : m + 1 + 1 ≤ n) :
    SepLoad8 (srcPtr + BitVec.ofNat 64 (n - (m + 1 + 1))) (srcPtr ↦ᵣ bs)
      (bs.getD (n - (m + 1 + 1)) 0#8) := by
  wp_sep_access

example (m : Nat) (hm : m + 2 ≤ bs.length) :
    SepLoad8 (srcPtr + BitVec.ofNat 64 (m + 2) - 1#64) ((dst ↦ₛ bs) ∗ (srcPtr ↦ᵣ bs))
      (bs.getD (m + 2 - 1) 0#8) := by
  wp_sep_access

example (_hk : k + 1 ≤ bs.length) : True := by
  fail_if_success
    have : SepStore64 (dst + BitVec.ofNat 64 k) v (dst ↦ₛ bs)
        (dst ↦ₛ ByteSlice.write64 bs k v) := by wp_sep_access
  trivial

example (_hk : k + 1 ≤ bs.length) : True := by
  fail_if_success
    have : SepStore8 (dst + BitVec.ofNat 64 k) b (dst ↦ₛ bs)
        (dst ↦ₛ ByteSlice.write8 bs k b) := by
      set_option proofLib.wpSymbolicBytes false in wp_sep_access
  trivial

end sep_access_bytes_tests

/-! ## Byte-Fill Loop -/

@[simp, arm64_norm] def byte_fill_addr : BitVec 64 := 0x5b000#64

/-- Byte fill (`x0` = destination, `w1` = byte, `x2` = count >= 1) at `0x5b000`:
    * `0x5b000`: `strb w1, [x0], #1`
    * `0x5b004`: `subs x2, x2, #1`
    * `0x5b008`: `b.ne 0x5b000`
    * `0x5b00c`: `ret` -/
def byteFillCode : FnCode :=
  .atAddr "byte_fill" byte_fill_addr
    ("38001401 " ++ -- 0x5b000: strb w1, [x0], #1
     "f1000442 " ++ -- 0x5b004: subs x2, x2, #1
     "54ffffc1 " ++ -- 0x5b008: b.ne 0x5b000
     "d65f03c0")    -- 0x5b00c: ret

theorem byte_fill_loop_test (prog : Program) (h_code : byteFillCode.holds prog)
    (s0 : State) (dst : BitVec 64) (bs0 : List (BitVec 8)) (b : BitVec 8) (n : Nat)
    (hn0 : 0 < n) (hn : n < 2 ^ 32) (hlen : bs0.length = n)
    (hpc : s0.pc = 0x5b000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = b.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs0)
      (sepPost (fun _ => True) (dst ↦ₛ List.replicate n b)) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst + BitVec.ofNat 64 (n - (k + 1)) ∧
      st.readReg64 .x1 = b.zeroExtend 64 ∧ st.readReg64 .x2 = BitVec.ofNat 64 (k + 1))
    (fun k _ => dst ↦ₛ ByteSlice.fillPrefix bs0 b (n - (k + 1)))
  case init => byte_region_entails
  case base =>
    wp_steps
    wp_done
  case step =>
    right
    wp_steps
    wp_done

theorem byte_fill_no_branch_stop_test (prog : Program) (h_code : byteFillCode.holds prog)
    (s0 : State) (dst : BitVec 64) (bs0 : List (BitVec 8)) (b : BitVec 8) (n : Nat)
    (hn0 : 0 < n) (hn : n < 2 ^ 32) (hlen : bs0.length = n)
    (hpc : s0.pc = 0x5b000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = b.zeroExtend 64)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs0)
      (sepPost (fun _ => True) (dst ↦ₛ List.replicate n b)) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst + BitVec.ofNat 64 (n - (k + 1)) ∧
      st.readReg64 .x1 = b.zeroExtend 64 ∧ st.readReg64 .x2 = BitVec.ofNat 64 (k + 1))
    (fun k _ => dst ↦ₛ ByteSlice.fillPrefix bs0 b (n - (k + 1)))
  case init => byte_region_entails
  case base =>
    wp_steps
    wp_done
  case step =>
    right
    fail_if_success
      set_option proofLib.wpStopAtBranchTarget false in
      (wp_steps; wp_done)
    wp_steps
    wp_done

/-! ## 8-Byte Copy Loop -/

@[simp, arm64_norm] def word_copy_addr : BitVec 64 := 0x5c000#64

/-- Word copy (`x0` = destination, `x1` = source, `x2` = word count >= 1) at `0x5c000`:
    * `0x5c000`: `ldr x3, [x1], #8`
    * `0x5c004`: `str x3, [x0], #8`
    * `0x5c008`: `subs x2, x2, #1`
    * `0x5c00c`: `b.ne 0x5c000`
    * `0x5c010`: `ret` -/
def wordCopyCode : FnCode :=
  .atAddr "word_copy" word_copy_addr
    ("f8408423 " ++ -- 0x5c000: ldr x3, [x1], #8
     "f8008403 " ++ -- 0x5c004: str x3, [x0], #8
     "f1000442 " ++ -- 0x5c008: subs x2, x2, #1
     "54ffffa1 " ++ -- 0x5c00c: b.ne 0x5c000
     "d65f03c0")    -- 0x5c010: ret

theorem word_copy_loop_test (prog : Program) (h_code : wordCopyCode.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (n : Nat)
    (hn0 : 0 < n) (hn : n < 2 ^ 32) (hlen : old.length = 8 * n) (hslen : src.length = 8 * n)
    (hpc : s0.pc = 0x5c000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = srcPtr)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 ((dst ↦ₛ old) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True) ((dst ↦ₛ src) ∗ (srcPtr ↦ᵣ src))) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst + BitVec.ofNat 64 (8 * (n - (k + 1))) ∧
      st.readReg64 .x1 = srcPtr + BitVec.ofNat 64 (8 * (n - (k + 1))) ∧
      st.readReg64 .x2 = BitVec.ofNat 64 (k + 1))
    (fun k _ => (dst ↦ₛ ByteSlice.copyPrefix old src (8 * (n - (k + 1)))) ∗ (srcPtr ↦ᵣ src))
  case init => byte_region_entails
  case base =>
    wp_steps
    wp_done
  case step =>
    right
    wp_steps
    wp_done

theorem word_copy_loop_sym_test (prog : Program) (h_code : wordCopyCode.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (n : Nat)
    (hn0 : 0 < n) (hn : n < 2 ^ 32) (hlen : old.length = 8 * n) (hslen : src.length = 8 * n)
    (hpc : s0.pc = 0x5c000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = srcPtr)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 ((dst ↦ₛ old) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True) ((dst ↦ₛ src) ∗ (srcPtr ↦ᵣ src))) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst + BitVec.ofNat 64 (8 * (n - (k + 1))) ∧
      st.readReg64 .x1 = srcPtr + BitVec.ofNat 64 (8 * (n - (k + 1))) ∧
      st.readReg64 .x2 = BitVec.ofNat 64 (k + 1))
    (fun k _ => (dst ↦ₛ ByteSlice.copyPrefix old src (8 * (n - (k + 1)))) ∗ (srcPtr ↦ᵣ src))
  case init => byte_region_entails
  case base =>
    wp_sym_steps
    wp_done
  case step =>
    right
    wp_sym_steps
    wp_done

/-! ## Straight-Line Store at a Symbolic End Offset -/

@[simp, arm64_norm] def tail_store_addr : BitVec 64 := 0x5d000#64

/-- Store `x1` to the last 8 bytes of `[x0, x0 + x2)` at `0x5d000`:
    * `0x5d000`: `add x3, x0, x2`
    * `0x5d004`: `stur x1, [x3, #-8]`
    * `0x5d008`: `ret` -/
def tailStoreCode : FnCode :=
  .atAddr "tail_store" tail_store_addr
    ("8b020003 " ++ -- 0x5d000: add x3, x0, x2
     "f81f8061 " ++ -- 0x5d004: stur x1, [x3, #-8]
     "d65f03c0")    -- 0x5d008: ret

theorem tail_store_test (prog : Program) (h_code : tailStoreCode.holds prog)
    (s0 : State) (dst n v : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = n.toNat) (h8 : 8 ≤ n.toNat)
    (hpc : s0.pc = 0x5d000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = v)
    (hx2 : s0.readReg64 .x2 = n) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (fun _ => True) (dst ↦ₛ ByteSlice.write64 bs (n.toNat - 8) v)) := by
  wp_steps
  wp_done

/-! ## Straight-Line 2/4/8-Byte Copies Through 16/32-Bit Registers -/

@[simp, arm64_norm] def copy32_addr : BitVec 64 := 0x5e000#64
@[simp, arm64_norm] def copy16_addr : BitVec 64 := 0x5e100#64
@[simp, arm64_norm] def copy_pair_addr : BitVec 64 := 0x5e300#64

/-- `ldr w3, [x1]; str w3, [x0]; ret` at `0x5e000`. -/
def copy32Code : FnCode := .atAddr "copy32" copy32_addr ("b9400023 " ++ "b9000003 " ++ "d65f03c0")
/-- `ldrh w3, [x1]; strh w3, [x0]; ret` at `0x5e100`. -/
def copy16Code : FnCode := .atAddr "copy16" copy16_addr ("79400023 " ++ "79000003 " ++ "d65f03c0")
/-- `ldp w3, w4, [x1]; stp w3, w4, [x0]; ret` at `0x5e300`. -/
def copyPairCode : FnCode :=
  .atAddr "copy_pair" copy_pair_addr ("29401023 " ++ "29001003 " ++ "d65f03c0")

theorem copy32_test (prog : Program) (h_code : copy32Code.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (j : Nat)
    (hlen : old.length = src.length) (hj : j + 4 ≤ src.length)
    (hpc : s0.pc = 0x5e000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 j)
    (hx1 : s0.readReg64 .x1 = srcPtr + BitVec.ofNat 64 j) :
    SepWP prog (s0.readReg64 .lr) s0
      ((dst ↦ₛ ByteSlice.copyPrefix old src j) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.copyPrefix old src (j + 4)) ∗ (srcPtr ↦ᵣ src))) := by
  wp_steps
  wp_done

theorem copy32_no_symbolic_bytes_test (prog : Program) (h_code : copy32Code.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (j : Nat)
    (hlen : old.length = src.length) (hj : j + 4 ≤ src.length)
    (hpc : s0.pc = 0x5e000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 j)
    (hx1 : s0.readReg64 .x1 = srcPtr + BitVec.ofNat 64 j) :
    SepWP prog (s0.readReg64 .lr) s0
      ((dst ↦ₛ ByteSlice.copyPrefix old src j) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.copyPrefix old src (j + 4)) ∗ (srcPtr ↦ᵣ src))) := by
  fail_if_success
    set_option proofLib.wpSymbolicBytes false in
    (wp_steps; wp_done)
  wp_steps
  wp_done

theorem copy32_sym_test (prog : Program) (h_code : copy32Code.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (j : Nat)
    (hlen : old.length = src.length) (hj : j + 4 ≤ src.length)
    (hpc : s0.pc = 0x5e000#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 j)
    (hx1 : s0.readReg64 .x1 = srcPtr + BitVec.ofNat 64 j) :
    SepWP prog (s0.readReg64 .lr) s0
      ((dst ↦ₛ ByteSlice.copyPrefix old src j) ∗ (srcPtr ↦ₛ src))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.copyPrefix old src (j + 4)) ∗ (srcPtr ↦ₛ src))) := by
  wp_sym_steps
  wp_done

theorem copy16_sym_test (prog : Program) (h_code : copy16Code.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (j : Nat)
    (hlen : old.length = src.length) (hj : j + 2 ≤ src.length)
    (hpc : s0.pc = 0x5e100#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 j)
    (hx1 : s0.readReg64 .x1 = srcPtr + BitVec.ofNat 64 j) :
    SepWP prog (s0.readReg64 .lr) s0
      ((dst ↦ₛ ByteSlice.copyPrefix old src j) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.copyPrefix old src (j + 2)) ∗ (srcPtr ↦ᵣ src))) := by
  wp_sym_steps
  wp_done

theorem copy_pair_test (prog : Program) (h_code : copyPairCode.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (j : Nat)
    (hlen : old.length = src.length) (hj : j + 8 ≤ src.length)
    (hpc : s0.pc = 0x5e300#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 j)
    (hx1 : s0.readReg64 .x1 = srcPtr + BitVec.ofNat 64 j) :
    SepWP prog (s0.readReg64 .lr) s0
      ((dst ↦ₛ ByteSlice.copyPrefix old src j) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.copyPrefix old src (j + 8)) ∗ (srcPtr ↦ᵣ src))) := by
  wp_steps
  wp_done

/-! ## 4-Byte Copy Loop -/

@[simp, arm64_norm] def copy32_loop_addr : BitVec 64 := 0x5e400#64

/-- Word copy (`x0` = destination, `x1` = source, `x2` = 4-byte count >= 1) at `0x5e400`:
    * `0x5e400`: `ldr w3, [x1], #4`
    * `0x5e404`: `str w3, [x0], #4`
    * `0x5e408`: `subs x2, x2, #1`
    * `0x5e40c`: `b.ne 0x5e400`
    * `0x5e410`: `ret` -/
def copy32LoopCode : FnCode :=
  .atAddr "copy32_loop" copy32_loop_addr
    ("b8404423 " ++ -- 0x5e400: ldr w3, [x1], #4
     "b8004403 " ++ -- 0x5e404: str w3, [x0], #4
     "f1000442 " ++ -- 0x5e408: subs x2, x2, #1
     "54ffffa1 " ++ -- 0x5e40c: b.ne 0x5e400
     "d65f03c0")    -- 0x5e410: ret

theorem copy32_loop_sym_test (prog : Program) (h_code : copy32LoopCode.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (n : Nat)
    (hn0 : 0 < n) (hn : n < 2 ^ 32) (hlen : old.length = 4 * n) (hslen : src.length = 4 * n)
    (hpc : s0.pc = 0x5e400#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = srcPtr)
    (hx2 : s0.readReg64 .x2 = BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 ((dst ↦ₛ old) ∗ (srcPtr ↦ᵣ src))
      (sepPost (fun _ => True) ((dst ↦ₛ src) ∗ (srcPtr ↦ᵣ src))) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst + BitVec.ofNat 64 (4 * (n - (k + 1))) ∧
      st.readReg64 .x1 = srcPtr + BitVec.ofNat 64 (4 * (n - (k + 1))) ∧
      st.readReg64 .x2 = BitVec.ofNat 64 (k + 1))
    (fun k _ => (dst ↦ₛ ByteSlice.copyPrefix old src (4 * (n - (k + 1)))) ∗ (srcPtr ↦ᵣ src))
  case init => byte_region_entails
  case base =>
    wp_sym_steps
    wp_done
  case step =>
    right
    wp_sym_steps
    wp_done

/-! ## Byte-Broadcast Stores of 4, 2, and 1 Bytes -/

@[simp, arm64_norm] def bcast_store_addr : BitVec 64 := 0x5e600#64

/-- `str w1, [x0]; strh w1, [x0, #4]; strb w1, [x0, #6]; ret` at `0x5e600`. -/
def bcastStoreCode : FnCode :=
  .atAddr "bcast_store" bcast_store_addr ("b9000001 " ++ "79000801 " ++ "39001801 " ++ "d65f03c0")

theorem bcast_store_test (prog : Program) (h_code : bcastStoreCode.holds prog)
    (s0 : State) (dst : BitVec 64) (bs : List (BitVec 8)) (b : BitVec 8) (k : Nat)
    (hk : k + 7 ≤ bs.length)
    (hpc : s0.pc = 0x5e600#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst + BitVec.ofNat 64 k)
    (hx1 : s0.readReg64 .x1 = ByteSlice.bcast64 b) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ ByteSlice.fillPrefix bs b k)
      (sepPost (fun _ => True) (dst ↦ₛ ByteSlice.fillPrefix bs b (k + 7))) := by
  wp_sym_steps
  wp_done

/-! ## Pointer-Compare Loop and `wp_bv_omega` with Register Definitions -/

section wp_bv_omega_tests

variable (s0 st : State) (dst a b : BitVec 64) (n m : Nat)

set_option linter.unusedVariables false in
set_option maxHeartbeats 30000 in
example (hdst : dst.toNat + n < 2 ^ 64) (h_1 : m + 1 < n)
    (h_2 : st.readReg64 (Reg.gpr 0#5) = dst)
    (h_3 : st.readReg64 (Reg.gpr 8#5) = dst + BitVec.ofNat 64 (n - (m + 1 + 1)))
    (h_4 : st.readReg64 (Reg.gpr 1#5) = a + BitVec.ofNat 64 (n - (m + 1 + 1)))
    (h_5 : st.readReg64 (Reg.gpr 9#5) = dst + BitVec.ofNat 64 n)
    (h_6 : st.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5))
    (h_7 : st.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5))
    (h_8 : st.readReg64 (Reg.gpr 29#5) = s0.readReg64 (Reg.gpr 29#5))
    (h_9 : st.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5))
    (hcond : dst + BitVec.ofNat 64 (n - (m + 1 + 1)) + 1#64 ≠ dst + BitVec.ofNat 64 n) :
    dst + BitVec.ofNat 64 (n - (m + 1 + 1)) + 1#64 = dst + BitVec.ofNat 64 (n - (m + 1)) := by
  wp_bv_omega

example (h : st.readReg64 (Reg.gpr 0#5) = a + 1#64) : st.readReg64 (Reg.gpr 0#5) - 1#64 = a := by
  wp_bv_omega

example (h1 : st.readReg64 .x1 = a + 2#64) (h2 : st.readReg64 .x2 = st.readReg64 .x1 + 2#64) :
    st.readReg64 .x2 = a + 4#64 := by
  wp_bv_omega

example (h1 : st.readReg64 .x3 = a) (h2 : st.readReg64 .x3 = b) : a = b := by
  wp_bv_omega

example (_h1 : st.readReg64 .x3 = a) : True := by
  fail_if_success have : a = b := by wp_bv_omega
  trivial

end wp_bv_omega_tests

@[simp, arm64_norm] def byte_copy_cmp_addr : BitVec 64 := 0x5e500#64

/-- Byte copy until cursor `x8` reaches end pointer `x9` (`x1` = source cursor,
    `x0` = destination) at `0x5e500`:
    * `0x5e500`: `ldrb w10, [x1], #1`
    * `0x5e504`: `strb w10, [x8], #1`
    * `0x5e508`: `cmp x8, x9`
    * `0x5e50c`: `b.ne 0x5e500`
    * `0x5e510`: `ret` -/
def byteCopyCmpCode : FnCode :=
  .atAddr "byte_copy_cmp" byte_copy_cmp_addr
    ("3840142a " ++ -- 0x5e500: ldrb w10, [x1], #1
     "3800150a " ++ -- 0x5e504: strb w10, [x8], #1
     "eb09011f " ++ -- 0x5e508: cmp x8, x9
     "54ffffa1 " ++ -- 0x5e50c: b.ne 0x5e500
     "d65f03c0")    -- 0x5e510: ret

theorem byte_copy_cmp_loop_sym_test (prog : Program) (h_code : byteCopyCmpCode.holds prog)
    (s0 : State) (dst srcPtr : BitVec 64) (old src : List (BitVec 8)) (n : Nat)
    (hn0 : 0 < n) (hlen : old.length = n) (hslen : src.length = n)
    (hdst : dst.toNat + n < 2 ^ 64)
    (hpc : s0.pc = 0x5e500#64) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx8 : s0.readReg64 .x8 = dst)
    (hx1 : s0.readReg64 .x1 = srcPtr) (hx9 : s0.readReg64 .x9 = dst + BitVec.ofNat 64 n) :
    SepWP prog (s0.readReg64 .lr) s0 ((dst ↦ₛ old) ∗ (srcPtr ↦ₛ src))
      (sepPost (fun sf => sf.readReg64 .x0 = dst) ((dst ↦ₛ src) ∗ (srcPtr ↦ₛ src))) := by
  wp_loop_measure frame (n - 1) (fun k st =>
    k < n ∧ st.readReg64 .x0 = dst ∧
      st.readReg64 .x8 = dst + BitVec.ofNat 64 (n - (k + 1)) ∧
      st.readReg64 .x1 = srcPtr + BitVec.ofNat 64 (n - (k + 1)) ∧
      st.readReg64 .x9 = dst + BitVec.ofNat 64 n)
    (fun k _ => (dst ↦ₛ ByteSlice.copyPrefix old src (n - (k + 1))) ∗ (srcPtr ↦ₛ src))
  case init => byte_region_entails
  case base =>
    wp_sym_steps
    wp_done
  case step =>
    right
    wp_sym_steps
    wp_done

/-! ## Tail Copy of the Last 16 Bytes Next to a Chain of Writes -/

@[simp, arm64_norm] def tail16_copy_addr : BitVec 64 := 0x5e700#64

/-- Copy the last 16 bytes of `[x1, x1 + n)` to `[x0, x0 + n)` with `x4 = src + n` and
    `x5 = dst + n` at `0x5e700`:
    * `0x5e700`: `ldp x10, x11, [x4, #-16]`
    * `0x5e704`: `stp x10, x11, [x5, #-16]`
    * `0x5e708`: `ret` -/
def tail16CopyCode : FnCode :=
  .atAddr "tail16_copy" tail16_copy_addr
    ("a97f2c8a " ++ -- 0x5e700: ldp x10, x11, [x4, #-16]
     "a93f2caa " ++ -- 0x5e704: stp x10, x11, [x5, #-16]
     "d65f03c0")    -- 0x5e708: ret

set_option maxHeartbeats 400000 in
theorem last16_load_with_write_chain_test (prog : Program) (h_code : tail16CopyCode.holds prog)
    (st : State) (dst src n : BitVec 64) (old bs : List (BitVec 8)) (p : Nat)
    (hpc : st.pc = 0x5e700#64) (hrun : st.status = .Running)
    (_hx0 : st.readReg64 .x0 = dst) (_hx3 : st.readReg64 .x3 = dst + BitVec.ofNat 64 p - 16#64)
    (hx4 : st.readReg64 .x4 = src + n) (hx5 : st.readReg64 .x5 = dst + n)
    (hlen : old.length = n.toNat) (hslen : bs.length = n.toNat) (_hn128 : 128 < n.toNat)
    (_hn63 : n.toNat ≤ 2 ^ 63) (hp : p + 64 ≤ n.toNat) (_hcov : n.toNat ≤ p + 128) :
    SepWP prog (st.readReg64 .lr) st
      ((dst ↦ₛ ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
          (ByteSlice.write64 (ByteSlice.write64
            (ByteSlice.copySet old bs fun i => decide (i < 16) || decide (i < p)) p
            (ByteSlice.readLE bs p 8)) (p + 8) (ByteSlice.readLE bs (p + 8) 8))
          (p + 16) (ByteSlice.readLE bs (p + 16) 8)) (p + 24) (ByteSlice.readLE bs (p + 24) 8))
          (p + 32) (ByteSlice.readLE bs (p + 32) 8)) (p + 40) (ByteSlice.readLE bs (p + 40) 8)) ∗
        (src ↦ᵣ bs))
      (sepPost (fun _ => True)
        ((dst ↦ₛ ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
            (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64 (ByteSlice.write64
              (ByteSlice.copySet old bs fun i => decide (i < 16) || decide (i < p)) p
              (ByteSlice.readLE bs p 8)) (p + 8) (ByteSlice.readLE bs (p + 8) 8))
            (p + 16) (ByteSlice.readLE bs (p + 16) 8)) (p + 24) (ByteSlice.readLE bs (p + 24) 8))
            (p + 32) (ByteSlice.readLE bs (p + 32) 8)) (p + 40) (ByteSlice.readLE bs (p + 40) 8))
            (n.toNat - 16) (ByteSlice.readLE bs (n.toNat - 16) 8))
            (n.toNat - 8) (ByteSlice.readLE bs (n.toNat - 8) 8)) ∗
          (src ↦ᵣ bs))) := by
  wp_steps
  wp_done

end Testing.ByteRegion
