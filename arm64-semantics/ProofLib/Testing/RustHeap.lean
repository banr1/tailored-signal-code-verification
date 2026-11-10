/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ObjectLoad
public import ProofLib.GenDecodes
public import ProofLib.Abi.Rust.Heap
public import ProofLib.GlobalAlloc

/-!
# Rust Heap and Allocator Tests

Tests the Rust global allocator interface (`RustAlloc`, `GlobalAlloc`, `LayoutOk`, `SmallLen`),
`Vec` and `Box` representation predicates (`vecAt`, `vecU8At`, `boxAt`, `boxU8At`), and
`wp_bv_omega` hypothesis pruning on a small `Vec<u64>` program.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.RustHeap

open Arm64
open _root_.ProofLib
open _root_.ProofLib.ProgramReflection
open _root_.ProofLib.GenDecodes
open _root_.ProofLib.RustHeap

/-! ## `Vec<u64>` Test Program -/

/-
Two subroutines on a `Vec<u64>` at `x0` (`{cap, ptr, len}` header at `+0, +8, +16`):
- `vec_u64_len` (offset `0x00`):
    0x00: ldr x0, [x0, #16]   (0xf9400800)
    0x04: ret                 (0xd65f03c0)
- `vec_u64_set0` (offset `0x08`):
    0x08: ldr x8, [x0, #8]    (0xf9400408)
    0x0c: str x1, [x8]        (0xf9000101)
    0x10: ret                 (0xd65f03c0)
    0x14: udf #0              (0x00000000) -- padding to 6 words
-/
def vecToyRawProg_tree : WordTree :=
  .node 2
    (.node 1
      (.leaf 0x00#8 0x08#8 0x40#8 0xf9#8)  -- 0x00: ldr x0, [x0, #16]
      (.leaf 0xc0#8 0x03#8 0x5f#8 0xd6#8)) -- 0x04: ret
    (.node 1
      (.leaf 0x08#8 0x04#8 0x40#8 0xf9#8)  -- 0x08: ldr x8, [x0, #8]
      (.node 1
        (.leaf 0x01#8 0x01#8 0x00#8 0xf9#8)  -- 0x0c: str x1, [x8]
        (.leaf 0xc0#8 0x03#8 0x5f#8 0xd6#8))) -- 0x10: ret

def vecToyRawProg : Program :=
  { base := 0#64
    code := vecToyRawProg_tree.toBytes
    symbols := [
      ("vec_u64_len",  0x00),
      ("vec_u64_set0", 0x08)
    ]
    stubs := [] }

@[simp, arm64_norm]
theorem vecToyRawProg_fnOff_len : vecToyRawProg.fnOff "vec_u64_len" = 0x00 := rfl

@[simp, arm64_norm]
theorem vecToyRawProg_fnOff_set0 : vecToyRawProg.fnOff "vec_u64_set0" = 0x08 := rfl

theorem vecToyRawProg_fetch_at (off : Nat) (inst : Instr)
    (h : vecToyRawProg_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64) :
    vecToyRawProg.fetch (BitVec.ofNat 64 off) = some inst := by
  simpa [vecToyRawProg] using
    fetch_of_wordTree (prog := vecToyRawProg) (t := vecToyRawProg_tree) 5 rfl rfl h hoff
      (hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) off)

theorem vecToyRawProg_fetch_rebase_text (b : BitVec 64) (X : String → Option (State → State))
    (off : Nat) (inst : Instr) (h : vecToyRawProg_tree.fetchDecodeAt off = some inst)
    (htext : off < 20) (hoff : off < 2 ^ 64) :
    (vecToyRawProg.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_of_noStubBefore (P := vecToyRawProg) rfl (fun _ => rfl) (fun _ => rfl)
    rfl b X htext hoff).trans (vecToyRawProg_fetch_at off inst h hoff)

gen_fetches vecToyRawProg vecToy 20 true [0 → 16]

@[irreducible, wp_unfold]
def vecToyProg (b : BitVec 64) : Program :=
  vecToyRawProg.rebase b

abbrev elemU64 (w : BitVec 64) (addr : BitVec 64) : SepProp :=
  addr ↦₆₄ w

abbrev vecU64At (A : RustAlloc) (v cap ptr : BitVec 64) (ws : List (BitVec 64)) : SepProp :=
  vecAt A 8 8 elemU64 v cap ptr ws

structure VecU64LenGhost where
  v   : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  ws  : List (BitVec 64)

/-- Contract for `vec_u64_len`: returns `ws.length` in `x0` and keeps `vecU64At` intact. -/
def vecU64LenSpec (A : RustAlloc) : Spec VecU64LenGhost :=
  { pre  := fun g s =>
      ⌜s.readReg64 .x0 = g.v⌝ ∗ vecU64At A g.v g.cap g.ptr g.ws
    post := fun g s0 sf =>
      ⌜sf.readReg64 .x0 = BitVec.ofNat 64 g.ws.length ∧ sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf⌝ ∗
        vecU64At A g.v g.cap g.ptr g.ws }

theorem vec_u64_len_ok (b : BitVec 64) (A : RustAlloc) :
    (vecToyProg b).subroutineOk "vec_u64_len" (vecU64LenSpec A) := by
  wp_init g s0
  unfold vecU64At vecAt vecHeader
  wp_steps
  wp_done

structure VecU64Set0Ghost where
  v   : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  ws  : List (BitVec 64)
  x   : BitVec 64

/-- Contract for `vec_u64_set0`: when `0 < ws.length`, overwrites `ws[0]` with `x` in place. -/
def vecU64Set0Spec (A : RustAlloc) : Spec VecU64Set0Ghost :=
  { pre  := fun g s =>
      ⌜s.readReg64 .x0 = g.v ∧ s.readReg64 .x1 = g.x ∧ 0 < g.ws.length⌝ ∗
        vecU64At A g.v g.cap g.ptr g.ws
    post := fun g s0 sf =>
      ⌜sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf⌝ ∗
        vecU64At A g.v g.cap g.ptr (g.ws.set 0 g.x) }

theorem vec_u64_set0_ok (b : BitVec 64) (A : RustAlloc) :
    (vecToyProg b).subroutineOk "vec_u64_set0" (vecU64Set0Spec A) := by
  wp_init g s0
  have hpos : 0 < g.ws.length := ‹_›
  unfold vecU64At vecAt vecHeader
  apply SepWP.weaken_pre (sepConj_mono_right (vecBuf_split_at A 8 8 elemU64 g.cap g.ptr g.ws hpos))
  dsimp only [elemU64]
  have hzero : g.ptr + BitVec.ofNat 64 (0 * 8) = g.ptr := by bv_omega
  rw [hzero]
  wp_steps
  simp only [List.length_set]
  have hset := vecBuf_set A 8 8 elemU64 g.cap g.ptr g.ws hpos g.x
  simp only [elemU64, hzero] at hset
  apply SepWP.weaken_pre (sepConj_mono_right hset)
  wp_done

/-! ## Allocator, Layout, and `Vec` Algebra Tests -/

example (size : Nat) (hpos : 0 < size) (hle : size + 8 ≤ 2 ^ 63) :
    LayoutOk size 8 ∧ SmallLen size := by
  have hl : LayoutOk size 8 := LayoutOk.align_8 hpos hle
  exact ⟨hl, hl.size_small⟩

example (s0 sf : State) (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf :=
  allocFailedIn_append_singleton h

example (s0 sf : State) (h : sf.trace = s0.trace) :
    ¬ allocFailedIn s0 sf :=
  not_allocFailedIn_of_trace_eq h

example (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecAt A 1 1 (fun b a => a ↦₈ b) v cap ptr bs :=
  vecU8At_eq_vecAt A v cap ptr bs

example (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8At A ptr bs = boxAt A 1 1 (fun b a => a ↦₈ b) ptr bs :=
  boxU8At_eq_boxAt A ptr bs

example (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢
      memRegion v 24 ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat)) :=
  Entails.trans (vecU8At_entails_dealloc A v cap ptr bs)
    (sepConj_mono_left (vecHeader_entails_memRegion v cap ptr (BitVec.ofNat 64 bs.length)))

/-! ## `Arm64.Allocator` Invariant Checks -/

/-- `Allocator.live_noWrap` and `Allocator.live_field_ne_zero` extract non-wrapping
    (`p.toNat + sz ≤ 2 ^ 64`) and interior field non-nullness (`p + off ≠ 0#64`) from `A.live p sz`. -/
theorem allocator_live_noWrap_and_field_ne_zero_test (A : Arm64.Allocator)
    (p : BitVec 64) (off sz : Nat) (hp : p ≠ 0#64) (hoff : off < sz) :
    (A.live p sz ⊢ ⌜p.toNat + sz ≤ 2 ^ 64⌝ ∗ A.live p sz) ∧
    (A.live p sz ⊢ ⌜p + BitVec.ofNat 64 off ≠ 0#64⌝ ∗ A.live p sz) :=
  ⟨A.live_noWrap p sz, A.live_field_ne_zero p off sz hp hoff⟩

/--
error: Fields missing: `noWrap`
-/
#guard_msgs (substring := true) in
def badAllocatorMissingNoWrap : Arm64.Allocator :=
  { pool := emp, live := fun _ _ => emp }

/-! ## `Arm64.Rust.GlobalAlloc` Bridges and `wp_bv_omega` Pruning -/

/-- `wp_bv_omega` retains `Arm64.Rust.SmallLen`, `Arm64.Rust.LayoutOk`, and `Arm64.Rust.BudgetOk`
    in the local context instead of pruning them as heavy `Arm64.*` hypotheses. -/
theorem wp_bv_omega_keeps_globalAlloc_arith_hyps
    (n : Nat) (size align : BitVec 64)
    (maxAlign maxBytes maxBlocks liveBytes liveBlocks : Nat)
    (hsmall : Arm64.Rust.SmallLen n)
    (hlay : Arm64.Rust.LayoutOk size align)
    (hbud : Arm64.Rust.BudgetOk maxAlign maxBytes maxBlocks liveBytes liveBlocks size.toNat align.toNat) :
    n < 2 ^ 63 ∧
    size.toNat + align.toNat ≤ 2 ^ 63 ∧
    align.toNat ≤ maxAlign ∧
    liveBytes + size.toNat ≤ maxBytes ∧
    liveBlocks + 1 ≤ maxBlocks := by
  refine ⟨by wp_bv_omega, by wp_bv_omega, by wp_bv_omega, by wp_bv_omega, by wp_bv_omega⟩

-- When `n < 10` is bundled inside a hypothesis mentioning a non-allowlisted `Arm64.Rust` constant
-- (`Arm64.Rust.AllocStatePreserved s0 sf ∧ n < 10`), `omega` extracts `n < 10`, whereas
-- `wp_bv_omega` prunes `_hpres` via `isHeavyHypType` and fails.
example (s0 sf : State) (n : Nat)
    (_hpres : Arm64.Rust.AllocStatePreserved s0 sf ∧ n < 10) :
    n < 10 := by
  omega

/--
error: omega could not prove the goal
-/
#guard_msgs (substring := true) in
example (s0 sf : State) (n : Nat)
    (_hpres : Arm64.Rust.AllocStatePreserved s0 sf ∧ n < 10)
    (hsmall : Arm64.Rust.SmallLen n) :
    n < 10 := by
  wp_bv_omega

/-- `GlobalAlloc` bridges to `vec_u64_len_ok` and `vec_u64_set0_ok` via `A.toRustAlloc` and
    transports `A.Heap` across register and memory writes. -/
theorem globalAlloc_vec_and_transport_bridge
    {P : Program} {addrs : Arm64.Rust.GlobalAllocAddrs}
    (A : Arm64.Rust.GlobalAlloc P addrs) (b : BitVec 64)
    (liveBytes liveBlocks : Nat) (s : State) (a : BitVec 64) (v : BitVec 64) :
    (vecToyProg b).subroutineOk "vec_u64_len" (vecU64LenSpec A.toRustAlloc) ∧
    (vecToyProg b).subroutineOk "vec_u64_set0" (vecU64Set0Spec A.toRustAlloc) ∧
    A.Heap liveBytes liveBlocks (s.setMem (s.mem.write64 a v)) = A.Heap liveBytes liveBlocks s :=
  ⟨vec_u64_len_ok b A.toRustAlloc,
   vec_u64_set0_ok b A.toRustAlloc,
   A.heap_transport liveBytes liveBlocks s (s.setMem (s.mem.write64 a v))
     (Arm64.Rust.VmPreserved.setMem_write64 s a v)⟩

/-! ## Axiom Audit -/

/--
info: 'Examples.Testing.ProofLib.RustHeap.vec_u64_len_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms vec_u64_len_ok

/--
info: 'Examples.Testing.ProofLib.RustHeap.vec_u64_set0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms vec_u64_set0_ok

end Examples.Testing.ProofLib.RustHeap

end
