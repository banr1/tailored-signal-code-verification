/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Proofs.MemsetSymCommon
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Large Sizes of `musl` `memset.S`

Proves `memset_sym_large`, the `96 < n` path of `musl`'s AArch64 `memset.S` over raw memory using
the `PrefixFilled` invariant across the 16-byte head store, the 64-byte `dc zva` or `stp` loop,
and the 64-byte tail store at `dst + n - 64`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

/-! ## Arithmetic helpers -/

def MemsetAligned64 (x : BitVec 64) : Prop :=
  x &&& 0xffffffffffffffc0#64 = x

theorem MemsetAligned64.add_64 {x : BitVec 64} (h : MemsetAligned64 x) :
    MemsetAligned64 (x + 64#64) := by
  unfold MemsetAligned64 at *
  bv_bits

theorem memset_and_15_lt (dst : BitVec 64) : (dst &&& 15#64).toNat < 16 := by
  have h : (dst &&& 15#64).ult 16#64 = true := by bv_bits
  simpa [BitVec.ult] using h

theorem memset_and_63_lt (dst : BitVec 64) : (dst &&& 63#64).toNat < 64 := by
  have h : (dst &&& 63#64).ult 64#64 = true := by bv_bits
  simpa [BitVec.ult] using h

theorem memset_and_15_le_and_63 (dst : BitVec 64) :
    (dst &&& 15#64).toNat ≤ (dst &&& 63#64).toNat := by
  have h : (dst &&& 15#64).ule (dst &&& 63#64) = true := by bv_bits
  simpa [BitVec.ule] using h

theorem memset_and_mask16_eq_sub (dst : BitVec 64) :
    dst &&& -16#64 = dst - BitVec.ofNat 64 (dst &&& 15#64).toNat := by
  have h1 : dst &&& -16#64 = dst - (dst &&& 15#64) := by bv_bits
  have h2 : BitVec.ofNat 64 (dst &&& 15#64).toNat = dst &&& 15#64 := by bv_arith
  rw [h1, h2]

theorem memset_and_mask64_of_sub_and15 (dst : BitVec 64) :
    (dst - (dst &&& 15#64)) &&& -64#64 = dst - BitVec.ofNat 64 (dst &&& 63#64).toNat := by
  have h1 : (dst - (dst &&& 15#64)) &&& -64#64 = dst - (dst &&& 63#64) := by bv_bits
  have h3 : BitVec.ofNat 64 (dst &&& 63#64).toNat = dst &&& 63#64 := by bv_arith
  rw [h1, h3]

theorem MemsetAligned64.dst_add_sub_and63 (dst : BitVec 64) :
    MemsetAligned64 (dst + BitVec.ofNat 64 (64 - (dst &&& 63#64).toNat)) := by
  have hlt : (dst &&& 63#64).toNat < 64 := memset_and_63_lt dst
  have heq : BitVec.ofNat 64 (64 - (dst &&& 63#64).toNat) = 64#64 - (dst &&& 63#64) := by
    bv_arith
  unfold MemsetAligned64
  rw [heq]
  bv_bits

theorem memset_trunc32_and255_eq_zero {c : BitVec 64} (h : c.truncate 8 = 0#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) = 0#32 := by
  bv_bits

theorem memset_trunc32_and255_bne_zero {c : BitVec 64} (h : c.truncate 8 ≠ 0#8) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) != 0#32) =
      true := by
  cases hbne : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64)
      != 0#32)
  · exfalso; apply h
    have heq : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 c) &&& 255#64) =
        0#32 := by simpa [bne] using hbne
    bv_bits
  · rfl

theorem memset_simdStoreRegs_dcZva (ea : BitVec 64) (m : Memory) :
    simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m =
      (((((((m.write64 ea 0#64).write64 (ea + 8#64) 0#64).write64
        (ea + 16#64) 0#64).write64 (ea + 16#64 + 8#64) 0#64).write64
        (ea + 16#64 + 16#64) 0#64).write64 (ea + 16#64 + 16#64 + 8#64) 0#64).write64
        (ea + 16#64 + 16#64 + 16#64) 0#64).write64 (ea + 16#64 + 16#64 + 16#64 + 8#64) 0#64 :=
  rfl

theorem PrefixFilled.memset_step_dcZva {m₀ m : Memory} {dst v ea : BitVec 64}
    {k' len : Nat} (k off : Nat)
    (hv0 : v.truncate 8 = 0#8)
    (hoff_le : off ≤ k) (hoff_len : off + 64 ≤ len) (hlen : len ≤ 2 ^ 64) (hk' : off + 64 = k')
    (hea : ea = dst + BitVec.ofNat 64 off)
    (h : PrefixFilled m₀ m dst v k len) :
    PrefixFilled m₀ (simdStoreRegs SimdMemSize.Q128 (fun _ => 0#128) 4 0#5 ea m) dst v k' len := by
  rw [memset_simdStoreRegs_dcZva]
  exact h.memset_step512_zero k off hv0 hoff_le hoff_len hlen hk' hea rfl rfl rfl rfl rfl rfl rfl

/-! ## Loops and tails -/

section Large
variable (prog : Program) (a : BitVec 64) (hc : prog.hasCode a memsetWordsSym)
  (m₀ : Memory) (dst c n : BitVec 64) (hrw : m₀.RW dst n.toNat) (s0 : State)
  (Post : State → Prop)
  (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
    sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
    PrefixFilled m₀ sf.mem dst c n.toNat n.toNat → Post sf)
include hc hrw hpost

theorem memset_stp_loop (hlen : n.toNat ≤ 2 ^ 64) :
    ∀ (fuel k : Nat) (rem : BitVec 64) (s : State),
      (rem.toNat - 1) / 64 ≤ fuel → 1 ≤ rem.toNat → k + rem.toNat + 64 = n.toNat →
      s.pc = a + 0xe8#64 → s.status = .Running →
      s.readReg64 .x0 = dst → s.readReg64 .x2 = rem →
      s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 32#64 → s.readReg64 .x4 = dst + n →
      s.readVReg128 0#5 = memsetDup16 c → MemsetLeafPreserved s0 s →
      PrefixFilled m₀ s.mem dst c k n.toNat →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
  intro fuel
  induction fuel with
  | zero =>
    intro k rem s hfuel hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hbhi : (64#64).ult rem = false := by bv_arith
    arm64_step_inst -- stp q0, q0, [x3, #32]
    arm64_step_inst -- stp q0, q0, [x3, #64]!
    arm64_step_inst -- subs x2, x2, #64
    arm64_step_inst -- b.hi (not taken)
    arm64_step_inst -- stp q0, q0, [x4, #-64]
    arm64_step_inst -- stp q0, q0, [x4, #-32]
    arm64_step_inst -- ret
    refine reaches_pc_refl (by simpa [arm64_norm] using hcc.2) (by simp [arm64_norm, hrun]) ?_
    apply hpost _ (by simpa [arm64_norm] using hcc.2) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc)
    dsimp only [State.setMem]
    refine PrefixFilled.memset_step512 (k + 64) (n.toNat - 64) (by omega) (by omega) hlen
      (by omega) (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith) ?_
    exact PrefixFilled.memset_step512 k k (by omega) (by omega) hlen rfl
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
      (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith) hfc
  | succ fuel ih =>
    intro k rem s hfuel hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    by_cases hrem_le : rem.toNat ≤ 64
    · exact ih k rem s (by omega) hrem_pos hk_eq hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hbhi : (64#64).ult rem = true := by bv_arith
    arm64_step_inst -- stp q0, q0, [x3, #32]
    arm64_step_inst -- stp q0, q0, [x3, #64]!
    arm64_step_inst -- subs x2, x2, #64
    arm64_step_inst -- b.hi (taken)
    have hrem_sub : (rem - 64#64).toNat = rem.toNat - 64 := by bv_omega
    refine ih (k + 64) (rem - 64#64) _ (by omega) (by omega) (by omega)
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm]) ?_
      (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
    · simp only [arm64_norm]; bv_arith
    · dsimp only [State.setMem]
      exact PrefixFilled.memset_step512 k k (by omega) (by omega) hlen rfl
        (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
        (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith) hfc

theorem memset_zva_tail (hlen : n.toNat ≤ 2 ^ 64) (s : State) (k : Nat)
    (hn64 : 64 ≤ n.toNat) (hk_cover : n.toNat ≤ k + 64) (hk_le : k ≤ n.toNat)
    (hpc : s.pc = a + 0xd0#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst) (hx4 : s.readReg64 .x4 = dst + n)
    (hv0 : s.readVReg128 0#5 = memsetDup16 c) (hcc : MemsetLeafPreserved s0 s)
    (hfc : PrefixFilled m₀ s.mem dst c k n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  arm64_step_inst -- stp q0, q0, [x4, #-64]
  arm64_step_inst -- stp q0, q0, [x4, #-32]
  arm64_step_inst -- ret
  refine reaches_pc_refl (by simpa [arm64_norm] using hcc.2) (by simp [arm64_norm, hrun]) ?_
  apply hpost _ (by simpa [arm64_norm] using hcc.2) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0])
    (by simp (config := { decide := true }) only [arm64_norm]; exact hcc)
  dsimp only [State.setMem]
  exact PrefixFilled.memset_step512 k (n.toNat - 64) (by omega) (by omega) hlen (by omega)
    (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith)
    (by bv_arith) (by bv_arith) (by bv_arith) (by bv_arith) hfc

theorem memset_zva_loop (hlen : n.toNat ≤ 2 ^ 64) (hc0 : c.truncate 8 = 0#8) :
    ∀ (fuel k : Nat) (rem : BitVec 64) (s : State),
      (rem.toNat - 1) / 64 ≤ fuel → 1 ≤ rem.toNat → k + rem.toNat + 64 = n.toNat →
      MemsetAligned64 (dst + BitVec.ofNat 64 k) →
      s.pc = a + 0xc0#64 → s.status = .Running →
      s.readReg64 .x0 = dst → s.readReg64 .x2 = rem →
      s.readReg64 .x3 = dst + BitVec.ofNat 64 k - 64#64 → s.readReg64 .x4 = dst + n →
      s.readVReg128 0#5 = memsetDup16 c → MemsetLeafPreserved s0 s →
      PrefixFilled m₀ s.mem dst c k n.toNat →
      reaches_pc prog (s0.readReg64 .lr) s Post := by
  intro fuel
  induction fuel with
  | zero =>
    intro k rem s hfuel hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hbhi : (64#64).ult rem = false := by bv_arith
    arm64_step_inst -- add x3, x3, #64
    have halign' : (dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64 =
        dst + BitVec.ofNat 64 k := halign
    have hcw : s.mem.canWrite ((dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64) 64 = true := by
      rw [halign']
      exact hrw_s.canWrite_sub (by bv_arith) hlen
    arm64_step_inst -- dc zva, x3
    clear hcw halign'
    arm64_step_inst -- subs x2, x2, #64
    arm64_step_inst -- b.hi (not taken)
    refine memset_zva_tail prog a hc m₀ dst c n hrw s0 Post hpost hlen _ (k + 64)
      (by omega) (by omega) (by omega)
      (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
    dsimp only [State.setMem]
    exact PrefixFilled.memset_step_dcZva k k hc0 (by omega) (by omega) hlen rfl (by bv_arith) hfc
  | succ fuel ih =>
    intro k rem s hfuel hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    by_cases hrem_le : rem.toNat ≤ 64
    · exact ih k rem s (by omega) hrem_pos hk_eq halign hpc hrun hx0 hx2 hx3 hx4 hv0 hcc hfc
    have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
    have hbhi : (64#64).ult rem = true := by bv_arith
    arm64_step_inst -- add x3, x3, #64
    have halign' : (dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64 =
        dst + BitVec.ofNat 64 k := halign
    have hcw : s.mem.canWrite ((dst + BitVec.ofNat 64 k) &&& 0xffffffffffffffc0#64) 64 = true := by
      rw [halign']
      exact hrw_s.canWrite_sub (by bv_arith) hlen
    arm64_step_inst -- dc zva, x3
    clear hcw halign'
    arm64_step_inst -- subs x2, x2, #64
    arm64_step_inst -- b.hi (taken)
    have hrem_sub : (rem - 64#64).toNat = rem.toNat - 64 := by bv_omega
    have halign_next : MemsetAligned64 (dst + BitVec.ofNat 64 (k + 64)) := by
      rw [show dst + BitVec.ofNat 64 (k + 64) = (dst + BitVec.ofNat 64 k) + 64#64 by bv_arith]
      exact halign.add_64
    refine ih (k + 64) (rem - 64#64) _ (by omega) (by omega) (by omega) halign_next
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm]) ?_
      (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
    · simp only [arm64_norm]; bv_arith
    · dsimp only [State.setMem]
      exact PrefixFilled.memset_step_dcZva k k hc0 (by omega) (by omega) hlen rfl (by bv_arith) hfc

theorem memset_stp_setup (hn_gt : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (d0 : Nat) (hd0_lt : d0 < 16) (s : State)
    (hpc : s.pc = a + 0xdc#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst) (hx3 : s.readReg64 .x3 = dst - BitVec.ofNat 64 d0)
    (hx4 : s.readReg64 .x4 = dst + n) (hv0 : s.readVReg128 0#5 = memsetDup16 c)
    (hcc : MemsetLeafPreserved s0 s) (hfc : PrefixFilled m₀ s.mem dst c (16 - d0) n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  arm64_step_inst -- sub x2, x4, x3
  arm64_step_inst -- sub x3, x3, #16
  arm64_step_inst -- sub x2, x2, #80
  let rem := (dst + n) - (dst - BitVec.ofNat 64 d0) - 80#64
  have hrem_eq : rem.toNat = n.toNat + d0 - 80 := by dsimp only [rem]; bv_omega
  refine memset_stp_loop prog a hc m₀ dst c n hrw s0 Post hpost hlen
    ((rem.toNat - 1) / 64) (16 - d0) rem _ (Nat.le_refl _) (by omega) (by omega)
    (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, rem]) ?_
    (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
    (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) hfc
  simp only [arm64_norm]; bv_arith

theorem memset_zva_setup (hn_ge : 160 ≤ n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (hc0 : c.truncate 8 = 0#8) (s : State)
    (hpc : s.pc = a + 0x98#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = dst)
    (hx3 : s.readReg64 .x3 = dst - BitVec.ofNat 64 (dst &&& 15#64).toNat)
    (hx4 : s.readReg64 .x4 = dst + n) (hv0 : s.readVReg128 0#5 = memsetDup16 c)
    (hcc : MemsetLeafPreserved s0 s)
    (hfc : PrefixFilled m₀ s.mem dst c (16 - (dst &&& 15#64).toNat) n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  have hd0_lt : (dst &&& 15#64).toNat < 16 := memset_and_15_lt dst
  have hd64_lt : (dst &&& 63#64).toNat < 64 := memset_and_63_lt dst
  have hd0_le_d64 := memset_and_15_le_and_63 dst
  arm64_step_inst -- mrs x5, DCZID_EL0
  arm64_step_inst -- and x5, x5, #31
  arm64_step_inst -- cmp x5, #4
  arm64_step_inst -- b.ne (not taken)
  arm64_step_inst -- str q0, [x3, #16]
  arm64_step_inst -- stp q0, q0, [x3, #32]
  arm64_step_inst -- and x3, x3, #~63
  arm64_step_inst -- sub x2, x4, x3
  arm64_step_inst -- sub x2, x2, #128
  arm64_step_inst -- nop
  have hx3_64 := memset_and_mask64_of_sub_and15 dst
  let d0 := (dst &&& 15#64).toNat
  let d64 := (dst &&& 63#64).toNat
  let rem := (dst + n) - ((dst - (dst &&& 15#64)) &&& -64#64) - 128#64
  have hrem_eq : rem.toNat = n.toNat + d64 - 128 := by
    dsimp only [rem, d64]; rw [hx3_64]; bv_omega
  refine memset_zva_loop prog a hc m₀ dst c n hrw s0 Post hpost hlen hc0
    ((rem.toNat - 1) / 64) (64 - d64) rem _ (Nat.le_refl _) (by omega) (by omega)
    (MemsetAligned64.dst_add_sub_and63 dst)
    (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, rem]) ?_
    (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
    (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) ?_
  · simp only [arm64_norm]; dsimp only [d64]; rw [hx3_64]; bv_arith
  · dsimp only [State.setMem]
    refine PrefixFilled.mono (k := 64 - d0) ?_ (by omega)
    have h64 : 64 - d0 = 16 - d0 + 16 + 16 + 16 := by omega
    rw [h64]
    refine PrefixFilled.memset_step128 (16 - d0 + 16 + 16) (48 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) ?_
    refine PrefixFilled.memset_step128 (16 - d0 + 16) (32 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) ?_
    exact PrefixFilled.memset_step128 (16 - d0) (16 - d0)
      (by omega) (by omega) hlen (by omega) (by bv_arith) (by bv_arith) hfc

theorem memset_large_branch (hn_gt : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64) (s : State)
    (hpc : s.pc = a + 0x80#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = c)
    (hx2 : s.readReg64 .x2 = n) (hx4 : s.readReg64 .x4 = dst + n)
    (hv0 : s.readVReg128 0#5 = memsetDup16 c)
    (hcc : MemsetLeafPreserved s0 s) (hfc : PrefixFilled m₀ s.mem dst c 0 n.toNat) :
    reaches_pc prog (s0.readReg64 .lr) s Post := by
  have hlen : n.toNat ≤ 2 ^ 64 := by omega
  have hrw_s : s.mem.RW dst n.toNat := hfc.rw hrw
  have hd0_lt : (dst &&& 15#64).toNat < 16 := memset_and_15_lt dst
  have hand16 := memset_and_mask16_eq_sub dst
  arm64_step_inst -- and w1, w1, #0xff
  arm64_step_inst -- and x3, x0, #~15
  arm64_step_inst -- str q0, [x0]
  arm64_step_inst -- cmp x2, #160
  have hhead : PrefixFilled m₀ ((s.mem.write64 dst (memsetDup8 c)).write64 (dst + 8#64)
      (memsetDup8 c)) dst c (16 - (dst &&& 15#64).toNat) n.toNat :=
    (PrefixFilled.memset_step128 0 0 (by omega) (by omega) hlen rfl (by bv_arith) rfl hfc).mono
      (by omega)
  by_cases hn160 : 160 ≤ n.toNat
  · have hule160 : (160#64).ule n = true := by bv_arith
    by_cases hc0 : c.truncate 8 = 0#8
    · have hc0_32 := memset_trunc32_and255_eq_zero hc0
      arm64_step_inst -- ccmp w1, #0, #0, hs
      arm64_step_inst -- b.ne (not taken)
      exact memset_zva_setup prog a hc m₀ dst c n hrw s0 Post hpost hn160 hn_le hc0 _
        (by simp only [arm64_norm]; bv_arith) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) hhead
    · have hbne0 := memset_trunc32_and255_bne_zero hc0
      arm64_step_inst -- ccmp w1, #0, #0, hs
      arm64_step_inst -- b.ne (taken)
      exact memset_stp_setup prog a hc m₀ dst c n hrw s0 Post hpost hn_gt hn_le
        (dst &&& 15#64).toNat hd0_lt _
        (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
        (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
        (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) hhead
  · have hule160 : (160#64).ule n = false := by bv_arith
    arm64_step_inst -- ccmp w1, #0, #0, hs
    arm64_step_inst -- b.ne (taken)
    exact memset_stp_setup prog a hc m₀ dst c n hrw s0 Post hpost hn_gt hn_le
      (dst &&& 15#64).toNat hd0_lt _
      (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hx0]) (by simp [arm64_norm])
      (by simp [arm64_norm, hx4]) (by simp [arm64_norm, hv0])
      (by simp (config := { decide := true }) only [arm64_norm]; exact hcc) hhead

end Large

/-- Large sizes (`96 < n`) of `memset`: starting at `s0.pc = a` with writable `[dst, dst + n)`,
    execution reaches `s0.readReg64 .lr` with `x0 = dst`, `MemsetLeafPreserved s0 sf`, and
    `PrefixFilled s0.mem sf.mem dst c n.toNat n.toNat`. -/
theorem memset_sym_large (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (s0 : State) (Post : State → Prop)
    (dst c n : BitVec 64)
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
    (hx2 : s0.readReg64 .x2 = n)
    (hrw : s0.mem.RW dst n.toNat)
    (hn96 : 96 < n.toNat) (hn_le : n.toNat + 260 ≤ 2 ^ 64)
    (hpost : ∀ sf : State, sf.pc = s0.readReg64 .lr → sf.status = .Running →
      sf.readReg64 .x0 = dst → MemsetLeafPreserved s0 sf →
      PrefixFilled s0.mem sf.mem dst c n.toNat n.toNat →
      Post sf) :
    reaches_pc prog (s0.readReg64 .lr) s0 Post := by
  have hfc0 : PrefixFilled s0.mem s0.mem dst c 0 n.toNat := PrefixFilled.zero s0.mem dst c n.toNat
  arm64_step_inst -- dup v0.16b, w1
  arm64_step_inst -- add x4, x0, x2
  arm64_step_inst -- cmp x2, #96
  have hbhi96 : (96#64).ult n = true := by bv_arith
  arm64_step_inst -- b.hi (taken)
  exact memset_large_branch prog a hc s0.mem dst c n hrw s0 Post hpost hn96 hn_le _
    (by simp only [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx1])
    (by simp [arm64_norm, hx2]) (by simp [arm64_norm])
    (by simp only [arm64_norm]; exact memsetDup16_expand c)
    (by simp (config := { decide := true }) only [arm64_norm]) hfc0

end VerifiedLibraries.Musl
