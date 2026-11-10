/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.SepLogic.LoopTactics
public import VerifiedLibraries.Musl.Proofs.MemsetSymCommon
public import VerifiedLibraries.Musl.Proofs.MemsetLargeSym
public meta import ProofLib.SepLogic.LoopTactics

/-!
# Symbolic Verification of `musl` `memset`

Symbolic execution proof of `musl` v1.2.5's AArch64 `src/string/aarch64/memset.S` against
`memsetSymSpec`. Sizes `n <= 96` are proved as `SepWP` triples over `dst ↦ₛ bs` (`memset_sepWP_le96`),
and sizes `96 < n` delegate to `memset_sym_large`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 ProofLib

abbrev MemsetFinal (s0 : State) (dst : BitVec 64) (sf : State) : Prop :=
  sf.readReg64 .x0 = dst ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-! ## Byte-list lemmas -/

theorem memset_write64_fillSet_zero (bs : List (BitVec 8)) (p : Nat → Bool) (off : Nat)
    (h : off + 8 ≤ bs.length) :
    ByteSlice.write64 (ByteSlice.fillSet bs 0#8 p) off 0#64 =
      ByteSlice.fillSet bs 0#8 (fun i => p i || (decide (off ≤ i) && decide (i < off + 8))) :=
  ByteSlice.writeLE_fillSet 8 bs 0#8 p off 0#64 h (fun j _ => by ext k hk; simp)

theorem memset_write64_zero (bs : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ bs.length) :
    ByteSlice.write64 bs off 0#64 =
      ByteSlice.fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 8)) := by
  have := memset_write64_fillSet_zero bs (fun _ => false) off h
  rw [ByteSlice.fillSet_false] at this
  simpa only [Bool.false_or] using this

theorem memset_fillSet_fillSet (bs : List (BitVec 8)) (b : BitVec 8) (p q : Nat → Bool) :
    ByteSlice.fillSet (ByteSlice.fillSet bs b p) b q =
      ByteSlice.fillSet bs b (fun i => p i || q i) := by
  apply ByteSlice.ext_getD (by simp)
  intro i hi
  simp only [ByteSlice.fillSet_length] at hi
  simp only [ByteSlice.getD_fillSet, ByteSlice.fillSet_length, hi, decide_true, Bool.and_true]
  cases p i <;> cases q i <;> simp

theorem memset_lo64 (hi lo : BitVec 64) :
    BitVec.setWidth 64 ((hi ++ lo) >>> 0 &&& 18446744073709551615#128) = lo := by
  bv_slice

theorem memset_truncate16_truncate32 (x : BitVec 64) :
    (x.truncate 32).truncate 16 = x.truncate 16 := by
  ext i hi
  simp [BitVec.getElem_setWidth]

theorem memset_dup_chain (c : BitVec 64) :
    (0#128 ||| (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 0 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 8 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 16 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 24 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 32 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 40 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 48 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 56 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 64 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 72 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 80 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 88 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 96 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 104 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 112 |||
      (BitVec.setWidth 128 c &&& 255#128 &&& 255#128) <<< 120) =
      ByteSlice.bcast64 (c.truncate 8) ++ ByteSlice.bcast64 (c.truncate 8) := by
  unfold ByteSlice.bcast64
  bv_slice

/-! ## Byte-fill closers -/

/-- Collapse a chain of broadcast / zero stores over `bs` into a single `fillSet`. -/
macro "memset_fill_collapse" : tactic =>
  `(tactic| try simp (disch := byte_region_len) only [ByteSlice.write64_fillSet_bcast64,
    ByteSlice.write64_bcast64, memset_write64_fillSet_zero, memset_write64_zero,
    memset_fillSet_fillSet])

/-- Close `dst ↦ₛ L ⊢ dst ↦ₛ R` where `L` is a chain of broadcast stores / fills over `bs` and
    `R` is `List.replicate n b` or a `fillSet bs b q` covering the same bytes. -/
macro "memset_fill" : tactic =>
  `(tactic| (
    apply ProofLib.ByteSlice.entails_of_eq
    apply ProofLib.pointsToBytes_congr_bytes
    memset_fill_collapse
    first
    | (refine ByteSlice.fillSet_all (by omega) ?_
       intro i hi
       simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
       omega)
    | (refine ByteSlice.fillSet_congr ?_
       intro i hi
       rw [Bool.eq_iff_iff]
       simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
       omega)))

/-! ## Sizes `n <= 96` -/

section Small
variable (prog : Program) (a : BitVec 64) (hc : prog.hasCode a memsetWordsSym)
  (s0 : State) (dst c n : BitVec 64) (bs : List (BitVec 8))
  (hpc : s0.pc = a) (hrun : s0.status = .Running)
  (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
  (hx2 : s0.readReg64 .x2 = n) (hlen : bs.length = n.toNat)
include hc hpc hrun hx0 hx1 hx2 hlen

theorem memset_small8 (hn8 : 8 ≤ n.toNat) (hn16 : n.toNat < 16) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = true := by bv_bits
  wp_sym_steps
  wp_done

theorem memset_small4 (hn4 : 4 ≤ n.toNat) (hn8 : n.toNat < 8) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = false := by bv_bits
  have htbz2 : n.getLsbD 2 = true := by bv_bits
  wp_sym_steps
  simp (disch := byte_region_len) only [ByteSlice.write32_bcast64]
  wp_done

theorem memset_small2 (hn1 : 1 ≤ n.toNat) (hn4 : n.toNat < 4) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = false := by bv_arith
  have htbz3 : n.getLsbD 3 = false := by bv_bits
  have htbz2 : n.getLsbD 2 = false := by bv_bits
  have hn0 : (n == 0#64) = false := by bv_arith
  by_cases hn2 : 2 ≤ n.toNat
  · have h1 : n.getLsbD 1 = true := by bv_bits
    wp_sym_steps
    simp (disch := byte_region_len) only [memset_truncate16_truncate32,
      ByteSlice.write16_bcast64, ByteSlice.bcast64_truncate8]
    wp_done
  · have h1 : n.getLsbD 1 = false := by bv_bits
    wp_sym_steps
    simp (disch := byte_region_len) only [ByteSlice.bcast64_truncate8]
    wp_done

theorem memset_small0 (hn0 : n.toNat = 0) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hn : n = 0#64 := by bv_omega
  subst hn
  wp_sym_steps
  wp_done

theorem memset_medium16 (hn16 : 16 ≤ n.toNat) (hn64 : n.toNat < 64) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = true := by bv_arith
  have htbnz6 : n.getLsbD 6 = false := by bv_bits
  by_cases hn32 : 32 ≤ n.toNat
  · have htbz5 : n.getLsbD 5 = true := by bv_bits
    wp_sym_steps
    refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
      (by memset_fill) ?_
    wp_done
  · have htbz5 : n.getLsbD 5 = false := by bv_bits
    wp_sym_steps
    refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
      (by memset_fill) ?_
    wp_done

theorem memset_medium64 (hn64 : 64 ≤ n.toNat) (hn96 : n.toNat ≤ 96) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  have hdup := memset_dup_chain c
  have hlo := memset_lo64 (ByteSlice.bcast64 (c.truncate 8)) (ByteSlice.bcast64 (c.truncate 8))
  have hbhi96 : (96#64).ult n = false := by bv_arith
  have hule16 : (16#64).ule n = true := by bv_arith
  have htbnz6 : n.getLsbD 6 = true := by bv_bits
  wp_sym_steps
  refine SepWP.weaken_pre (P' := dst ↦ₛ List.replicate n.toNat (c.truncate 8))
    (by memset_fill) ?_
  wp_done

end Small

theorem memset_sepWP_le96 (prog : Program) (a : BitVec 64)
    (hc : prog.hasCode a memsetWordsSym)
    (s0 : State) (dst c n : BitVec 64) (bs : List (BitVec 8))
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = c)
    (hx2 : s0.readReg64 .x2 = n) (hlen : bs.length = n.toNat) (hn96 : n.toNat ≤ 96) :
    SepWP prog (s0.readReg64 .lr) s0 (dst ↦ₛ bs)
      (sepPost (MemsetFinal s0 dst) (dst ↦ₛ List.replicate n.toNat (c.truncate 8))) := by
  by_cases hn64 : 64 ≤ n.toNat
  · exact memset_medium64 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn64 hn96
  by_cases hn16 : 16 ≤ n.toNat
  · exact memset_medium16 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn16 (by omega)
  by_cases hn8 : 8 ≤ n.toNat
  · exact memset_small8 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn8 (by omega)
  by_cases hn4 : 4 ≤ n.toNat
  · exact memset_small4 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn4 (by omega)
  by_cases hn1 : 1 ≤ n.toNat
  · exact memset_small2 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen hn1 (by omega)
  · exact memset_small0 prog a hc s0 dst c n bs hpc hrun hx0 hx1 hx2 hlen (by omega)

/-! ## Code-placement bounds from `CodeLoaded` -/

private theorem memset_codeLoaded_perm_rx {prog : Program} {m : Memory} {a : BitVec 64}
    {words : List (BitVec 32)} (hL : prog.CodeLoaded m) (hw : prog.hasWords a words)
    {j : Nat} (hj : j < 4 * words.length) :
    m.perm (a + BitVec.ofNat 64 j) = some Perm.rx := by
  have hget := Program.code_getElem?_of_hasWordsOff hw j hj
  have hflat : j < (words.flatMap Program.wordToBytesLE).length := by
    rw [Program.length_flatMap_wordToBytesLE]; exact hj
  rw [List.getElem?_eq_getElem hflat] at hget
  have hlt : (a - prog.base).toNat + j < prog.code.length :=
    Classical.byContradiction fun hge => by
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
  have hp := hL.perm_eq ((a - prog.base).toNat + j) hlt
  have haddr : prog.base + BitVec.ofNat 64 ((a - prog.base).toNat + j) =
      a + BitVec.ofNat 64 j := by bv_omega
  rwa [haddr] at hp

private theorem memset_rw_len_add_code_le {prog : Program} {m : Memory} {a dst : BitVec 64}
    {words : List (BitVec 32)} {n : Nat}
    (hL : prog.CodeLoaded m) (hw : prog.hasWords a words) (hrw : m.RW dst n)
    (hn : n ≤ 2 ^ 64) :
    n + 4 * words.length ≤ 2 ^ 64 := by
  have hnx : ∀ x, InRegion dst n x → m.perm x ≠ some Perm.rx := fun x hx => by
    rw [(Memory.permNoLazy_eq_some_rw_iff.mp (hrw x hx)).1]; decide
  by_cases hn0 : n = 0
  · subst hn0; have := hw.1; omega
  by_cases hw0 : words.length = 0
  · simp [hw0, hn]
  have h1 : n ≤ (a - dst).toNat :=
    Classical.byContradiction fun hlt =>
      hnx a (by unfold InRegion; omega) (by
        simpa using memset_codeLoaded_perm_rx hL hw (j := 0) (by omega))
  have h2 : 4 * words.length ≤ (dst - a).toNat :=
    Classical.byContradiction fun hlt => by
      have hp := memset_codeLoaded_perm_rx hL hw (j := (dst - a).toNat) (by omega)
      have haddr : a + BitVec.ofNat 64 (dst - a).toNat = dst := by bv_omega
      rw [haddr] at hp
      exact hnx dst (by unfold InRegion; simp; omega) hp
  bv_omega

/-! ## Spec-free `memset` contract -/

private theorem memset_readBytes_replicate (m : Memory) (b : BitVec 8) :
    ∀ (n : Nat) (base : BitVec 64), (∀ i, i < n → m.read8 (base + BitVec.ofNat 64 i) = b) →
      m.readBytes base n = List.replicate n b := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro base h
    rw [Memory.readBytes_succ, List.replicate_succ]
    congr 1
    · simpa using h 0 (by omega)
    · refine ih (base + 1) fun i hi => ?_
      have := h (i + 1) (by omega)
      rw [BitVec.add_assoc]
      have heq : (1 : BitVec 64) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) := by
        bv_omega
      rw [heq]; exact this

private theorem memset_readBytes_of_prefixFilled {m₀ mf : Memory} {dst c : BitVec 64} {n : Nat}
    (hfc : PrefixFilled m₀ mf dst c n n) :
    mf.readBytes dst n = List.replicate n (c.truncate 8) :=
  memset_readBytes_replicate mf _ n dst hfc.2

open Arm64.CType in
/-- Specification for `memset(dst, c, n)`: fills `n` bytes at `dst` with the low 8 bits of `c`
and returns `dst`. -/
c_type_spec memsetSymSpec (dst : ptr) (c : u32) (n : u64) : ptr where
  c_arg dst : UninitSlot n.toNat ⇝ MutSlice8 (List.replicate n.toNat (c.setWidth 8))
  c_arg c : Val U32
  c_arg n : Val SizeT
  returns dst

theorem memset_codeAt_ok_sym (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memsetWordsSym) :
    subroutine_ok prog a memsetSymSpec := by
  apply subroutine_ok_outcome_intro
  intro ⟨dst, c, n⟩ R s0 hpc hrun hpre _hsp
  simp only [memsetSymSpec, CType.Bytes, CType.MutSlice8, CType.U32, CType.SizeT,
    CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, _, _⟩, hmem⟩ := hpre
  have hlen64 : n.toNat ≤ 2 ^ 64 := by have := BitVec.isLt n; omega
  have htrunc : (s0.readReg64 .x1).truncate 8 = c.setWidth 8 := by
    have h32 : (s0.readReg64 .x1).truncate 32 = c := hx1
    rw [← h32]
    bv_bits
  refine reaches_outcome_of_reaches_pc (oom := fun _ => False) ?_
  by_cases hn96 : n.toNat ≤ 96
  ·
    rw [memRegion_eq_exists_bytes dst n.toNat hlen64, sepExists_sepConj_left,
      satisfies_sepExists] at hmem
    obtain ⟨bs, hmem⟩ := hmem
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
    obtain ⟨hbs_len, hmem⟩ := hmem
    refine reaches_pc_mono (SepWP.to_reaches_pc (memset_sepWP_le96 prog a hc s0 dst
      (s0.readReg64 .x1) n bs hpc hrun hx0 rfl hx2 hbs_len hn96) hmem) ?_
      (fun _ _ h => not_satisfies_false_sepConj h)
    rintro sf _ _ ⟨P_f, hmf, ⟨hx0_f, hsp_f, hcs_f⟩, hent⟩
    have hpost_mem : sf.mem ⊨ (dst ↦ₛ List.replicate n.toNat (c.setWidth 8)) ∗ R := by
      rw [← htrunc]
      exact Satisfies.mono (sepConj_mono_left hent) hmf
    have hpost : sf.mem ⊨ memsetSymSpec.post (dst, c, n) s0 sf ∗ R := by
      simp only [memsetSymSpec, CType.Bytes, CType.MutSlice8,
        sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨trivial, hx0_f⟩, hpost_mem⟩
    exact ⟨hpost, hsp_f, hcs_f⟩
  have hrw : s0.mem.RW dst n.toNat :=
    (IsBlock.memRegion dst n.toNat).rw hmem
  intro hL
  have hn_code : n.toNat + 4 * memsetWordsSym.length ≤ 2 ^ 64 :=
    memset_rw_len_add_code_le hL hc hrw hlen64
  have hn_le : n.toNat + 260 ≤ 2 ^ 64 := by simpa [memsetWordsSym] using hn_code
  refine memset_sym_large prog a hc s0 _ dst (s0.readReg64 .x1) n
    hpc hrun hx0 rfl hx2 hrw (by omega) hn_le ?_ hL
  intro sf _hpc_f _hrun_f hx0_f hcc hfc
  let bs := List.replicate n.toNat (c.setWidth 8)
  have hdst_bytes : sf.mem.readBytes dst bs.length = bs := by
    dsimp only [bs]
    rw [List.length_replicate, ← htrunc]
    exact memset_readBytes_of_prefixFilled hfc
  have hpost_mem : sf.mem ⊨ (dst ↦ₛ bs) ∗ R :=
    (IsBlock.memRegion dst n.toNat).update (IsBlock.pointsToBytes dst bs)
      (by simp only [bs, List.length_replicate]; omega) hmem hfc.1
      ⟨by simp only [bs, List.length_replicate]; omega, hdst_bytes⟩
  have hpost : sf.mem ⊨ memsetSymSpec.post (dst, c, n) s0 sf ∗ R := by
    simp only [memsetSymSpec, CType.Bytes, CType.MutSlice8,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨trivial, hx0_f⟩, hpost_mem⟩
  exact ⟨hpost, hcc.1⟩

end VerifiedLibraries.Musl
