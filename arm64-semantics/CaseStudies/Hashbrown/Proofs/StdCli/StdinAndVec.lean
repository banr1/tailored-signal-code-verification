/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.StdCli.StdinInit
public meta import ProofLib.LiteralFetchLint
import ProofLib.BV

/-!
# Placement-Generic `RawVecInner` and `small_probe_read`

Total-correctness contracts and `SepWP` call wrappers for `HbByteVec`,
`RawVecInner::{finish_grow, do_reserve_and_handle}`, and `default_read_to_end::small_probe_read`
over `HbCliLayout`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs.StdCli

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CaseStudies.Hashbrown

local macro "iAdrp " rd:term:arg pc:term:arg t:term:arg : term =>
  `(Instr.adr true $rd (adrpOff $pc $t))
local macro "iAddLo12 " rd:term:arg rn:term:arg t:term:arg : term =>
  `(Instr.addSubImm .W64 .ADD $rd $rn (($t).truncate 12) false)
local macro "iBl " pc:term:arg t:term:arg : term => `(Instr.bl ($t - $pc))
local macro "iB " pc:term:arg t:term:arg : term => `(Instr.b ($t - $pc))
local macro "unpack_hb_stdin_code " chunks:ident h:term : tactic => `(tactic| (
  have _hc := chunksToStepFacts $h
  simp only [$chunks:ident, chunksStepFacts, chunkStepAcc, fetchAtAcc,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at _hc
  (repeat obtain ⟨_, _hc⟩ := _hc); try clear _hc))
local macro "norm_jmp" : tactic =>
  `(tactic| conv in State.setPC _ _ => arg 2; rw [bv64_add_sub_cancel])
local macro "unpack_cells " k:num : tactic => `(tactic| (
  conv => arg 4; (try simp only [Nat.reduceMul])
  cells_unfold
  conv => arg 4; (try simp only [sepExists_sepConj_left, sepExists_sepConj_right])
  iterate $k (apply SepWP.exists_left; intro _)))
local macro "repack_cells" : tactic => `(tactic| (
  try simp only [Nat.reduceMul]; cells_unfold
  try simp only [BitVec.ofNat_eq_ofNat, sepExists_sepConj_left, sepExists_sepConj_right]; sep_entail))
local macro "unpack_cs " h:ident : tactic =>
  `(tactic| obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := $h)
local macro "close_cs" : tactic =>
  `(tactic| simp [CalleeSavedPreserved.iff_regs, Reg.fp, wp_norm, arm64_norm, *])
local macro "wp_a" : term => `(by simp [wp_norm, arm64_norm, bv_lin_norm, *] <;> try bv_lin)

/-! ## Byte `Vec<u8>` (`HbByteVec`) and `RawVecInner` -/

/-- Heap cost owned by `HbByteVecBuf` (`0` when `cap = 0`, `mallocngBlockCost cap` otherwise). -/
def hbByteVecCost (cap : Nat) : Nat :=
  if cap = 0 then 0 else mallocngBlockCost cap

/-- Heap block count owned by `HbByteVecBuf` (`0` when `cap = 0`, `1` when `0 < cap`). -/
def hbByteVecBlocks (cap : Nat) : Nat :=
  if cap = 0 then 0 else 1

/-- Backing buffer ownership for a Rust `Vec<u8>` with capacity `cap`, pointer `ptr`, and
    initialized prefix `bs`. -/
def HbByteVecBuf {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (cap : Nat) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0 then
    ⌜bs = [] ∧ ptr ≠ 0#64⌝
  else
    ⌜ptr ≠ 0#64 ∧ 16 ∣ ptr.toNat ∧ ptr.toNat + cap < 2 ^ 64 ∧ bs.length ≤ cap⌝ ∗
    M.Block γ ptr cap ∗
    (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length)

/-- Full Rust `Vec<u8>` header + backing buffer at `vecPtr`
    (`[vecPtr] = cap`, `[vecPtr + 0x08] = ptr`, `[vecPtr + 0x10] = bs.length`). -/
def HbByteVec {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    (vecPtr : BitVec 64) (cap : Nat) (ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (vecPtr ↦₆₄ BitVec.ofNat 64 cap) ∗
  ((vecPtr + 0x08#64) ↦₆₄ ptr) ∗
  ((vecPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
  HbByteVecBuf M γ cap ptr bs

theorem HbByteVecBuf_len_le {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    {M : MallocngCoreIface P addrs lim} {γ : GhostName}
    {cap : Nat} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : Memory} {R : SepProp}
    (hm : m ⊨ HbByteVecBuf M γ cap ptr bs ∗ R) :
    bs.length ≤ cap := by
  rcases Nat.eq_zero_or_pos cap with rfl | hpos
  · simp only [HbByteVecBuf, ↓reduceIte, satisfies_pure_sepConj] at hm
    rw [hm.1.1]; exact Nat.zero_le _
  · have hne : cap ≠ 0 := by omega
    simp only [HbByteVecBuf, hne, ↓reduceIte, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.2.2.2

private theorem realloc_slice_repack (ret : BitVec 64) (bs tailBs : List (BitVec 8))
    {oldCap newCap : Nat} (htail : tailBs.length = oldCap - bs.length)
    (hbs : bs.length ≤ oldCap) (hle : oldCap ≤ newCap) (hnew : newCap ≤ 2 ^ 64) :
    (ret ↦ₛ (bs ++ tailBs).take newCap) ∗
      memRegion (ret + BitVec.ofNat 64 ((bs ++ tailBs).take newCap).length)
        (newCap - ((bs ++ tailBs).take newCap).length) ⊢
    (ret ↦ₛ bs) ∗ memRegion (ret + BitVec.ofNat 64 bs.length) (newCap - bs.length) := by
  have htot : (bs ++ tailBs).length = oldCap := by rw [List.length_append, htail]; omega
  have htake : (bs ++ tailBs).take newCap = bs ++ tailBs :=
    List.take_of_length_le (by rw [htot]; exact hle)
  rw [htake, htot, pointsToBytes_append, sepConj_assoc]
  refine sepConj_mono (Entails.refl _) ?_
  have haddr : ret + BitVec.ofNat 64 oldCap =
      (ret + BitVec.ofNat 64 bs.length) + BitVec.ofNat 64 tailBs.length := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [htail]; omega
  have hsub : newCap - oldCap = (newCap - bs.length) - tailBs.length := by rw [htail]; omega
  rw [haddr, hsub]
  exact pointsToBytes_memRegion_entails _ tailBs (newCap - bs.length) (by rw [htail]; omega) (by omega)

/-- Total-correctness contract for `RawVecInner::finish_grow` (`C.rawVecFinishGrowAddr`). -/
def hbRawVecFinishGrowSpec {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : HbMallocngIface P addrs lim) (γ : GhostName) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × Nat × BitVec 64 ×
      List (BitVec 8) × Nat × Nat × Nat × BitVec 32) where
  pre := fun (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lc, blk, e0) s0 =>
    ⌜s0.readReg64 .x0 = outPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 oldCap ∧
      s0.readReg64 .x2 = oldPtr ∧
      s0.readReg64 .x3 = BitVec.ofNat 64 newCap ∧
      s0.readReg64 .x4 = 1#64 ∧
      s0.readReg64 .x5 = 1#64 ∧
      0 < newCap ∧ newCap < 2 ^ 63 ∧ oldCap ≤ newCap ∧
      hbByteVecBlocks oldCap ≤ blk ∧
      newCap ≤ lim.maxReq ∧
      lc + mallocngBlockCost newCap ≤ lim.maxPeakCost ∧
      blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
    ((outPtr ↦₆₄ v0) ∗
      ((outPtr + 0x08#64) ↦₆₄ v1) ∗
      ((outPtr + 0x10#64) ↦₆₄ v2) ∗
      HbByteVecBuf M.toMallocngCoreIface γ oldCap oldPtr bs ∗
      M.Heap γ lc blk s0 ∗
      (muslErrnoAddr s0 ↦₃₂ e0) ∗
      stackAt s0.sp (48 + MallocngStackBytes))
  post := fun (outPtr, _, _, _, oldCap, _, bs, newCap, lc, blk, _) s0 sf =>
    let lc' := lc - hbByteVecCost oldCap + mallocngBlockCost newCap
    let blk' := blk - hbByteVecBlocks oldCap + 1
    ∃∗ newPtr : BitVec 64, ∃∗ e1 : BitVec 32,
      ⌜MallocngStatePreserved s0 sf⌝ ∗
      (outPtr ↦₆₄ 0#64) ∗
      ((outPtr + 0x08#64) ↦₆₄ newPtr) ∗
      ((outPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 newCap) ∗
      HbByteVecBuf M.toMallocngCoreIface γ newCap newPtr bs ∗
      M.Heap γ lc' blk' sf ∗
      (muslErrnoAddr sf ↦₃₂ e1) ∗
      stackAt s0.sp (48 + MallocngStackBytes)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

@[simp, wp_norm, arm64_norm]
private theorem umulh_one_left (y : BitVec 64) :
    (((1#64).zeroExtend 128 * y.zeroExtend 128) >>> 64).truncate 64 = 0#64 := by
  rw [show (1#64).zeroExtend 128 = 1#128 from rfl, BitVec.one_mul]; bv_bits

@[simp, wp_norm, arm64_norm]
private theorem umulh_one_left' (y : BitVec 64) :
    ((1#128 * y.zeroExtend 128) >>> 64).truncate 64 = 0#64 := by
  rw [BitVec.one_mul]; bv_bits

@[simp, wp_norm, arm64_norm]
private theorem bv64_one_mul (y : BitVec 64) : 1#64 * y = y := BitVec.one_mul y

private theorem hrepack_rdl (m : Memory) (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (R : SepProp)
    (hm : m ⊨ (((sp - 56#64) ↦₆₄ w0) ∗ ((sp - 64#64) ↦₆₄ w1) ∗
      ((sp - 72#64) ↦₆₄ w2) ∗ ((sp - 80#64) ↦₆₄ w3) ∗
      ((sp - 88#64) ↦₆₄ w4) ∗ ((sp - 96#64) ↦₆₄ w5) ∗
      ((sp - 104#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗
      stackAt (sp - 112#64) (MallocngStackBytes - 64)) ∗ R) :
    m ⊨ stackAt (sp - 48#64) MallocngStackBytes ∗ R := by
  rw [show sp - 112#64 = sp - 48#64 - BitVec.ofNat 64 (8 * 8) from by bv_lin] at hm
  have hm1 : m ⊨ stackAt (sp - 48#64) ((MallocngStackBytes - 64) + 8 * 8) ∗ R := by
    rw [stackAt_split_cells (sp - 48#64) (MallocngStackBytes - 64) 8 (by decide)]
    repack_cells
  rwa [show (MallocngStackBytes - 64) + 8 * 8 = MallocngStackBytes from by decide] at hm1

set_option maxHeartbeats 400000 in
theorem hbRawVecFinishGrow_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbStdinAndVecCode P C)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.rawVecFinishGrowAddr (hbRawVecFinishGrowSpec M γ) := by
  apply subroutine_ok_of_sepWP_frozen
  rintro ⟨outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lc, blk, e0⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [hbRawVecFinishGrowSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnew_pos, hnew_lt, hold_le, hblk_ge,
    hreq_lim, hlc_lim, hblk_lim⟩, hm⟩
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5] at hx0 hx1 hx2 hx3 hx4 hx5
  have hnew_ne : newCap ≠ 0 := by omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnew_bv_nz : BitVec.ofNat 64 newCap ≠ 0#64 := by
    intro h; have := congrArg BitVec.toNat h
    rw [hnew_toNat] at this; exact hnew_ne this
  have hnew_ult1 : (BitVec.ofNat 64 newCap).ult 1#64 = false := by
    rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_toNat_lt, hnew_toNat]
    have : (1#64).toNat = 1 := rfl
    omega
  have hnew_hi : BitVec.ult 0x7fffffffffffffff#64 (BitVec.ofNat 64 newCap) = false := by
    rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_toNat_lt, hnew_toNat]
    have : (0x7fffffffffffffff#64).toNat = 2 ^ 63 - 1 := by decide
    omega
  refine ⟨_, hm, ?_⟩
  rw [show 48 + MallocngStackBytes = MallocngStackBytes + 8 * 6 from by omega,
      stackAt_split_cells s0.sp MallocngStackBytes 6 (by decide)]
  unpack_cells 6
  conv => arg 4; rw [show s0.sp - BitVec.ofNat 64 (8 * 6) = s0.sp - 48#64 from rfl]
  rcases Nat.eq_zero_or_pos oldCap with rfl | hold_pos
  ·
    conv => arg 4; simp only [HbByteVecBuf, ↓reduceIte, sepConj_assoc, sepConj_pull_pure]
    apply SepWP.pure_elim; rintro ⟨hbs, _⟩
    subst hbs
    refine SepWP.seq_nonVm (mid := C.mallocng.mallocAddr) hext hsvc ?_
    have hc_nv1 := hc.withSvc nonVmSvc
    unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
    wp_steps; norm_jmp; wp_steps; wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps; norm_jmp
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm1
    refine call_malloc M.toMallocngCoreIface γ hvm1 (req := newCap)
      (sp_call := s0.sp - 48#64) (ret_pc := C.rawVecFinishGrowAddr + 0x78#64)
      (by omega) hlc_lim hblk_lim (F := ?_) (by sep_frame)
      (fun s1 e1 hpc1 hrun1 hsp1 hcs1 hmsp1 hnz1 hal16_1 hnw1 => ?_)
      (hsp_align := by
        simp only [State.spAligned, wp_norm, arm64_norm]
        simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 48#64 hsp_align)
      (hreq_reg := by simp [wp_norm, arm64_norm, hnew_toNat])
    have hx19_1 : s1.readReg64 (.gpr 19#5) = outPtr := by
      rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap := by
      rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
    replace hsp1 : s1.sp = s0.sp - 48#64 := by rw [hsp1]; exact wp_a
    have hsp1_al : s1.spAligned = true := by
      simp only [State.spAligned, hsp1]; exact s0.spAligned_sub 48#64 hsp_align
    have hnz1' : s1.readReg64 (.gpr 0#5) ≠ 0#64 := hnz1
    apply SepWP.of_nonVm hext hsvc
    wp_steps
    (try simp only [bne_iff_ne, ne_eq, hnz1', not_false_eq_true, ↓reduceIte])
    wp_steps
    wp_steps
    apply SepWP.done
      (by unpack_cs hcs1; simp [wp_norm, arm64_norm, *] <;> try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun1])
    intro hvm2
    refine ⟨fun hkf hm_end => ?_, by simp [wp_norm, arm64_norm, *] <;> bv_lin,
      by unpack_cs hcs1; close_cs⟩
    dsimp only [hbRawVecFinishGrowSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨s1.readReg64 .x0, e1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm]; rw [hmsp1.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.2.1]; simp [wp_norm, arm64_norm],
             hkf⟩, ?_⟩
    replace hm_end := mono_head_sat (vmHeapTransport M.toMallocngCoreIface hvm2) hm_end
    simp only [HbByteVecBuf, hbByteVecCost, hbByteVecBlocks, ↓reduceIte, hnew_ne,
      Nat.sub_zero, List.length_nil, BitVec.add_zero, pointsToBytes_nil,
      emp_sepConj, muslErrnoAddr, wp_norm, arm64_norm] at hm_end ⊢
    refine ⟨⟨hnz1, hal16_1, hnw1, Nat.zero_le _⟩, ?_⟩
    rw [show 48 + MallocngStackBytes = MallocngStackBytes + 8 * 6 from by omega,
        stackAt_split_cells s0.sp MallocngStackBytes 6 (by decide)]
    repack_cells
  ·
    have hold_ne : oldCap ≠ 0 := by omega
    have hold_bv_nz : BitVec.ofNat 64 oldCap ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h
      simp [Nat.mod_eq_of_lt (by omega : oldCap < 2 ^ 64)] at this; omega
    conv => arg 4; simp only [HbByteVecBuf, hold_ne, ↓reduceIte, sepConj_assoc, sepConj_pull_pure]
    apply SepWP.pure_elim; rintro ⟨hp_nz, _, _, hbs_le⟩
    conv =>
      arg 4
      rw [memRegion_eq_exists_bytes (oldPtr + BitVec.ofNat 64 bs.length) (oldCap - bs.length) (by omega)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro tailBs
    conv => arg 4; simp only [sepConj_assoc, sepConj_pull_pure]
    apply SepWP.pure_elim; intro htail_len
    refine SepWP.weaken_pre (P' := (oldPtr ↦ₛ (bs ++ tailBs)) ∗ ?_)
      (by rw [pointsToBytes_append]; sep_frame) ?_
    rw [show MallocngStackBytes = (MallocngStackBytes - 64) + 8 * 8 from by decide,
        stackAt_split_cells (s0.sp - 48#64) (MallocngStackBytes - 64) 8 (by decide)]
    unpack_cells 8
    conv => arg 4; rw [show s0.sp - 48#64 - BitVec.ofNat 64 (8 * 8) = s0.sp - 112#64 from by bv_lin]
    refine SepWP.seq_nonVm (mid := C.mallocng.reallocAddr) hext hsvc ?_
    have hc_nv1 := hc.withSvc nonVmSvc
    unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
    wp_steps; norm_jmp; wp_steps; norm_jmp; wp_steps; norm_jmp
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
    intro hvm1
    refine SepWP.weaken_pre_frame (P' := stackAt (s0.sp - 48#64) MallocngStackBytes ∗ ?_)
      (fun R hm' => by
        simpa only [sepConj_assoc] using
          hrepack_rdl _ s0.sp _ _ _ _ _ _ _ _ _ (Satisfies.mono (by sep_frame) hm')) ?_
    refine call_realloc M γ hvm1 hp_nz (oldReq := oldCap) (newReq := newCap) (bs := bs ++ tailBs)
      (sp_call := s0.sp - 48#64) (ret_pc := C.rawVecFinishGrowAddr + 0x5c#64)
      (by rw [List.length_append, htail_len]; omega) hreq_lim hlc_lim hblk_lim (F := ?_) (by sep_frame)
      (fun s1 e1 hpc1 hrun1 hsp1 hcs1 hmsp1 hnz1 hal16_1 hnw1 => ?_)
      (hsp_align := by
        simp only [State.spAligned, wp_norm, arm64_norm]
        simpa [BitVec.sub_eq_add_neg] using s0.spAligned_sub 48#64 hsp_align)
      (hx0 := by simp [wp_norm, arm64_norm])
      (hreq_reg := by simp [wp_norm, arm64_norm, hnew_toNat])
    refine SepWP.weaken_pre
      (P' := ((s1.readReg64 .x0 ↦ₛ (bs ++ tailBs).take newCap) ∗
        memRegion (s1.readReg64 .x0 + BitVec.ofNat 64 ((bs ++ tailBs).take newCap).length)
          (newCap - ((bs ++ tailBs).take newCap).length)) ∗ ?_) (by sep_frame) ?_
    refine SepWP.weaken_pre
      (sepConj_mono (realloc_slice_repack (s1.readReg64 .x0) bs tailBs htail_len hbs_le hold_le (by omega))
        (Entails.refl _)) ?_
    have hx19_1 : s1.readReg64 (.gpr 19#5) = outPtr := by
      rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
    have hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 newCap := by
      rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
    replace hsp1 : s1.sp = s0.sp - 48#64 := by rw [hsp1]; exact wp_a
    have hsp1_al : s1.spAligned = true := by
      simp only [State.spAligned, hsp1]; exact s0.spAligned_sub 48#64 hsp_align
    have hnz1' : s1.readReg64 (.gpr 0#5) ≠ 0#64 := hnz1
    apply SepWP.of_nonVm hext hsvc
    wp_steps
    (try simp only [bne_iff_ne, ne_eq, hnz1', not_false_eq_true, ↓reduceIte])
    wp_steps
    wp_steps
    apply SepWP.done
      (by unpack_cs hcs1; simp [wp_norm, arm64_norm, *] <;> try bv_lin)
      (by simp [wp_norm, arm64_norm, hrun1])
    intro hvm2
    refine ⟨fun hkf hm_end => ?_, by simp [wp_norm, arm64_norm, *] <;> bv_lin,
      by unpack_cs hcs1; close_cs⟩
    dsimp only [hbRawVecFinishGrowSpec]
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨s1.readReg64 .x0, e1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm]; rw [hmsp1.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.1]; simp [wp_norm, arm64_norm],
             by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.2.1]; simp [wp_norm, arm64_norm],
             hkf⟩, ?_⟩
    replace hm_end := mono_head_sat (vmHeapTransport M.toMallocngCoreIface hvm2) hm_end
    have hblk_eq : blk - hbByteVecBlocks oldCap + 1 = blk := by
      simp only [hbByteVecBlocks, hold_ne, ↓reduceIte] at hblk_ge ⊢; omega
    simp only [HbByteVecBuf, hbByteVecCost, hold_ne, hnew_ne, ↓reduceIte, hblk_eq,
      muslErrnoAddr, wp_norm, arm64_norm] at hm_end ⊢
    refine ⟨⟨hnz1, hal16_1, hnw1, by omega⟩, ?_⟩
    rw [show 48 + MallocngStackBytes = MallocngStackBytes + 8 * 6 from by omega,
        stackAt_split_cells s0.sp MallocngStackBytes 6 (by decide)]
    repack_cells

theorem hbRawVecFinishGrow_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (hc : HbStdinAndVecCode P C)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {outPtr v0 v1 v2 oldPtr : BitVec 64} {oldCap newCap lc blk : Nat}
    {bs : List (BitVec 8)} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s := by exact ⟨rfl, rfl, rfl, fun _ => rfl⟩)
    (hnew_pos : 0 < newCap) (hnew_lt : newCap < 2 ^ 63) (hold_le : oldCap ≤ newCap)
    (hblk_ge : hbByteVecBlocks oldCap ≤ blk)
    (hreq_lim : newCap ≤ lim.maxReq)
    (hlc_lim : lc + mallocngBlockCost newCap ≤ lim.maxPeakCost)
    (hblk_lim : blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((outPtr ↦₆₄ v0) ∗
        ((outPtr + 0x08#64) ↦₆₄ v1) ∗
        ((outPtr + 0x10#64) ↦₆₄ v2) ∗
        HbByteVecBuf M.toMallocngCoreIface γ oldCap oldPtr bs ∗
        M.Heap γ lc blk s0 ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗
        stackAt sp_call (48 + MallocngStackBytes)) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (newPtr : BitVec 64) (e1 : BitVec 32),
      let lc' := lc - hbByteVecCost oldCap + mallocngBlockCost newCap
      let blk' := blk - hbByteVecBlocks oldCap + 1
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      SepWP P target_pc sf
        (((outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 0x08#64) ↦₆₄ newPtr) ∗
          ((outPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 newCap) ∗
          HbByteVecBuf M.toMallocngCoreIface γ newCap newPtr bs ∗
          M.Heap γ lc' blk' sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt sp_call (48 + MallocngStackBytes)) ∗ F) post oom)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hpc : s.pc = C.rawVecFinishGrowAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = outPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 oldCap := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = oldPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 newCap := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx4 : s.readReg64 .x4 = 1#64 := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx5 : s.readReg64 .x5 = 1#64 := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbRawVecFinishGrow_ok hc M γ hsvc hext)
    (x := (outPtr, v0, v1, v2, oldCap, oldPtr, bs, newCap, lc, blk, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only [hbRawVecFinishGrowSpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnew_pos, hnew_lt, hold_le, hblk_ge,
      hreq_lim, hlc_lim, hblk_lim⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (entails_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm)) hm'
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [hbRawVecFinishGrowSpec]
    conv => arg 4; rw [hsp_call]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun newPtr => SepWP.exists_elim fun e1 => ?_
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hmsp
    exact SepWP.weaken_pre (by sep_frame) (hnext sf newPtr e1 hpc_f hrun_f hsp_f hcs_f hmsp)

abbrev hbRawVecReserveStackBytes : Nat := 112 + MallocngStackBytes

private theorem csel_hi_max {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (if BitVec.ult (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true
     then BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (max a b) := by
  simp only [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  split <;> (congr 1; omega)

private theorem csel_hi_max8 {a : Nat} (ha : a < 2 ^ 64) :
    (if BitVec.ult 8#64 (BitVec.ofNat 64 a) = true
     then BitVec.ofNat 64 a else 8#64) = BitVec.ofNat 64 (max a 8) :=
  csel_hi_max ha (by decide)

/-- Total-correctness contract for `RawVecInner::do_reserve_and_handle` (`C.rawVecDoReserveAddr`). -/
def hbRawVecDoReserveSpec {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : HbMallocngIface P addrs lim) (γ : GhostName) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8) × Nat × Nat × Nat × BitVec 32) where
  pre := fun (vecPtr, oldCap, oldPtr, bs, additional, lc, blk, e0) s0 =>
    let newCap := max (max (bs.length + additional) (2 * oldCap)) 8
    ⌜s0.readReg64 .x0 = vecPtr ∧
      s0.readReg64 .x1 = BitVec.ofNat 64 bs.length ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 additional ∧
      s0.readReg64 .x3 = 1#64 ∧
      s0.readReg64 .x4 = 1#64 ∧
      1 ≤ additional ∧ bs.length + additional < 2 ^ 63 ∧ oldCap < 2 ^ 62 ∧
      hbByteVecBlocks oldCap ≤ blk ∧
      newCap ≤ lim.maxReq ∧
      lc + mallocngBlockCost newCap ≤ lim.maxPeakCost ∧
      blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
    ((vecPtr ↦₆₄ BitVec.ofNat 64 oldCap) ∗
      ((vecPtr + 0x08#64) ↦₆₄ oldPtr) ∗
      HbByteVecBuf M.toMallocngCoreIface γ oldCap oldPtr bs ∗
      M.Heap γ lc blk s0 ∗
      (muslErrnoAddr s0 ↦₃₂ e0) ∗
      stackAt s0.sp hbRawVecReserveStackBytes)
  post := fun (vecPtr, oldCap, _, bs, additional, lc, blk, _) s0 sf =>
    let newCap := max (max (bs.length + additional) (2 * oldCap)) 8
    let lc' := lc - hbByteVecCost oldCap + mallocngBlockCost newCap
    let blk' := blk - hbByteVecBlocks oldCap + 1
    ∃∗ newPtr : BitVec 64, ∃∗ e1 : BitVec 32,
      ⌜MallocngStatePreserved s0 sf⌝ ∗
      (vecPtr ↦₆₄ BitVec.ofNat 64 newCap) ∗
      ((vecPtr + 0x08#64) ↦₆₄ newPtr) ∗
      HbByteVecBuf M.toMallocngCoreIface γ newCap newPtr bs ∗
      M.Heap γ lc' blk' sf ∗
      (muslErrnoAddr sf ↦₃₂ e1) ∗
      stackAt s0.sp hbRawVecReserveStackBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem hbRawVecDoReserve_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbStdinAndVecCode P C)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.rawVecDoReserveAddr (hbRawVecDoReserveSpec M γ) := by
  refine subroutine_ok_of_sepWP_frozen
    fun ⟨vecPtr, oldCap, oldPtr, bs, additional, lc, blk, e0⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [hbRawVecDoReserveSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hadd_pos, hadd_lt, hcap_lt, hblk_ge,
    hreq_lim, hlc_lim, hblk_lim⟩, hm⟩
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4] at hx0 hx1 hx2 hx3 hx4
  have h_add_eq : BitVec.ofNat 64 additional + BitVec.ofNat 64 bs.length =
      BitVec.ofNat 64 (bs.length + additional) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have h_no_ovf : BitVec.ult (BitVec.ofNat 64 (bs.length + additional))
      (BitVec.ofNat 64 additional) = false := by
    rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_toNat_lt]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : bs.length + additional < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : additional < 2 ^ 64)]; omega
  have h_lsl_eq : (BitVec.ofNat 64 oldCap) <<< 1 = BitVec.ofNat 64 (2 * oldCap) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : oldCap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 2 * oldCap < 2 ^ 64)]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have h_csel_eq :
      (if BitVec.ult 8#64
            (if BitVec.ult (BitVec.ofNat 64 (2 * oldCap))
                  (BitVec.ofNat 64 (bs.length + additional)) = true
             then BitVec.ofNat 64 (bs.length + additional)
             else BitVec.ofNat 64 (2 * oldCap)) = true
       then if BitVec.ult (BitVec.ofNat 64 (2 * oldCap))
                 (BitVec.ofNat 64 (bs.length + additional)) = true
            then BitVec.ofNat 64 (bs.length + additional)
            else BitVec.ofNat 64 (2 * oldCap)
       else 8#64) =
      BitVec.ofNat 64 (max (max (bs.length + additional) (2 * oldCap)) 8) := by
    rw [csel_hi_max (by omega) (by omega), csel_hi_max8 (by omega)]
  refine ⟨_, hm, ?_⟩
  rw [show hbRawVecReserveStackBytes = (48 + MallocngStackBytes) + 8 * 8 from by
        unfold hbRawVecReserveStackBytes; omega,
      stackAt_split_cells s0.sp (48 + MallocngStackBytes) 8 (by decide)]
  unpack_cells 8
  conv => arg 4; rw [show s0.sp - BitVec.ofNat 64 (8 * 8) = s0.sp - 64#64 from rfl]
  refine SepWP.seq_nonVm (mid := C.rawVecFinishGrowAddr) hext hsvc ?_
  have hc_nv1 := hc.withSvc nonVmSvc
  unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
  wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine hbRawVecFinishGrow_wp hc M γ hvm1
    (outPtr := s0.sp - 56#64) (oldCap := oldCap) (oldPtr := oldPtr) (bs := bs)
    (newCap := max (max (bs.length + additional) (2 * oldCap)) 8)
    (sp_call := s0.sp - 64#64) (ret_pc := C.rawVecDoReserveAddr + 0x58#64)
    (by omega) (by omega) (by omega) hblk_ge hreq_lim hlc_lim hblk_lim
    (by simp only [show s0.sp - 56#64 + 0x08#64 = s0.sp - 48#64 from by bv_lin,
          show s0.sp - 56#64 + 0x10#64 = s0.sp - 40#64 from by bv_lin]; sep_frame)
    (fun s1 newPtr e1 hpc1 hrun1 hsp1 hcs1 hmsp1 => ?_) hsvc hext
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (hx0 := by simp [wp_norm, arm64_norm] <;> bv_lin)
    (hx1 := by simp [wp_norm, arm64_norm])
    (hx2 := by simp [wp_norm, arm64_norm])
    (hx3 := by simp [wp_norm, arm64_norm])
    (hx4 := by simp [wp_norm, arm64_norm])
    (hx5 := by simp [wp_norm, arm64_norm])
  conv =>
    arg 4
    simp only [show s0.sp - 56#64 + 0x08#64 = s0.sp - 48#64 from by bv_lin,
      show s0.sp - 56#64 + 0x10#64 = s0.sp - 40#64 from by bv_lin]
  have hx19_1 : s1.readReg64 (.gpr 19#5) = vecPtr := by
    rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hx20_1 : s1.readReg64 (.gpr 20#5) =
      BitVec.ofNat 64 (max (max (bs.length + additional) (2 * oldCap)) 8) := by
    rw [← Reg.x20, hcs1.readReg64_x20]; simp [wp_norm, arm64_norm]
  replace hsp1 : s1.sp = s0.sp - 64#64 := by rw [hsp1]; exact wp_a
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1]; exact s0.spAligned_sub 64#64 hsp_align
  refine SepWP.of_nonVm hext hsvc ?_
  wp_steps
  apply SepWP.done
    (by unpack_cs hcs1; simp [wp_norm, arm64_norm, *] <;> try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun1])
  intro hvm2
  refine ⟨fun hkf hm_end => ?_, by simp [wp_norm, arm64_norm, *] <;> bv_lin,
    by unpack_cs hcs1; close_cs⟩
  dsimp only [hbRawVecDoReserveSpec]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨newPtr, e1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by simp only [wp_norm, arm64_norm]; rw [hmsp1.1]; simp [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.1]; simp [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.1]; simp [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm]; rw [hmsp1.2.2.2.1]; simp [wp_norm, arm64_norm],
           hkf⟩, ?_⟩
  replace hm_end := mono_head_sat (vmHeapTransport M.toMallocngCoreIface hvm2) hm_end
  simp only [muslErrnoAddr, wp_norm, arm64_norm] at hm_end ⊢
  rw [show hbRawVecReserveStackBytes = (48 + MallocngStackBytes) + 8 * 8 from by
        unfold hbRawVecReserveStackBytes; omega,
      stackAt_split_cells s0.sp (48 + MallocngStackBytes) 8 (by decide)]
  repack_cells

theorem hbRawVecDoReserve_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (hc : HbStdinAndVecCode P C)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {vecPtr oldPtr : BitVec 64} {oldCap additional lc blk : Nat}
    {bs : List (BitVec 8)} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s := by exact ⟨rfl, rfl, rfl, fun _ => rfl⟩)
    (hadd_pos : 1 ≤ additional) (hadd_lt : bs.length + additional < 2 ^ 63) (hcap_lt : oldCap < 2 ^ 62)
    (hblk_ge : hbByteVecBlocks oldCap ≤ blk)
    (hreq_lim : max (max (bs.length + additional) (2 * oldCap)) 8 ≤ lim.maxReq)
    (hlc_lim : lc + mallocngBlockCost (max (max (bs.length + additional) (2 * oldCap)) 8) ≤ lim.maxPeakCost)
    (hblk_lim : blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ ((vecPtr ↦₆₄ BitVec.ofNat 64 oldCap) ∗
        ((vecPtr + 0x08#64) ↦₆₄ oldPtr) ∗
        HbByteVecBuf M.toMallocngCoreIface γ oldCap oldPtr bs ∗
        M.Heap γ lc blk s0 ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗
        stackAt sp_call hbRawVecReserveStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (newPtr : BitVec 64) (e1 : BitVec 32),
      let newCap := max (max (bs.length + additional) (2 * oldCap)) 8
      let lc' := lc - hbByteVecCost oldCap + mallocngBlockCost newCap
      let blk' := blk - hbByteVecBlocks oldCap + 1
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      SepWP P target_pc sf
        (((vecPtr ↦₆₄ BitVec.ofNat 64 newCap) ∗
          ((vecPtr + 0x08#64) ↦₆₄ newPtr) ∗
          HbByteVecBuf M.toMallocngCoreIface γ newCap newPtr bs ∗
          M.Heap γ lc' blk' sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt sp_call hbRawVecReserveStackBytes) ∗ F) post oom)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hpc : s.pc = C.rawVecDoReserveAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = vecPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs.length := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 additional := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx3 : s.readReg64 .x3 = 1#64 := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx4 : s.readReg64 .x4 = 1#64 := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbRawVecDoReserve_ok hc M γ hsvc hext)
    (x := (vecPtr, oldCap, oldPtr, bs, additional, lc, blk, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only [hbRawVecDoReserveSpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hadd_pos, hadd_lt, hcap_lt, hblk_ge,
      hreq_lim, hlc_lim, hblk_lim⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (entails_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm)) hm'
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [hbRawVecDoReserveSpec]
    conv => arg 4; rw [hsp_call]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun newPtr => SepWP.exists_elim fun e1 => ?_
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWP.pure_elim; intro hmsp
    exact SepWP.weaken_pre (by sep_frame) (hnext sf newPtr e1 hpc_f hrun_f hsp_f hcs_f hmsp)

/-! ## `default_read_to_end::small_probe_read` -/

abbrev hbSmallProbeStackBytes : Nat := 144 + hbRawVecReserveStackBytes

private theorem four_cells_to_memRegion32 (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
      ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) ⊢
    memRegion (sp - 144#64) 32 := by
  rw [memRegion_split' (b := sp - 144#64) (b' := sp - 136#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp - 136#64) (b' := sp - 128#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp - 128#64) (b' := sp - 120#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))

private theorem vec_append_repack {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) (γ : GhostName)
    {cap' : Nat} {ptr' : BitVec 64} {bs chunk : List (BitVec 8)}
    (hpos : 0 < chunk.length) (hfit : bs.length + chunk.length ≤ cap')
    (hnz : ptr' ≠ 0#64) (hal : 16 ∣ ptr'.toNat) (hnw : ptr'.toNat + cap' < 2 ^ 64) :
    M.Block γ ptr' cap' ∗ (ptr' ↦ₛ bs) ∗ ((ptr' + BitVec.ofNat 64 bs.length) ↦ₛ chunk) ∗
      memRegion ((ptr' + BitVec.ofNat 64 bs.length) + BitVec.ofNat 64 chunk.length)
        (cap' - bs.length - chunk.length) ⊢
    HbByteVecBuf M γ cap' ptr' (bs ++ chunk) := by
  have hne : cap' ≠ 0 := by omega
  simp only [HbByteVecBuf, hne, ↓reduceIte]
  have haddr : (ptr' + BitVec.ofNat 64 bs.length) + BitVec.ofNat 64 chunk.length =
      ptr' + BitVec.ofNat 64 (bs ++ chunk).length := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, List.length_append]
  have hsub : cap' - bs.length - chunk.length = cap' - (bs ++ chunk).length := by
    rw [List.length_append]; omega
  rw [haddr, hsub, ← sepConj_assoc (ptr' ↦ₛ bs), ← pointsToBytes_append]
  exact Entails.pure_right ⟨hnz, hal, hnw, by rw [List.length_append]; omega⟩ (by sep_entail)

/-- Total-correctness contract for `std::io::default_read_to_end::small_probe_read`
    (`C.smallProbeReadAddr`): reads up to `32` bytes from open `stdin` (`fd = 0`) and appends
    them to the Rust `Vec<u8>` at `vecPtr`, growing via `RawVecInner::do_reserve_and_handle`
    when `cap - bs.length < chunk.length`. -/
def hbSmallProbeReadSpec {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : HbMallocngIface P addrs lim) (γ : GhostName) :
    Spec (BitVec 64 × Nat × BitVec 64 × List (BitVec 8) × List (BitVec 8) ×
      Nat × Nat × BitVec 32) where
  pre := fun (vecPtr, cap, ptr, bs, rem, lc, blk, e0) s0 =>
    let chunk := rem.take 32
    let growCap := max (max (bs.length + chunk.length) (2 * cap)) 8
    ⌜s0.readReg64 .x0 = vecPtr ∧
      HbStdinOpen rem s0.fs ∧
      144 ≤ s0.sp.toNat ∧ s0.sp.toNat ≤ Arm64.USER_VA_LIMIT ∧
      bs.length + 32 < 2 ^ 63 ∧
      cap < 2 ^ 62 ∧
      (cap - bs.length < chunk.length →
        hbByteVecBlocks cap ≤ blk ∧
        growCap ≤ lim.maxReq ∧
        lc + mallocngBlockCost growCap ≤ lim.maxPeakCost ∧
        blk + 1 ≤ lim.maxPeakBlocks)⌝ ∗
    (HbByteVec M.toMallocngCoreIface γ vecPtr cap ptr bs ∗
      M.Heap γ lc blk s0 ∗
      (muslErrnoAddr s0 ↦₃₂ e0) ∗
      stackAt s0.sp hbSmallProbeStackBytes)
  post := fun (vecPtr, cap, _, bs, rem, lc, blk, _) s0 sf =>
    let chunk := rem.take 32
    let growCap := max (max (bs.length + chunk.length) (2 * cap)) 8
    let cap' := if cap - bs.length < chunk.length then growCap else cap
    let lc' := if cap - bs.length < chunk.length
      then lc - hbByteVecCost cap + mallocngBlockCost growCap else lc
    let blk' := if cap - bs.length < chunk.length then blk - hbByteVecBlocks cap + 1 else blk
    ∃∗ ptr' : BitVec 64, ∃∗ e1 : BitVec 32,
      ⌜sf.readReg64 .x0 = 0#64 ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length ∧
        HbStdinOpen (rem.drop chunk.length) sf.fs ∧
        sf.trace = s0.trace ∧
        sf.tpidrEl0 = s0.tpidrEl0 ∧
        sf.sigActions = s0.sigActions ∧
        s0.mem.KeepsFrozen sf.mem⌝ ∗
      HbByteVec M.toMallocngCoreIface γ vecPtr cap' ptr' (bs ++ chunk) ∗
      M.Heap γ lc' blk' sf ∗
      (muslErrnoAddr sf ↦₃₂ e1) ∗
      stackAt s0.sp hbSmallProbeStackBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private def hbUpperCS (s0 s : State) : Prop :=
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem hbUpperCS_step {s0 s1 s2 : State}
    (h01 : hbUpperCS s0 s1) (hcs : CalleeSavedPreserved s1 s2) :
    hbUpperCS s0 s2 := by
  obtain ⟨_, _⟩ := h01; unpack_cs hcs
  simp [hbUpperCS, wp_norm, arm64_norm, *]

private theorem hbSmallProbeFinish_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbStdinAndVecCode P C)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    {vecPtr ptr0 ptr' u0 u1 u2 : BitVec 64} {cap cap' lc blk lc' blk' : Nat}
    {bs rem : List (BitVec 8)} {e0 e1 : BitVec 32} {Pre R : SepProp} {s0 s : State}
    (hcap' : cap' = if cap - bs.length < (rem.take 32).length
      then max (max (bs.length + (rem.take 32).length) (2 * cap)) 8 else cap)
    (hlc' : lc' = if cap - bs.length < (rem.take 32).length
      then lc - hbByteVecCost cap +
        mallocngBlockCost (max (max (bs.length + (rem.take 32).length) (2 * cap)) 8) else lc)
    (hblk' : blk' = if cap - bs.length < (rem.take 32).length
      then blk - hbByteVecBlocks cap + 1 else blk)
    (hpc : s.pc = C.smallProbeReadAddr + 0x7c#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = vecPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (rem.take 32).length)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 bs.length)
    (hup : hbUpperCS s0 s)
    (hopen : HbStdinOpen (rem.drop (rem.take 32).length) s.fs)
    (htr : s.trace = s0.trace) (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hsig : s.sigActions = s0.sigActions)
    (hpre : Pre ⊢
      ((vecPtr ↦₆₄ BitVec.ofNat 64 cap') ∗
        ((vecPtr + 0x08#64) ↦₆₄ ptr') ∗
        ((vecPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        HbByteVecBuf M.toMallocngCoreIface γ cap' ptr' (bs ++ rem.take 32) ∗
        M.Heap γ lc' blk' s ∗
        (muslErrnoAddr s0 ↦₃₂ e1) ∗
        stackAt (s0.sp - 144#64) hbRawVecReserveStackBytes ∗
        ((s0.sp - 144#64) ↦ₛ rem.take 32) ∗
        memRegion (s0.sp - 144#64 + BitVec.ofNat 64 (rem.take 32).length)
          (32 - (rem.take 32).length) ∗
        ((s0.sp - 112#64) ↦₆₄ u0) ∗
        ((s0.sp - 104#64) ↦₆₄ u1) ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ u2) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) :
    SepWP P (s0.readReg64 Reg.lr) s Pre
      (fun sf P_f =>
        (s0.mem.KeepsFrozen sf.mem → sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (hbSmallProbeReadSpec M γ).post
            (vecPtr, cap, ptr0, bs, rem, lc, blk, e0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.weaken_pre hpre ?_
  have hchunk_le : (rem.take 32).length ≤ 32 := List.length_take_le 32 rem
  have hsp_r : s.readReg64 Reg.sp = s0.sp - 144#64 := hsp
  have h_len_add : BitVec.ofNat 64 bs.length + BitVec.ofNat 64 (rem.take 32).length =
      BitVec.ofNat 64 (bs ++ rem.take 32).length := by
    rw [← BitVec.ofNat_add, List.length_append]
  refine SepWP.of_nonVm hext hsvc ?_
  have hc_nv := hc.withSvc nonVmSvc
  unpack_hb_stdin_code hbStdinAndVecChunks hc_nv
  wp_steps
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
  intro hvm
  obtain ⟨_, _⟩ := hup
  refine ⟨fun hkf hm_end => ?_, by simp [wp_norm, arm64_norm] <;> bv_lin, by close_cs⟩
  dsimp only [hbSmallProbeReadSpec]
  rw [← hcap', ← hlc', ← hblk']
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ptr', e1, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by simp [wp_norm, arm64_norm],
           by simp [wp_norm, arm64_norm],
           by simpa [wp_norm, arm64_norm] using hopen,
           by simp [wp_norm, arm64_norm, htr],
           by simp [wp_norm, arm64_norm, htp],
           by simp [wp_norm, arm64_norm, hsig],
           hkf⟩, ?_⟩
  replace hm_end := mono_head_sat (vmHeapTransport M.toMallocngCoreIface hvm) hm_end
  have hm_chunk : ((s0.sp - 144#64) ↦ₛ rem.take 32) ∗
      memRegion (s0.sp - 144#64 + BitVec.ofNat 64 (rem.take 32).length) (32 - (rem.take 32).length) ⊢
      memRegion (s0.sp - 144#64) 32 :=
    pointsToBytes_memRegion_entails (s0.sp - 144#64) (rem.take 32) 32 hchunk_le (by decide)
  replace hm_end := Satisfies.mono (Entails.trans (by sep_frame)
    (Entails.trans (sepConj_mono hm_chunk (Entails.refl _)) (by sep_frame))) hm_end
  simp only [HbByteVec, muslErrnoAddr, htp, wp_norm, arm64_norm] at hm_end ⊢
  rw [show hbSmallProbeStackBytes = (hbRawVecReserveStackBytes + 32) + 8 * 14 from by
        unfold hbSmallProbeStackBytes hbRawVecReserveStackBytes; omega,
      stackAt_split_cells s0.sp (hbRawVecReserveStackBytes + 32) 14 (by decide),
      stackAt_region (s0.sp - BitVec.ofNat 64 (8 * 14)) hbRawVecReserveStackBytes 32 (by decide),
      show (s0.sp - BitVec.ofNat 64 (8 * 14)) - BitVec.ofNat 64 32 = s0.sp - 144#64 from by
        simp only [Nat.reduceMul]; bv_lin]
  repack_cells

private theorem hbSmallProbeCopyAndFinish_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbStdinAndVecCode P C)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard) (hext : ∀ pc, P.externAt? pc = none)
    {vecPtr ptr0 ptr' u0 u1 u2 : BitVec 64} {cap cap' lc blk lc' blk' : Nat}
    {bs rem : List (BitVec 8)} {e0 e1 : BitVec 32} {Pre R : SepProp} {s0 s : State}
    (hpos : 0 < (rem.take 32).length) (hfit : bs.length + (rem.take 32).length ≤ cap')
    (hcap' : cap' = if cap - bs.length < (rem.take 32).length
      then max (max (bs.length + (rem.take 32).length) (2 * cap)) 8 else cap)
    (hlc' : lc' = if cap - bs.length < (rem.take 32).length
      then lc - hbByteVecCost cap +
        mallocngBlockCost (max (max (bs.length + (rem.take 32).length) (2 * cap)) 8) else lc)
    (hblk' : blk' = if cap - bs.length < (rem.take 32).length
      then blk - hbByteVecBlocks cap + 1 else blk)
    (hpc : s.pc = C.smallProbeReadAddr + 0x68#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 144#64) (hsp_al : s.spAligned = true)
    (hx19 : s.readReg64 (.gpr 19#5) = vecPtr)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (rem.take 32).length)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.ofNat 64 bs.length)
    (hup : hbUpperCS s0 s)
    (hopen : HbStdinOpen (rem.drop (rem.take 32).length) s.fs)
    (htr : s.trace = s0.trace) (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hsig : s.sigActions = s0.sigActions)
    (hpre : Pre ⊢
      ((vecPtr ↦₆₄ BitVec.ofNat 64 cap') ∗
        ((vecPtr + 0x08#64) ↦₆₄ ptr') ∗
        ((vecPtr + 0x10#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        HbByteVecBuf M.toMallocngCoreIface γ cap' ptr' bs ∗
        M.Heap γ lc' blk' s ∗
        (muslErrnoAddr s0 ↦₃₂ e1) ∗
        stackAt (s0.sp - 144#64) hbRawVecReserveStackBytes ∗
        ((s0.sp - 144#64) ↦ₛ rem.take 32) ∗
        memRegion (s0.sp - 144#64 + BitVec.ofNat 64 (rem.take 32).length)
          (32 - (rem.take 32).length) ∗
        ((s0.sp - 112#64) ↦₆₄ u0) ∗
        ((s0.sp - 104#64) ↦₆₄ u1) ∗
        ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ u2) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (.gpr 19#5)))) :
    SepWP P (s0.readReg64 Reg.lr) s Pre
      (fun sf P_f =>
        (s0.mem.KeepsFrozen sf.mem → sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (hbSmallProbeReadSpec M γ).post
            (vecPtr, cap, ptr0, bs, rem, lc, blk, e0) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  refine SepWP.weaken_pre hpre ?_
  have hchunk_le : (rem.take 32).length ≤ 32 := List.length_take_le 32 rem
  have hne_cap : cap' ≠ 0 := by omega
  have hsp_r : s.readReg64 Reg.sp = s0.sp - 144#64 := hsp
  conv =>
    arg 4
    simp only [HbByteVecBuf, hne_cap, ↓reduceIte, sepConj_assoc]
    rw [sepConj_pull_pure, sepConj_pull_pure, sepConj_pull_pure]
  apply SepWP.pure_elim; rintro ⟨hnz_p, hal_p, hnw_p, hbs_le⟩
  conv =>
    arg 4
    rw [memRegion_split_le (ptr' + BitVec.ofNat 64 bs.length) (rem.take 32).length
          (cap' - bs.length) (by omega) (by omega)]
  refine SepWP.seq_nonVm (mid := C.std.memcpyAddr) hext hsvc ?_
  have hc_nv1 := hc.withSvc nonVmSvc
  unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
  wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm1
  refine hMem.call_memcpy
    (dst := ptr' + BitVec.ofNat 64 bs.length) (src := s0.sp - 144#64) (bs := rem.take 32)
    (ret_pc := C.smallProbeReadAddr + 0x7c#64)
    (by sep_frame)
    (fun s2 hpc2 hrun2 hsp2 hcs2 _ hstd2 => ?_)
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_al)
    (hx0 := by simp [wp_norm, arm64_norm])
    (hx1 := by simp [wp_norm, arm64_norm])
    (hx2 := by simp [wp_norm, arm64_norm])
    (hlen := by omega)
  have hvm12 : VmFieldsPreserved s s2 := hvm1.trans (vmOfStdState hstd2)
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm12)
  have hrepack := vec_append_repack M.toMallocngCoreIface γ (bs := bs) (chunk := rem.take 32)
    hpos hfit hnz_p hal_p hnw_p
  refine SepWP.weaken_pre (Entails.trans (by sep_frame)
    (Entails.trans (sepConj_mono hrepack (Entails.refl _)) (by sep_frame))) ?_
  have hx19_2 : s2.readReg64 (.gpr 19#5) = vecPtr := by
    rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19]
  have hx20_2 : s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (rem.take 32).length := by
    rw [← Reg.x20, hcs2.readReg64_x20]; simp [wp_norm, arm64_norm, hx20]
  have hx22_2 : s2.readReg64 (.gpr 22#5) = BitVec.ofNat 64 bs.length := by
    rw [← Reg.x22, hcs2.readReg64_x22]; simp [wp_norm, arm64_norm, hx22]
  have hsp2_eq : s2.sp = s0.sp - 144#64 := by rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp
  have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2_eq, hsp] using hsp_al
  refine hbSmallProbeFinish_wp hc M γ hsvc hext
    (ptr' := ptr') (u0 := u0) (u1 := u1) (u2 := u2) (e1 := e1) hcap' hlc' hblk'
    hpc2 hrun2 hsp2_eq hsp2_al hx19_2 hx20_2 hx22_2
    (hbUpperCS_step (by obtain ⟨_, _⟩ := hup; simp [hbUpperCS, wp_norm, arm64_norm, *]) hcs2)
    (by simpa [wp_norm, arm64_norm, hstd2.1] using hopen)
    (by simp [wp_norm, arm64_norm, hstd2.2.1, htr])
    (by simp [wp_norm, arm64_norm, hstd2.2.2.1, htp])
    (by simp [wp_norm, arm64_norm, hstd2.2.2.2.1, hsig])
    (by sep_frame)

theorem hbSmallProbeRead_ok {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    (hc : HbStdinAndVecCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl) :
    subroutine_ok P C.smallProbeReadAddr (hbSmallProbeReadSpec M γ) := by
  refine subroutine_ok_of_sepWP_frozen
    fun ⟨vecPtr, cap, ptr, bs, rem, lc, blk, e0⟩ R s0 hpc hrun hpre hsp_align => ?_
  dsimp only [hbSmallProbeReadSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hopen0, hsp_lo, hsp_va, hlen32, hcap_lt, hres_lim⟩, hm⟩
  simp only [Reg.x0] at hx0
  have hbs_le : bs.length ≤ cap :=
    HbByteVecBuf_len_le (Satisfies.mono (by dsimp only [HbByteVec]; sep_frame) hm)
  refine ⟨_, hm, ?_⟩
  rw [show hbSmallProbeStackBytes = hbRawVecReserveStackBytes + 8 * 18 from by
        unfold hbSmallProbeStackBytes hbRawVecReserveStackBytes; omega,
      stackAt_split_cells s0.sp hbRawVecReserveStackBytes 18 (by decide)]
  unpack_cells 18
  conv =>
    arg 4; simp only [HbByteVec]
    rw [show s0.sp - BitVec.ofNat 64 (8 * 18) = s0.sp - 144#64 from rfl]
  refine SepWP.seq_nonVm (mid := C.readAddr) hext hsvc ?_
  have hc_nv0 := hc.withSvc nonVmSvc; unpack_hb_stdin_code hbStdinAndVecChunks hc_nv0
  wp_steps; norm_jmp
  apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun])
  intro hvm0
  refine SepWP.weaken_pre (Entails.trans (by sep_frame)
    (Entails.trans (sepConj_mono (four_cells_to_memRegion32 s0.sp _ _ _ _) (Entails.refl _))
      (by sep_frame))) ?_
  conv => arg 4; rw [stackAt_shrink (s0.sp - 144#64) hbRawVecReserveStackBytes 32 (by decide) (by decide)]
  have hbuf_va : (s0.sp - 144#64).toNat + (32#64).toNat ≤ Arm64.USER_VA_LIMIT := by
    unfold Arm64.USER_VA_LIMIT at hsp_va ⊢; bv_omega
  refine call_hbRead hc_sys (rem := rem) (bufPtr := s0.sp - 144#64) (count := 32#64)
    (ret_pc := C.smallProbeReadAddr + 0x3c#64) hsvc hext (by decide) hbuf_va
    (by simpa [State.writeVReg128, wp_norm, arm64_norm] using hopen0)
    (by change ∀ R', _ → _ ⊨ (memRegion (s0.sp - 144#64) 32 ∗ _) ∗ _
        simp only [wp_norm, arm64_norm]; sep_frame)
    (fun s1 hpc1 hrun1 hsp1 hcs1 hx0_1 hopen1 htr1 hnv1 => ?_)
    (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align)
    (hlr := by simp [wp_norm, arm64_norm] <;> bv_lin)
    (hx0 := by simp [wp_norm, arm64_norm])
    (hx1 := by simp [wp_norm, arm64_norm])
    (hx2 := by simp [wp_norm, arm64_norm])
  replace hx0_1 : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 (rem.take 32).length := hx0_1
  replace hopen1 : HbStdinOpen (rem.drop (rem.take 32).length) s1.fs := hopen1
  have hsp1_eq : s1.sp = s0.sp - 144#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
  have hsp1_r : s1.readReg64 Reg.sp = s0.sp - 144#64 := hsp1_eq
  have hsp1_al : s1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq]; exact s0.spAligned_sub 144#64 hsp_align
  have hx19_1 : s1.readReg64 (.gpr 19#5) = vecPtr := by
    rw [← Reg.x19, hcs1.readReg64_x19]; simp [wp_norm, arm64_norm]
  have hup1 : hbUpperCS s0 s1 := hbUpperCS_step
    (by simp [hbUpperCS, isCalleeSavedVReg, wp_norm, arm64_norm]) hcs1
  have htr1' : s1.trace = s0.trace := by rw [htr1]; simp [State.writeVReg128, wp_norm, arm64_norm]
  have htp1' : s1.tpidrEl0 = s0.tpidrEl0 := by
    rw [hnv1.tpidrEl0_eq]; simp [State.writeVReg128, wp_norm, arm64_norm]
  have hsig1' : s1.sigActions = s0.sigActions := by
    rw [hnv1.sigActions_eq]; simp [State.writeVReg128, wp_norm, arm64_norm]
  apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface (hvm0.trans hnv1.vm))
  have herr01 : muslErrnoAddr s0 = muslErrnoAddr s1 := by simp [muslErrnoAddr, htp1']
  have hsp_pre : _ = s0.sp - 144#64 := hsp1.symm.trans hsp1_eq
  have hmin32 : min 32 2147479552 = 32 := rfl
  conv =>
    arg 4
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Arm64.MAX_RW_COUNT, hmin32, herr01, hsp_pre]
  have hsh : memRegion ((s0.sp - 144#64) - BitVec.ofNat 64 hbRawVecReserveStackBytes)
        (hbRawVecReserveStackBytes - 32) ∗ stackAt (s0.sp - 144#64) 32 ⊢
      stackAt (s0.sp - 144#64) hbRawVecReserveStackBytes := by
    rw [stackAt_shrink (s0.sp - 144#64) hbRawVecReserveStackBytes 32 (by decide) (by decide)]
    exact Entails.refl _
  refine SepWP.weaken_pre (Entails.trans (by sep_frame)
    (Entails.trans (sepConj_mono hsh (Entails.refl _)) (by sep_frame))) ?_
  have hchunk_le : (rem.take 32).length ≤ 32 := List.length_take_le 32 rem
  have h_add1 : BitVec.ofNat 64 (rem.take 32).length + 1#64 =
      BitVec.ofNat 64 ((rem.take 32).length + 1) := by rw [← BitVec.ofNat_add]
  have h_ne0 : (BitVec.ofNat 64 ((rem.take 32).length + 1) != 0#64) = true := by
    rw [bne_iff_ne]; intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (rem.take 32).length + 1 < 2 ^ 64)] at this; omega
  have h_eq0_f : (BitVec.ofNat 64 ((rem.take 32).length + 1) == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (bne_iff_ne.mp h_ne0)
  have h_lt33 : BitVec.ult (BitVec.ofNat 64 (rem.take 32).length) 33#64 = true := by
    rw [BitVec.ult_iff_toNat_lt]
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (rem.take 32).length < 2 ^ 64)]; omega
  have h_ule33 : (33#64).ule (BitVec.ofNat 64 (rem.take 32).length) = false := by
    rw [Bool.eq_false_iff, ne_eq, BitVec.ule_iff_toNat_le]
    have : (33#64).toNat = 33 := rfl
    simp only [this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (rem.take 32).length < 2 ^ 64)]; omega
  have h_rem_sub : BitVec.ofNat 64 cap - BitVec.ofNat 64 bs.length =
      BitVec.ofNat 64 (cap - bs.length) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cap < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : bs.length < 2 ^ 64)]; omega
  by_cases hgrow : cap - bs.length < (rem.take 32).length
  · have h_hi : BitVec.ult (BitVec.ofNat 64 (cap - bs.length))
        (BitVec.ofNat 64 (rem.take 32).length) = true := by
      rw [BitVec.ult_iff_toNat_lt]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : (rem.take 32).length < 2 ^ 64)]; exact hgrow
    obtain ⟨hblk_ge, hreq_lim, hlc_lim, hblk_lim⟩ := hres_lim hgrow
    refine SepWP.seq_nonVm (mid := C.rawVecDoReserveAddr) hext hsvc ?_
    have hc_nv1 := hc.withSvc nonVmSvc; unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
    wp_steps; wp_steps; norm_jmp
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
    intro hvm1
    refine hbRawVecDoReserve_wp hc M γ hvm1
      (vecPtr := vecPtr) (oldCap := cap) (oldPtr := ptr) (bs := bs)
      (additional := (rem.take 32).length) (sp_call := s0.sp - 144#64)
      (ret_pc := C.smallProbeReadAddr + 0x158#64)
      (by omega) (by omega) hcap_lt hblk_ge hreq_lim hlc_lim hblk_lim
      (by sep_frame) (fun s2 newPtr e2 hpc2 hrun2 hsp2 hcs2 hmsp2 => ?_) hsvc hext
      (hsp_call := by simpa [wp_norm, arm64_norm] using hsp1_eq)
      (hsp_align := by simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al)
      (hx0 := by simp [wp_norm, arm64_norm])
      (hx1 := by simp [wp_norm, arm64_norm])
      (hx2 := by simp [wp_norm, arm64_norm])
      (hx3 := by simp [wp_norm, arm64_norm])
      (hx4 := by simp [wp_norm, arm64_norm])
    have hx19_2 : s2.readReg64 (.gpr 19#5) = vecPtr := by
      rw [← Reg.x19, hcs2.readReg64_x19]; simp [wp_norm, arm64_norm, hx19_1]
    have hx20_2 : s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 (rem.take 32).length := by
      rw [← Reg.x20, hcs2.readReg64_x20]; simp [wp_norm, arm64_norm]
    have hsp2_eq : s2.sp = s0.sp - 144#64 := by rw [hsp2]; simpa [wp_norm, arm64_norm] using hsp1_eq
    have hsp2_al : s2.spAligned = true := by simpa [State.spAligned, hsp2_eq, hsp1_eq] using hsp1_al
    refine SepWP.seq_nonVm (mid := C.smallProbeReadAddr + 0x68#64) hext hsvc ?_
    have hc_nv2 := hc.withSvc nonVmSvc; unpack_hb_stdin_code hbStdinAndVecChunks hc_nv2
    wp_steps
    apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun2])
    intro hvm2
    apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm2)
    have htp2' : s2.tpidrEl0 = s0.tpidrEl0 := by
      rw [hmsp2.2.2.2.1]; simp [wp_norm, arm64_norm, htp1']
    conv => arg 4; rw [show muslErrnoAddr s2 = muslErrnoAddr s0 from by
      simp [muslErrnoAddr, htp2']]
    refine hbSmallProbeCopyAndFinish_wp hc hMem M γ hsvc hext
      (ptr' := newPtr) (cap' := max (max (bs.length + (rem.take 32).length) (2 * cap)) 8)
      (lc' := lc - hbByteVecCost cap +
        mallocngBlockCost (max (max (bs.length + (rem.take 32).length) (2 * cap)) 8))
      (blk' := blk - hbByteVecBlocks cap + 1)
      (e1 := e2) (by omega) (by omega)
      (by simp only [hgrow, ↓reduceIte]) (by simp only [hgrow, ↓reduceIte])
      (by simp only [hgrow, ↓reduceIte])
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame)
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hrun2]
    · simpa [wp_norm, arm64_norm] using hsp2_eq
    · simpa [State.spAligned, wp_norm, arm64_norm] using hsp2_al
    · simp [wp_norm, arm64_norm, hx19_2]
    · simp [wp_norm, arm64_norm, hx20_2]
    · simp [wp_norm, arm64_norm]
    · obtain ⟨_, _⟩ := hbUpperCS_step (s0 := s0)
        (by obtain ⟨_, _⟩ := hup1; simp [hbUpperCS, wp_norm, arm64_norm, *]) hcs2
      simp [hbUpperCS, wp_norm, arm64_norm, *]
    · simpa [wp_norm, arm64_norm, hmsp2.1] using hopen1
    · simp [wp_norm, arm64_norm, hmsp2.2.1, htr1']
    · simp [wp_norm, arm64_norm, htp2']
    · simp [wp_norm, arm64_norm, hmsp2.2.2.1, hsig1']
  · have h_hi : BitVec.ult (BitVec.ofNat 64 (cap - bs.length))
        (BitVec.ofNat 64 (rem.take 32).length) = false := by
      rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_toNat_lt]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cap - bs.length < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : (rem.take 32).length < 2 ^ 64)]; omega
    rcases Nat.eq_zero_or_pos (rem.take 32).length with h0 | hpos
    · have hnil : rem.take 32 = [] := List.eq_nil_of_length_eq_zero h0
      have h_zero_bv : BitVec.ofNat 64 (rem.take 32).length = 0#64 := by rw [h0]
      have h_hi0 : (BitVec.ofNat 64 (cap - bs.length)).ult 0#64 = false := by
        rw [← h_zero_bv]; exact h_hi
      refine SepWP.seq_nonVm (mid := C.smallProbeReadAddr + 0x7c#64) hext hsvc ?_
      have hc_nv1 := hc.withSvc nonVmSvc; unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
      wp_steps
      apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
      intro hvm1
      apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
      conv =>
        arg 4
        rw [← herr01]
        rw [show HbByteVecBuf M.toMallocngCoreIface γ cap ptr bs =
          HbByteVecBuf M.toMallocngCoreIface γ cap ptr (bs ++ rem.take 32) from by rw [hnil, List.append_nil]]
      refine hbSmallProbeFinish_wp hc M γ hsvc hext
        (ptr' := ptr) (cap' := cap) (lc' := lc) (blk' := blk) (e1 := e0)
        (by simp only [hgrow, ↓reduceIte]) (by simp only [hgrow, ↓reduceIte])
        (by simp only [hgrow, ↓reduceIte])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame)
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hrun1]
      · simpa [wp_norm, arm64_norm] using hsp1_eq
      · simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al
      · simp [wp_norm, arm64_norm, hx19_1]
      · simp only [wp_norm, arm64_norm]; exact h_zero_bv.symm
      · simp [wp_norm, arm64_norm]
      · obtain ⟨_, _⟩ := hup1; simp [hbUpperCS, wp_norm, arm64_norm, *]
      · simpa [wp_norm, arm64_norm] using hopen1
      · simp [wp_norm, arm64_norm, htr1']
      · simp [wp_norm, arm64_norm, htp1']
      · simp [wp_norm, arm64_norm, hsig1']
    · have h_nz_c : (BitVec.ofNat 64 (rem.take 32).length == 0#64) = false := by
        rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : (rem.take 32).length < 2 ^ 64)] at this; omega
      refine SepWP.seq_nonVm (mid := C.smallProbeReadAddr + 0x68#64) hext hsvc ?_
      have hc_nv1 := hc.withSvc nonVmSvc; unpack_hb_stdin_code hbStdinAndVecChunks hc_nv1
      wp_steps
      apply SepWP.done wp_a (by simp [wp_norm, arm64_norm, hrun1])
      intro hvm1
      apply sepWP_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm1)
      conv => arg 4; rw [← herr01]
      refine hbSmallProbeCopyAndFinish_wp hc hMem M γ hsvc hext
        (ptr' := ptr) (cap' := cap) (lc' := lc) (blk' := blk) (e1 := e0) hpos (by omega)
        (by simp only [hgrow, ↓reduceIte]) (by simp only [hgrow, ↓reduceIte])
        (by simp only [hgrow, ↓reduceIte])
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame)
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hrun1]
      · simpa [wp_norm, arm64_norm] using hsp1_eq
      · simpa [State.spAligned, wp_norm, arm64_norm] using hsp1_al
      · simp [wp_norm, arm64_norm, hx19_1]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm]
      · obtain ⟨_, _⟩ := hup1; simp [hbUpperCS, wp_norm, arm64_norm, *]
      · simpa [wp_norm, arm64_norm] using hopen1
      · simp [wp_norm, arm64_norm, htr1']
      · simp [wp_norm, arm64_norm, htp1']
      · simp [wp_norm, arm64_norm, hsig1']

theorem hbSmallProbeRead_wp {P : Program} {C : HbCliLayout} {lim : MallocngLimits}
    {target_pc ret_pc sp_call : BitVec 64}
    (hc : HbStdinAndVecCode P C) (hc_sys : HbSyscallsAndStderrCode P C)
    (hMem : StdMemOps P C.std.memcpyAddr C.std.memsetAddr)
    (M : HbMallocngIface P C.mallocng lim) (γ : GhostName)
    {vecPtr ptr : BitVec 64} {cap lc blk : Nat}
    {bs rem : List (BitVec 8)} {e0 : BitVec 32}
    {s0 s : State} {Pre F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmFieldsPreserved s0 s := by exact ⟨rfl, rfl, rfl, fun _ => rfl⟩)
    (hopen : HbStdinOpen rem s.fs)
    (hsp_lo : 144 ≤ sp_call.toNat) (hsp_va : sp_call.toNat ≤ Arm64.USER_VA_LIMIT)
    (hlen32 : bs.length + 32 < 2 ^ 63) (hcap_lt : cap < 2 ^ 62)
    (hres_lim : cap - bs.length < (rem.take 32).length →
      let growCap := max (max (bs.length + (rem.take 32).length) (2 * cap)) 8
      hbByteVecBlocks cap ≤ blk ∧
      growCap ≤ lim.maxReq ∧
      lc + mallocngBlockCost growCap ≤ lim.maxPeakCost ∧
      blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (HbByteVec M.toMallocngCoreIface γ vecPtr cap ptr bs ∗
        M.Heap γ lc blk s0 ∗
        (muslErrnoAddr s0 ↦₃₂ e0) ∗
        stackAt sp_call hbSmallProbeStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (ptr' : BitVec 64) (e1 : BitVec 32),
      let chunk := rem.take 32
      let growCap := max (max (bs.length + chunk.length) (2 * cap)) 8
      let cap' := if cap - bs.length < chunk.length then growCap else cap
      let lc' := if cap - bs.length < chunk.length
        then lc - hbByteVecCost cap + mallocngBlockCost growCap else lc
      let blk' := if cap - bs.length < chunk.length then blk - hbByteVecBlocks cap + 1 else blk
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 → sf.readReg64 .x1 = BitVec.ofNat 64 chunk.length →
      HbStdinOpen (rem.drop chunk.length) sf.fs →
      sf.trace = s.trace → sf.tpidrEl0 = s.tpidrEl0 → sf.sigActions = s.sigActions →
      s.mem.KeepsFrozen sf.mem →
      SepWP P target_pc sf
        ((HbByteVec M.toMallocngCoreIface γ vecPtr cap' ptr' (bs ++ chunk) ∗
          M.Heap γ lc' blk' sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗
          stackAt sp_call hbSmallProbeStackBytes) ∗ F) post oom)
    (hsvc : P.svc = Syscall.standard := by rfl)
    (hext : ∀ pc, P.externAt? pc = none := by intro _; rfl)
    (hpc : s.pc = C.smallProbeReadAddr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hrun : s.status = .Running := by simp only [arm64_norm, *])
    (hsp_call : s.sp = sp_call := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (herr0 : muslErrnoAddr s0 = muslErrnoAddr s := by simp [muslErrnoAddr, wp_norm, arm64_norm, *])
    (hsp_align : s.spAligned = true := by
      simp (config := { decide := true }) only [State.spAligned, arm64_norm, *]
      try (simp only [State.spAligned, beq_iff_eq] at *; bv_bits))
    (hlr : s.readReg64 Reg.lr = ret_pc := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (hx0 : s.readReg64 .x0 = vecPtr := by simp (config := { decide := true }) only [arm64_norm, bv_lin_norm, *]; try bv_lin)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by wp_close_oom_default) :
    SepWP P target_pc s Pre post oom := by
  refine SepWP.call_subroutine_frame
    (hbSmallProbeRead_ok hc hc_sys hMem M γ hsvc hext)
    (x := (vecPtr, cap, ptr, bs, rem, lc, blk, e0)) (F := F)
    hpc hrun hsp_align hlr ?_ (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ h_oom
  · intro R hm
    dsimp only [hbSmallProbeReadSpec]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hopen, hsp_call ▸ hsp_lo, hsp_call ▸ hsp_va, hlen32, hcap_lt, hres_lim⟩, ?_⟩
    have hm' := hpre R hm
    rw [herr0, ← hsp_call] at hm'
    exact Satisfies.mono (entails_mono_atom (vmHeapTransport M.toMallocngCoreIface hvm)) hm'
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only [hbSmallProbeReadSpec]
    conv => arg 4; rw [hsp_call]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun ptr' => SepWP.exists_elim fun e1 => ?_
    conv => arg 4; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hx0_f, hx1_f, hopen_f, htr_f, htp_f, hsig_f, hkf_f⟩
    exact SepWP.weaken_pre (by sep_frame)
      (hnext sf ptr' e1 hpc_f hrun_f hsp_f hcs_f hx0_f hx1_f hopen_f htr_f htp_f hsig_f hkf_f)

end CaseStudies.Hashbrown.Proofs.StdCli
