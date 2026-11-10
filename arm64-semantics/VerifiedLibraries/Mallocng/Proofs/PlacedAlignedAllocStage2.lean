/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocStage1
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `aligned_alloc` Stage 2

Header-offset bitvector lemmas, shared `blk12` epilogue combinators, and symbolic execution of the
`delta = 0` (`new_p = p`) `set_size` stage (`alignedAlloc_reframe_delta0_ok`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## `set_size` and Header-Offset Algebra -/

theorem bv_madd_slotEnd {g : GroupDesc} {idx : Nat} (hStr16 : 16 ≤ g.stride)
    (_hEnd48 : (g.slotEnd idx).toNat ≤ 2 ^ 48) (hIdx31 : idx ≤ 31) :
    ((g.mem + 16#64) +
      (((BitVec.ofNat 32 idx).zeroExtend 64 + 1#64).truncate 32).signExtend 64 *
        BitVec.ofNat 64 g.stride) - 4#64 = g.slotEnd idx := by
  have hAdd1 : (((BitVec.ofNat 32 idx).zeroExtend 64 + 1#64).truncate 32).signExtend 64 =
      BitVec.ofNat 64 (idx + 1) := by
    have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
    rw [show BitVec.ofNat 64 (idx + 1) = (BitVec.ofNat 32 idx).zeroExtend 64 + 1#64 by bv_omega]
    revert hlt; bv_robdd
  rw [hAdd1, ← BitVec.ofNat_mul, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
  have hStrideEq : BitVec.ofNat 64 g.stride = BitVec.ofNat 64 (g.stride - 4) + 4#64 := by
    conv => lhs; rw [show g.stride = (g.stride - 4) + 4 by omega, BitVec.ofNat_add]
  unfold GroupDesc.slotEnd GroupDesc.slotStart GroupDesc.storage
  rw [hStrideEq]; bv_lin

theorem bv_madd_slotStart {g : GroupDesc} {idx : Nat} (hIdx31 : idx ≤ 31) :
    (g.mem + 16#64) + (((BitVec.ofNat 32 idx).zeroExtend 64) &&& 0xff#64) * BitVec.ofNat 64 g.stride =
      g.slotStart idx := by
  have hMask : ((BitVec.ofNat 32 idx).zeroExtend 64) &&& 0xff#64 = BitVec.ofNat 64 idx := by
    have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
    rw [show BitVec.ofNat 64 idx = (BitVec.ofNat 32 idx).zeroExtend 64 by bv_omega]
    revert hlt; bv_robdd
  rw [hMask, ← BitVec.ofNat_mul]; rfl

theorem res_subs32_eq {endPtr q len : BitVec 64}
    (hFit : q.toNat + len.toNat ≤ endPtr.toNat) (hEnd48 : endPtr.toNat ≤ 2 ^ 48) :
    (endPtr - q).truncate 32 - len.truncate 32 =
      BitVec.ofNat 32 (endPtr.toNat - (q.toNat + len.toNat)) := by
  have hSub64 : (endPtr - q) - len = BitVec.ofNat 64 (endPtr.toNat - (q.toNat + len.toNat)) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : q ≤ endPtr := BitVec.le_def.mpr (by omega)
    have h2 : len ≤ endPtr - q := by
      rw [BitVec.le_def, BitVec.toNat_sub_of_le h1]; omega
    rw [BitVec.toNat_sub_of_le h2, BitVec.toNat_sub_of_le h1,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hHom : ∀ a b : BitVec 64, a.truncate 32 - b.truncate 32 = (a - b).truncate 32 := by
    intro a b; bv_robdd
  rw [hHom, hSub64]; bv_omega

theorem slotEnd_add_sxtw_neg_res {endPtr q len : BitVec 64}
    (hFit : q.toNat + len.toNat ≤ endPtr.toNat) (hEnd48 : endPtr.toNat ≤ 2 ^ 48)
    (hResPos : 1 ≤ endPtr.toNat - (q.toNat + len.toNat))
    (hRes31 : endPtr.toNat - (q.toNat + len.toNat) < 2 ^ 31) :
    endPtr + (0#32 - BitVec.ofNat 32 (endPtr.toNat - (q.toNat + len.toNat))).signExtend 64 =
      q + len := by
  let res := endPtr.toNat - (q.toNat + len.toNat)
  have hNegSxtw : (0#32 - BitVec.ofNat 32 res).signExtend 64 = 0#64 - BitVec.ofNat 64 res := by
    have hLo : (0#32).ult (BitVec.ofNat 32 res) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change 0 < res % 4294967296; omega
    have hHi : (BitVec.ofNat 32 res).ult (1#32 <<< 31) = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change res % 4294967296 < 2147483648; omega
    rw [show BitVec.ofNat 64 res = (BitVec.ofNat 32 res).zeroExtend 64 by bv_omega]
    revert hLo hHi; bv_robdd
  rw [hNegSxtw]
  apply BitVec.eq_of_toNat_eq
  have hSub : endPtr + (0#64 - BitVec.ofNat 64 res) = endPtr - BitVec.ofNat 64 res := by bv_robdd
  have hLe : BitVec.ofNat 64 res ≤ endPtr := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hSub, BitVec.toNat_sub_of_le hLe, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  dsimp only [res]; omega

theorem eq_of_sub32_eq_zero {a b : BitVec 32} (h : a - b = 0#32) : a = b := by
  revert h; bv_robdd

theorem hdr3_pack_le4 {b0 : BitVec 8} {idx res : Nat}
    (hLow : b0.zeroExtend 32 &&& 0x1f#32 = BitVec.ofNat 32 idx)
    (hIdx : idx ≤ 31) (hResLo : 1 ≤ res) (hResHi : res ≤ 4) :
    (((b0.zeroExtend 64 &&& 133143986207#64).truncate 32 +
      (BitVec.ofNat 32 res <<< 5)).zeroExtend 64 &&& 255#64).truncate 8 =
      BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx) := by
  have hEq : ∀ (x : BitVec 8) (y : BitVec 32),
      (((x.zeroExtend 64 &&& 133143986207#64).truncate 32 + y).zeroExtend 64 &&& 255#64).truncate 8 =
        (((x.zeroExtend 32 &&& 0x1f#32) + y) &&& 0xff#32).truncate 8 := by intros; bv_robdd
  rw [hEq, hLow, Nat.min_eq_left (by omega : res ≤ 5)]
  have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
  rcases (by omega : res = 1 ∨ res = 2 ∨ res = 3 ∨ res = 4) with rfl | rfl | rfl | rfl
  · rw [show BitVec.ofNat 8 ((1 <<< 5) ||| idx) = ((BitVec.ofNat 32 idx ||| 32#32).truncate 8) by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : idx < 256), Nat.or_comm]]
    revert hlt; bv_robdd
  · rw [show BitVec.ofNat 8 ((2 <<< 5) ||| idx) = ((BitVec.ofNat 32 idx ||| 64#32).truncate 8) by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : idx < 256), Nat.or_comm]]
    revert hlt; bv_robdd
  · rw [show BitVec.ofNat 8 ((3 <<< 5) ||| idx) = ((BitVec.ofNat 32 idx ||| 96#32).truncate 8) by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : idx < 256), Nat.or_comm]]
    revert hlt; bv_robdd
  · rw [show BitVec.ofNat 8 ((4 <<< 5) ||| idx) = ((BitVec.ofNat 32 idx ||| 128#32).truncate 8) by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : idx < 256), Nat.or_comm]]
    revert hlt; bv_robdd

theorem hdr3_pack_ge5 {b0 : BitVec 8} {idx res : Nat}
    (hLow : b0.zeroExtend 32 &&& 0x1f#32 = BitVec.ofNat 32 idx)
    (hIdx : idx ≤ 31) (hResGe5 : 5 ≤ res) :
    (((b0.zeroExtend 64 &&& 133143986207#64).truncate 32 - 96#32).zeroExtend 64 &&& 255#64).truncate 8 =
      BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx) := by
  have hEq : ∀ (x : BitVec 8),
      (((x.zeroExtend 64 &&& 133143986207#64).truncate 32 - 96#32).zeroExtend 64 &&& 255#64).truncate 8 =
        (((x.zeroExtend 32 &&& 0x1f#32) - 0x60#32) &&& 0xff#32).truncate 8 := by intros; bv_robdd
  rw [hEq, hLow, Nat.min_eq_right hResGe5]
  have hlt : (BitVec.ofNat 32 idx).ult 32#32 = true := by
    rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change idx % 4294967296 < 32; omega
  rw [show BitVec.ofNat 8 ((5 <<< 5) ||| idx) = ((BitVec.ofNat 32 idx ||| 160#32).truncate 8) by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_or, Nat.mod_eq_of_lt (by omega : idx < 256), Nat.or_comm]]
  revert hlt; bv_robdd

theorem bv32_sle4_iff {res : Nat} (hRes31 : res < 2 ^ 31) :
    (BitVec.ofNat 32 res).sle 4#32 = decide (res ≤ 4) := by
  have hToInt : (BitVec.ofNat 32 res).toInt = (res : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; split <;> omega
  rw [BitVec.sle, hToInt, show (4#32 : BitVec 32).toInt = 4 from rfl]
  by_cases h : res ≤ 4 <;> simp [h] <;> omega

theorem tot_lsr4_eq {new_p stor : BitVec 64}
    (hLo : stor.toNat ≤ new_p.toNat) (hNew48 : new_p.toNat ≤ 2 ^ 48) :
    (new_p - stor) >>> 4 = BitVec.ofNat 64 ((new_p.toNat - stor.toNat) / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (BitVec.le_def.mpr hLo),
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem tot_cmp_hi_iff {tot : Nat} (hTot27 : tot < 2 ^ 27) :
    ConditionHolds .HI (subsPState32 ((BitVec.ofNat 64 tot).truncate 32) 0xffff#32) =
      decide (¬ tot ≤ 0xffff) := by
  rw [conditionHolds_hi_subsPState32,
    show (BitVec.ofNat 64 tot).truncate 32 = BitVec.ofNat 32 tot by bv_omega, BitVec.ult]
  have hMod : (BitVec.ofNat 32 tot).toNat = tot := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hMod, show (0xffff#32 : BitVec 32).toNat = 65535 from rfl]
  by_cases h : tot ≤ 65535 <;> simp [h] <;> omega

/-! ## Shared Epilogue and `ReframeExitPost` -/

def AlignedSpillSlots (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 20#5))

theorem spillSlots_repack_736 (sp0 : BitVec 64) (s0 : State) :
    (stackFrameAt (sp0 - 32#64) 704 ∗ AlignedSpillSlots sp0 s0) ⊢ stackFrameAt sp0 736 := by
  rw [stackFrameAt_736_split sp0]; dsimp only [AlignedSpillSlots]; cells_unfold; sep_frame

private theorem alignedAlloc_epilogue_ok [MallocngMultiPlacement] {b : BitVec 64} (hb : BlkBase 12 b)
    {s0 s : State} {sp0 retVal : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0xa4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = retVal)
    (hx19 : s.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : s.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP (blkPC_b12.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (AlignedSpillSlots sp0 s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ AlignedSpillSlots sp0 s0 ∗ Rest) ∧
        sf.mem = s.mem ∧ sf.brk = s.brk ∧ MallocngProcPreserved s sf ∧
        sf.readReg64 .x0 = retVal ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) oom := by
  have _ := hb
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have _hspAl32 : ((sp0 - 32#64) &&& 15#64 == 0#64) = true := by revert hspAl0'; bv_robdd
  have ha8 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have ha32 : sp0 - 32#64 + 32#64 = sp0 := by bv_arith
  conv => arg 4; dsimp only [AlignedSpillSlots]
  wp_step; wp_step
  obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs21_28
  refine SepWP.done (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    ⟨by dsimp only [AlignedSpillSlots]; exact Entails.refl _,
     rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
     by simp [arm64_norm, hx0],
     by simp [arm64_norm, hsp0],
     ⟨by simp [arm64_norm, hx19], by simp [arm64_norm, hx20],
      by simp [arm64_norm, h21], by simp [arm64_norm, h22], by simp [arm64_norm, h23],
      by simp [arm64_norm, h24], by simp [arm64_norm, h25], by simp [arm64_norm, h26],
      by simp [arm64_norm, h27], by simp [arm64_norm, h28], by simp [arm64_norm],
      by simp [calleeSavedVRegs, hv]⟩⟩

def ReframeExitPost [MallocngMultiPlacement] (s0 s4 : State) (sp0 new_p : BitVec 64)
    (st : MallocngSt) (p : BitVec 64) (eff : Nat) (Rest : SepProp)
    (P : (BitVec 64 → BitVec 8) → Prop) (sf : State) (Pf : SepProp) : Prop :=
  ∃ bv : BitVec 64 → BitVec 8,
    P bv ∧
    (Pf ⊢ ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗ AlignedSpillSlots sp0 s0 ∗ Rest) ∧
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem ∧
    sf.mem.perm = s4.mem.perm ∧ sf.brk = s4.brk ∧ MallocngProcPreserved s4 sf ∧
    sf.readReg64 .x0 = new_p ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def ReframeBvSpec (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (new_p len : BitVec 64) (bv : BitVec 64 → BitVec 8) : Prop :=
  let res' := (g.slotEnd idx).toNat - (new_p.toNat + len.toNat)
  let tot' := (new_p.toNat - g.storage.toNat) / 16
  (∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a) ∧
  bv (new_p - 3#64) = BitVec.ofNat 8 ((min res' 5 <<< 5) ||| idx) ∧
  (if tot' ≤ 0xffff then
     bv (new_p - 4#64) = 0#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
   else
     bv (new_p - 4#64) = 1#8 ∧ readBytesFromMap bv (new_p - 2#64) 2 = [0#8, 0#8] ∧
       readBytesFromMap bv (new_p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot')) ∧
  (1 ≤ res' → bv (new_p + len) = 0#8) ∧
  (5 ≤ res' → bv (g.slotEnd idx - 5#64) = 0#8 ∧
    readBytesFromMap bv (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32 res'))

theorem subRegion_of_bounds {lo ea : BitVec 64} {len subLen : Nat}
    (h48 : lo.toNat + len ≤ 2 ^ 48) (heaLo : lo.toNat ≤ ea.toNat)
    (heaHi : ea.toNat + subLen ≤ lo.toNat + len) :
    ∀ a : BitVec 64, InRegion ea subLen a → InRegion lo len a := by
  have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  intro a ha
  have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
  exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩

theorem not_inRegion_one_of_ne {ea a : BitVec 64} (hBound : ea.toNat + 1 ≤ 2 ^ 64)
    (hNe : a ≠ ea) : ¬ InRegion ea 1 a := fun hIn => by
  have ⟨_, _⟩ := (inRegion_iff_toNat (n := 1) hBound a).mp hIn
  exact hNe (BitVec.eq_of_toNat_eq (by omega))

theorem outBand_write {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    {bv : BitVec 64 → BitVec 8} {ea : BitVec 64} {bs : List (BitVec 8)}
    (hBand : ∀ a, InRegion ea bs.length a → InRegion (g.slotStart idx - 3#64) (g.stride - 1) a)
    (hPrev : ∀ a, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv a = st.byteVal a) :
    ∀ a, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      writeBytesToMap bv ea bs a = st.byteVal a := fun a hNot => by
  rw [writeBytesToMap_out bv ea bs (fun hIn => hNot (hBand a hIn))]
  exact hPrev a hNot

theorem ldp19_20_to_epilogue [MallocngMultiPlacement] {prog : Program}
    {b : BitVec 64} (hb : BlkBase 12 b) (hprog : prog = mallocngBlockProg mmpl 12 msvc)
    {s0 s4 s : State} {sp0 new_p : BitVec 64} {st : MallocngSt} {p : BitVec 64} {eff : Nat}
    {bv : BitVec 64 → BitVec 8} {Rest : SepProp} {P : (BitVec 64 → BitVec 8) → Prop}
    {oom : State → SepProp} {offLdp : Nat}
    (hFetchLdp : prog.fetch (b + BitVec.ofNat 64 offLdp) =
      some (.ldp .W64 false (.gpr 19#5) (.gpr 20#5) (.Offset .sp 16#64)))
    (hFetchBr : prog.fetch (b + BitVec.ofNat 64 (offLdp + 4)) =
      some (.b (0xa4#64 - BitVec.ofNat 64 (offLdp + 4))))
    (hBrEq : b + BitVec.ofNat 64 (offLdp + 4) + (0xa4#64 - BitVec.ofNat 64 (offLdp + 4)) = b + 0xa4#64)
    (hpc : s.pc = b + BitVec.ofNat 64 offLdp) (hrun : s.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk)
    (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = new_p)
    (hcs21_28 : CalleeSaved21_28 s0 s)
    (hPbv : P bv) :
    SepWP prog (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 new_p st p eff Rest P) oom := by
  have hProgEq : prog = blkPC_b12.rebase b (fun _ => none) := by
    rw [hprog, mallocngBlockProg_eq_b12, hb]
  subst hProgEq
  have hspAl0' : (sp0 &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp0] using hspAl0
  have hspAl32 : ((sp0 - 32#64) &&& 15#64 == 0#64) = true := by revert hspAl0'; bv_robdd
  have ha16 : sp0 - 32#64 + 16#64 = sp0 - 16#64 := by bv_arith
  have ha24 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_arith
  have h4 : b + BitVec.ofNat 64 offLdp + 4#64 = b + BitVec.ofNat 64 (offLdp + 4) := by
    rw [BitVec.ofNat_add]; bv_arith
  conv => arg 4; dsimp only [AlignedSpillSlots]
  let sLdp := (s.writeReg64 (.gpr 19#5) (s0.readReg64 (.gpr 19#5))).writeReg64 (.gpr 20#5) (s0.readReg64 (.gpr 20#5))
  refine SepWP.step_ldp64 (ea := sp0 - 16#64) (ea2 := sp0 - 8#64) (wb := none)
    (s' := sLdp.setPC (b + BitVec.ofNat 64 (offLdp + 4)))
    hpc hrun hFetchLdp
    (by simp only [checkAddrSPAligned, checkRegSPAligned, State.spAligned, hsp]; exact hspAl32)
    (by simp only [evalAddrMode, arm64_norm, hsp, ha16]) ha24 (by wp_sep_access) (by wp_sep_access)
    (by simp only [applyWriteback, h4, sLdp]) ?_
  refine SepWP.step_pure_setPC (s' := sLdp.setPC (b + 0xa4#64))
    (by simp [arm64_norm, hrun, sLdp]) hFetchBr
    (by simp [Program.evalInst, execInstWithSvc, State.setPC, hBrEq]) rfl ?_
  dsimp only [sLdp]
  have hSwap :
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗
        (((sp0 - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((sp0 - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((sp0 - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((sp0 - 8#64) ↦₆₄ s0.readReg64 (.gpr 20#5))) ∗ Rest) =
      (AlignedSpillSlots sp0 s0 ∗
        (ByteMap st.masterDom (alignedSlotKeep st p eff) bv ∗ Rest)) := by
    dsimp only [AlignedSpillSlots]; ac_rfl
  rw [hSwap]
  obtain ⟨h21, h22, h23, h24, h25, h26, h27, h28, hv⟩ := hcs21_28
  refine SepWP.mono (alignedAlloc_epilogue_ok hb rfl (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simpa [arm64_norm] using hx0)
    (by simp [arm64_norm]) (by simp [arm64_norm])
    ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22], by simp [arm64_norm, h23],
     by simp [arm64_norm, h24], by simp [arm64_norm, h25], by simp [arm64_norm, h26],
     by simp [arm64_norm, h27], by simp [arm64_norm, h28], by simp [calleeSavedVRegs, hv]⟩) ?_
  rintro sf Pf _ _ ⟨hEnt, hmem_f, hbrk_f, hproc_f, hx0_f, hsp_f, hcs_f⟩
  refine ⟨bv, hPbv, Entails.trans hEnt (by sep_frame), hmem_f ▸ hcl,
    (congrArg Memory.perm hmem_f).trans hperm, hbrk_f.trans hbrk,
    alignedProcPreserved_trans hproc hproc_f, hx0_f, hsp_f, hcs_f⟩

theorem step_bm8 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc next_pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 8}
    (hpc : s.pc = pc) (hnext_pc : pc + 4#64 = next_pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : (s.readReg64 rt).truncate 8 = val)
    (hDom : ∀ a, InRegion ea 1 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 1 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC next_pc).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea [val]) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom :=
  step_byteMap_str8 hNodup hpc hrun hfetch hsp haddr hval hDom hKeep
    (fun m' hm' hkf' => hnext_pc.symm ▸ hnext m' hm' hkf')

theorem step_bm16 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc next_pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 16}
    (hpc : s.pc = pc) (hnext_pc : pc + 4#64 = next_pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : (s.readReg64 rt).truncate 16 = val)
    (hDom : ∀ a, InRegion ea 2 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 2 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC next_pc).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea (unpack16 val)) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom :=
  step_byteMap_str16 hNodup hpc hrun hfetch hsp haddr hval hDom hKeep
    (fun m' hm' hkf' => hnext_pc.symm ▸ hnext m' hm' hkf')

theorem step_bm32 {prog : Program} {tgt : BitVec 64}
    {s : State} {dom : List (BitVec 64)} (hNodup : dom.Nodup)
    {keep : BitVec 64 → Prop} [DecidablePred keep] {bv : BitVec 64 → BitVec 8}
    {Rest : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc next_pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {val : BitVec 32}
    (hpc : s.pc = pc) (hnext_pc : pc + 4#64 = next_pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, none))
    (hval : s.readReg32 rt = val)
    (hDom : ∀ a, InRegion ea 4 a → a ∈ dom) (hKeep : ∀ a, InRegion ea 4 a → keep a)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog tgt ((s.setPC next_pc).setMem m')
        (ByteMap dom keep (writeBytesToMap bv ea (unpack32 val)) ∗ Rest) post oom) :
    SepWP prog tgt s (ByteMap dom keep bv ∗ Rest) post oom :=
  step_byteMap_str32 hNodup hpc hrun hfetch hsp haddr hval hDom hKeep
    (fun m' hm' hkf' => hnext_pc.symm ▸ hnext m' hm' hkf')

/-! ## Reframe `delta = 0` Stage -/

set_option maxHeartbeats 400000 in
theorem alignedAlloc_reframe_delta0_ok [MallocngMultiPlacement] {prog : Program}
    {b : BitVec 64} (hb : BlkBase 12 b) (hprog : prog = mallocngBlockProg mmpl 12 msvc)
    {base brkStart : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    {s0 s4 s : State}
    (hwf : MallocngWF base brkStart s4.brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p len : BitVec 64} {eff : Nat}
    (hSlot : g.slots[idx]'hIdx = .liveUser p eff (max eff MallocngMinBlockCost))
    (hFit : p.toNat + len.toNat ≤ (g.slotEnd idx).toNat)
    (hRes31 : (g.slotEnd idx).toNat - (p.toNat + len.toNat) < 2 ^ 31)
    {bv0 : BitVec 64 → BitVec 8}
    (hInBand : ∀ a : BitVec 64, InRegion (g.slotStart idx - 3#64) (g.stride - 1) a →
      alignedSlotKeep st p eff a ∧ a ∈ st.masterDom)
    (hOut0 : ∀ a : BitVec 64, ¬ InRegion (g.slotStart idx - 3#64) (g.stride - 1) a → bv0 a = st.byteVal a)
    (hLtP0 : ∀ a : BitVec 64, a.toNat < p.toNat → bv0 a = st.byteVal a)
    {sp0 : BitVec 64} {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x26c#64) (hrun : s.status = .Running)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hperm : s.mem.perm = s4.mem.perm) (hbrk : s.brk = s4.brk)
    (hproc : MallocngProcPreserved s4 s)
    (hsp : s.sp = sp0 - 32#64) (hsp0 : s0.sp = sp0) (hspAl0 : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = p)
    (hx2 : s.readReg64 .x2 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx3 : s.readReg64 .x3 = g.slotEnd idx)
    (hx20 : s.readReg64 .x20 = len)
    (hcs21_28 : CalleeSaved21_28 s0 s) :
    SepWP prog (s0.readReg64 .lr) s
      (ByteMap st.masterDom (alignedSlotKeep st p eff) bv0 ∗ AlignedSpillSlots sp0 s0 ∗ Rest)
      (ReframeExitPost s0 s4 sp0 p st p eff Rest (ReframeBvSpec st g idx p len)) oom := by
  have hProgEq : prog = blkPC_b12.rebase b (fun _ => none) := by
    rw [hprog, mallocngBlockProg_eq_b12, hb]
  subst hProgEq
  have _ := hb
  have _h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hNodup := hwf.masterDom_wf.1
  have hGWf := hwf.groups_wf g hg
  have hSWf := hGWf.slot_wf idx hIdx; rw [hSlot] at hSWf
  have ⟨hEn48, hIdx31, hBand48, _hP16, _hBandLo, _hBandHi, _hPSub3Lo, _hPSub3Hi⟩ :
      (g.slotEnd idx).toNat ≤ 2 ^ 48 ∧ idx ≤ 31 ∧
      (g.slotStart idx - 3#64).toNat + (g.stride - 1) ≤ 2 ^ 48 ∧ 16 ≤ p.toNat ∧
      (g.slotStart idx - 3#64).toNat + 3 ≤ p.toNat ∧
      (g.slotEnd idx).toNat ≤ (g.slotStart idx - 3#64).toNat + (g.stride - 1) ∧
      (p - 3#64).toNat + 3 ≤ p.toNat ∧ p.toNat ≤ (p - 3#64).toNat + 3 := by
    have ⟨_hStr16, _⟩ := group_stride_pos_and_align hGWf
    have ⟨_hIdxCnt, _hStorNat, _hStNat, _, _hEnNat, _hEndLeTot, _hTot48, _, _⟩ :=
      group_slot_bounds hGWf hIdx
    have _hLast31 : g.lastIdx ≤ 31 := hGWf.2.1
    have _hCntEq : g.cnt = g.lastIdx + 1 := rfl
    have _hMul1 : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.add_one_mul idx g.stride
    have _hSub3Nat := bv64_sub_toNat (a := g.slotStart idx) (n := 3) (by omega)
    have _hPLo := hSWf.2.2.2.2.2.1
    have _hPSub3 := bv64_sub_toNat (a := p) (n := 3) (by omega)
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hLowOld : (bv0 (p - 3#64)).zeroExtend 32 &&& 0x1f#32 = BitVec.ofNat 32 idx := by
    have hHdr3Old : bv0 (p - 3#64) =
        BitVec.ofNat 8 ((min ((g.slotEnd idx).toNat - (p.toNat + eff)) 5 <<< 5) ||| idx) := by
      rw [hLtP0 _ (by omega)]; exact hSWf.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [hHdr3Old]; exact (hdrByte_extract _ idx (Nat.min_le_right _ _) hIdx31).1
  have hHdrOffPres : ∀ bv : BitVec 64 → BitVec 8,
      (∀ a : BitVec 64, a.toNat < p.toNat → a ≠ p - 3#64 → bv a = bv0 a) →
      let tot' := (p.toNat - g.storage.toNat) / 16
      if tot' ≤ 0xffff then bv (p - 4#64) = 0#8 ∧ readBytesFromMap bv (p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
      else bv (p - 4#64) = 1#8 ∧ readBytesFromMap bv (p - 2#64) 2 = [0#8, 0#8] ∧
        readBytesFromMap bv (p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot') := by
    have hHdrOffOld :
        let tot' := (p.toNat - g.storage.toNat) / 16
        if tot' ≤ 0xffff then bv0 (p - 4#64) = 0#8 ∧ readBytesFromMap bv0 (p - 2#64) 2 = unpack16 (BitVec.ofNat 16 tot')
        else bv0 (p - 4#64) = 1#8 ∧ readBytesFromMap bv0 (p - 2#64) 2 = [0#8, 0#8] ∧
          readBytesFromMap bv0 (p - 8#64) 4 = unpack32 (BitVec.ofNat 32 tot') := by
      have hOld := hSWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dsimp only [] at hOld ⊢
      have _hPSub4 := bv64_sub_toNat (a := p) (n := 4) (by omega)
      have _hPSub2 := bv64_sub_toNat (a := p) (n := 2) (by omega)
      by_cases hTotLe : (p.toNat - g.storage.toNat) / 16 ≤ 0xffff
      · simp only [hTotLe, ↓reduceIte] at hOld ⊢
        exact ⟨(hLtP0 _ (by omega)).trans hOld.1,
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨_, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
            exact hLtP0 a (by omega)).trans hOld.2⟩
      · simp only [hTotLe, ↓reduceIte] at hOld ⊢
        obtain ⟨_, _, _, hM4, hM2, hM8⟩ := hOld
        have _hPSub8 := bv64_sub_toNat (a := p) (n := 8) (by omega)
        exact ⟨(hLtP0 _ (by omega)).trans hM4,
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨_, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
            exact hLtP0 a (by omega)).trans hM2,
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            have ⟨_, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
            exact hLtP0 a (by omega)).trans hM8⟩
    intro bv hAg
    have _hPSub4 := bv64_sub_toNat (a := p) (n := 4) (by omega)
    have _hPSub2 := bv64_sub_toNat (a := p) (n := 2) (by omega)
    have hNe : ∀ a : BitVec 64, a.toNat ≠ (p - 3#64).toNat → a ≠ p - 3#64 :=
      fun _ hn he => hn (congrArg BitVec.toNat he)
    dsimp only [] at hHdrOffOld ⊢
    by_cases hTotLe : (p.toNat - g.storage.toNat) / 16 ≤ 0xffff
    · simp only [hTotLe, ↓reduceIte] at hHdrOffOld ⊢
      exact ⟨(hAg _ (by omega) (hNe _ (by omega))).trans hHdrOffOld.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hAg a (by omega) (hNe a (by omega))).trans hHdrOffOld.2⟩
    · simp only [hTotLe, ↓reduceIte] at hHdrOffOld ⊢
      have _hPSub8 := bv64_sub_toNat (a := p) (n := 8) (by omega)
      exact ⟨(hAg _ (by omega) (hNe _ (by omega))).trans hHdrOffOld.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hAg a (by omega) (hNe a (by omega))).trans hHdrOffOld.2.1,
        (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
          have ⟨_h1, _h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
          exact hAg a (by omega) (hNe a (by omega))).trans hHdrOffOld.2.2⟩
  let res' := (g.slotEnd idx).toNat - (p.toNat + len.toNat)
  have hSubs : (g.slotEnd idx - p).truncate 32 - len.truncate 32 = BitVec.ofNat 32 res' :=
    res_subs32_eq hFit hEn48
  have hPM3Band := subRegion_of_bounds hBand48 (ea := p - 3#64) (subLen := 1) (by omega) (by omega)
  wp_step; wp_step; wp_step
  wp_if hResEq0
  · have hRes0 : res' = 0 := by
      have hEq : (g.slotEnd idx - p).truncate 32 - len.truncate 32 = 0#32 := by
        rw [hResEq0, BitVec.sub_self]
      rw [hSubs] at hEq
      have ht := congrArg BitVec.toNat hEq
      simp only [BitVec.toNat_ofNat] at ht
      omega
    have hValIdx : (((BitVec.ofNat 32 idx).zeroExtend 64).truncate 8) =
        BitVec.ofNat 8 ((min res' 5 <<< 5) ||| idx) := by
      rw [hRes0, show (min 0 5 <<< 5) ||| idx = idx by simp]; bv_omega
    refine step_bm8 (pc := b + 0x2a0#64) (next_pc := b + 0x2a4#64)
      (ea := p - 3#64) (val := BitVec.ofNat 8 ((min res' 5 <<< 5) ||| idx)) hNodup
      (by simp [arm64_norm]) (by bv_arith)
      (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm, hx0])
      (by simp only [arm64_norm, hx2]; exact hValIdx)
      (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1) ?_
    intro m1 hm1 hkf1
    have hcl1 := hcl.of_keepsFrozen hkf1
    refine ldp19_20_to_epilogue (offLdp := 0x2a4) hb hprog (by wp_close_fetch_cl) (by wp_close_fetch_cl)
      (by bv_arith) rfl (by simp [arm64_norm, hrun]) hcl1
      (hm1.trans hperm) (by simp [arm64_norm, hbrk])
      (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
       by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
       by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
       by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩ ?_
    refine ⟨outBand_write hPM3Band hOut0, writeBytesToMap_self_one _ _ _,
      hHdrOffPres _ (fun a _ hNe => writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe)),
      fun _ => by omega, fun _ => by omega⟩
  · have hResPos : 1 ≤ res' := by
      refine Classical.byContradiction fun hNot => hResEq0 ?_
      have h0 : res' = 0 := by omega
      exact eq_of_sub32_eq_zero (by rw [hSubs, h0])
    have ⟨_hPLenLo, _hPLenHi⟩ :
        (p + len).toNat ≤ p.toNat + len.toNat ∧ p.toNat + len.toNat ≤ (p + len).toNat := by
      have h := BitVec.toNat_add p len
      rw [Nat.mod_eq_of_lt (by omega)] at h; exact ⟨by omega, by omega⟩
    have hPLenBand := subRegion_of_bounds hBand48 (ea := p + len) (subLen := 1) (by omega) (by omega)
    have hEaEnd : g.slotEnd idx + (0#32 - BitVec.ofNat 32 res').signExtend 64 = p + len :=
      slotEnd_add_sxtw_neg_res hFit hEn48 hResPos hRes31
    wp_step; wp_step
    refine step_bm8 (pc := b + 0x280#64) (next_pc := b + 0x284#64)
      (ea := p + len) (val := 0#8) hNodup
      (by simp [arm64_norm]) (by bv_arith)
      (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
      (by simp [arm64_norm])
      (by simp only [evalAddrMode, arm64_norm, hx3, Prod.mk.injEq, and_true]; exact hEaEnd)
      (by simp [arm64_norm])
      (fun a ha => (hInBand a (hPLenBand a ha)).2) (fun a ha => (hInBand a (hPLenBand a ha)).1) ?_
    intro m1 hm1 hkf1
    have hcl1 := hcl.of_keepsFrozen hkf1
    let bv1 := writeBytesToMap bv0 (p + len) [0#8]
    wp_step
    wp_if hLe4
    · have hResLe4 : res' ≤ 4 := by
        rwa [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4
      conv => arg 4; rw [byteMap_focus8 hNodup bv1 (p - 3#64)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv1 (p - 3#64)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1)]
      have hBv1M3 : bv1 (p - 3#64) = bv0 (p - 3#64) := by
        dsimp only [bv1]
        exact writeBytesToMap_out _ _ _ (fun hIn => by
          have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)
      have hPack := hdr3_pack_le4 (hBv1M3.symm ▸ hLowOld) hIdx31 hResPos hResLe4
      refine step_bm8 (pc := b + 0x2a0#64) (next_pc := b + 0x2a4#64)
        (ea := p - 3#64) (val := BitVec.ofNat 8 ((min res' 5 <<< 5) ||| idx)) hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx0])
        (by simp only [arm64_norm]; exact hPack)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1) ?_
      intro m2 hm2 hkf2
      have hcl2 := hcl1.of_keepsFrozen hkf2
      refine ldp19_20_to_epilogue (offLdp := 0x2a4) hb hprog (by wp_close_fetch_cl) (by wp_close_fetch_cl)
        (by bv_arith) rfl (by simp [arm64_norm, hrun]) hcl2
        (hm2.trans (hm1.trans hperm)) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
         by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩ ?_
      refine ⟨outBand_write hPM3Band (outBand_write hPLenBand hOut0),
        writeBytesToMap_self_one _ _ _,
        hHdrOffPres _ (fun a _haLt hNe => by
          dsimp only [bv1]
          rw [writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega)]),
        fun _ => by
          dsimp only [bv1]
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
            have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
        fun _ => by omega⟩
    · have hResGe5 : 5 ≤ res' := by
        rw [bv32_sle4_iff hRes31, decide_eq_true_eq] at hLe4; omega
      have ⟨_hEnM5Lo, _hEnM5Hi, _hEnM4Lo, _hEnM4Hi⟩ :
          (g.slotEnd idx - 5#64).toNat + 5 ≤ (g.slotEnd idx).toNat ∧
          (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 5#64).toNat + 5 ∧
          (g.slotEnd idx - 4#64).toNat + 4 ≤ (g.slotEnd idx).toNat ∧
          (g.slotEnd idx).toNat ≤ (g.slotEnd idx - 4#64).toNat + 4 := by
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 5) (by omega)
        have _ := bv64_sub_toNat (a := g.slotEnd idx) (n := 4) (by omega)
        exact ⟨by omega, by omega, by omega, by omega⟩
      have hEnM5Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 5#64) (subLen := 1) (by omega) (by omega)
      have hEnM4Band := subRegion_of_bounds hBand48 (ea := g.slotEnd idx - 4#64) (subLen := 4) (by omega) (by omega)
      refine step_bm8 (pc := b + 0x288#64) (next_pc := b + 0x28c#64)
        (ea := g.slotEnd idx - 5#64) (val := 0#8) hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx3])
        (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM5Band a ha)).2) (fun a ha => (hInBand a (hEnM5Band a ha)).1) ?_
      intro m2 hm2 hkf2
      have hcl2 := hcl1.of_keepsFrozen hkf2
      refine step_bm32 (pc := b + 0x28c#64) (next_pc := b + 0x290#64)
        (ea := g.slotEnd idx - 4#64) (val := BitVec.ofNat 32 res') hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx3])
        (by simp [arm64_norm])
        (fun a ha => (hInBand a (hEnM4Band a ha)).2) (fun a ha => (hInBand a (hEnM4Band a ha)).1) ?_
      intro m3 hm3 hkf3
      have hcl3 := hcl2.of_keepsFrozen hkf3
      let bv3 := writeBytesToMap (writeBytesToMap bv1 (g.slotEnd idx - 5#64) [0#8])
        (g.slotEnd idx - 4#64) (unpack32 (BitVec.ofNat 32 res'))
      conv => arg 4; rw [byteMap_focus8 hNodup bv3 (p - 3#64)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; rw [← byteMap_focus8 hNodup bv3 (p - 3#64)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1)]
      have hBv3M3 : bv3 (p - 3#64) = bv0 (p - 3#64) := by
        dsimp only [bv3, bv1]
        rw [writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega)]
      have hPack5 := hdr3_pack_ge5 (hBv3M3.symm ▸ hLowOld) hIdx31 hResGe5
      refine step_bm8 (pc := b + 0x2a0#64) (next_pc := b + 0x2a4#64)
        (ea := p - 3#64) (val := BitVec.ofNat 8 ((min res' 5 <<< 5) ||| idx)) hNodup
        (by simp [arm64_norm]) (by bv_arith)
        (by simp [arm64_norm, hrun]) (by wp_close_fetch_cl)
        (by simp [arm64_norm])
        (by simp only [evalAddrMode, arm64_norm, hx0])
        (by simp only [arm64_norm]; exact hPack5)
        (fun a ha => (hInBand a (hPM3Band a ha)).2) (fun a ha => (hInBand a (hPM3Band a ha)).1) ?_
      intro m4 hm4 hkf4
      have hcl4 := hcl3.of_keepsFrozen hkf4
      refine ldp19_20_to_epilogue (offLdp := 0x2a4) hb hprog (by wp_close_fetch_cl) (by wp_close_fetch_cl)
        (by bv_arith) rfl (by simp [arm64_norm, hrun]) hcl4
        (hm4.trans (hm3.trans (hm2.trans (hm1.trans hperm)))) (by simp [arm64_norm, hbrk])
        (alignedProcPreserved_trans hproc ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
        (by simp [arm64_norm, hsp]) hsp0 hspAl0 (by simp [arm64_norm, hx0])
        ⟨by simp [arm64_norm, hcs21_28.1], by simp [arm64_norm, hcs21_28.2.1],
         by simp [arm64_norm, hcs21_28.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.1],
         by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.1], by simp [arm64_norm, hcs21_28.2.2.2.2.2.2.2.1],
         by simp [calleeSavedVRegs, hcs21_28.2.2.2.2.2.2.2.2]⟩ ?_
      refine ⟨outBand_write hPM3Band (outBand_write hEnM4Band (outBand_write hEnM5Band (outBand_write hPLenBand hOut0))),
        writeBytesToMap_self_one _ _ _,
        hHdrOffPres _ (fun a _haLt hNe => by
          dsimp only [bv3, bv1]
          rw [writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hNe),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega),
            writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega)]),
        fun _ => by
          dsimp only [bv3, bv1]
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          by_cases hEq5 : p + len = g.slotEnd idx - 5#64
          · rw [hEq5]; exact writeBytesToMap_self_one _ _ _
          · rw [writeBytesToMap_out _ _ _ (not_inRegion_one_of_ne (by omega) hEq5)]
            exact writeBytesToMap_self_one _ _ _,
        fun _ => ⟨by
          dsimp only [bv3, bv1]
          rw [writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) _).mp hIn; omega),
              writeBytesToMap_out _ _ _ (fun hIn => by
                have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) _).mp hIn; omega)]
          exact writeBytesToMap_self_one _ _ _,
          (readBytesFromMap_eq_of_inRegion (by decide) fun a ha => by
            dsimp only [bv3, bv1]
            have ⟨_h1, _⟩ := (inRegion_iff_toNat (n := 4) (by omega) a).mp ha
            exact writeBytesToMap_out _ _ _ (fun hIn => by
              have ⟨_, _h2⟩ := (inRegion_iff_toNat (n := 1) (by omega) a).mp hIn; omega)).trans
            (readBytesFromMap_writeBytesToMap _ _ (unpack32 (BitVec.ofNat 32 res')) (by simp))⟩⟩

end VerifiedLibraries.Mallocng.Proofs
