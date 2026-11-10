/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers3
public import VerifiedLibraries.Mallocng.Proofs.PlacedLeavesRuntimeProof
import ProofLib.Invariant

/-!
# Slot-Byte Enframing and `__libc_malloc_impl` Store Helpers

Slot-byte transformations (`enframeB1`, `enframeB2`, `enframeB3`, `enframe_slotBytes_props`),
`getStride_props`, `ByteMap` slice extractions (`meta_and_slot_extract`, `slot_extract`),
`enframe_bv_props`, `perm`- and `CodeLoaded`-preserving store tactics, lock/unlock leaf contracts,
and `mallocImplSuccessPost24`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib SepLogic

/-! ## Slot-byte enframing -/

def enframeB1 (slotBs : List (BitVec 8)) (off : Nat) : List (BitVec 8) :=
  if off = 0 then slotBs
  else ByteSlice.write8 (ByteSlice.write16 (ByteSlice.write8 slotBs 1 0xe0#8) 2 (BitVec.ofNat 16 off)) (16 * off) 0#8

def enframeB2 (bs1 : List (BitVec 8)) (off idx totOff16 : Nat) : List (BitVec 8) :=
  ByteSlice.write16 (ByteSlice.write8 bs1 (16 * off + 1) (BitVec.ofNat 8 idx)) (16 * off + 2) (BitVec.ofNat 16 totOff16)

def enframeB3 (bs2 : List (BitVec 8)) (off req stride res : Nat) : List (BitVec 8) :=
  if res = 0 then bs2
  else if res ≤ 4 then ByteSlice.write8 bs2 (4 + 16 * off + req) 0#8
  else ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8 bs2 (4 + 16 * off + req) 0#8) (stride - 5) 0#8)
    (stride - 4) (BitVec.ofNat 32 res)

private theorem enframeB1_props (slotBs : List (BitVec 8)) (off stride : Nat)
    (hLen : slotBs.length = stride) (hFit : 16 * off + 4 ≤ stride) (h0 : slotBs.getD 0 0#8 = 0#8) :
    (enframeB1 slotBs off).length = stride ∧
    (enframeB1 slotBs off).getD 0 0#8 = 0#8 ∧
    (enframeB1 slotBs off).getD (16 * off) 0#8 = 0#8 ∧
    (∀ k, 4 + 16 * off ≤ k → (enframeB1 slotBs off).getD k 0#8 = slotBs.getD k 0#8) := by
  unfold enframeB1; split
  · rename_i hZ; subst hZ; exact ⟨hLen, h0, h0, fun _ _ => rfl⟩
  · rename_i hNe
    have hL1 : (ByteSlice.write8 slotBs 1 0xe0#8).length = stride := by rw [ByteSlice.write8_length _ _ _ (by omega), hLen]
    have hL2 : (ByteSlice.write16 (ByteSlice.write8 slotBs 1 0xe0#8) 2 (BitVec.ofNat 16 off)).length = stride := by
      rw [ByteSlice.write16_length _ _ _ (by omega), hL1]
    refine ⟨by rw [ByteSlice.write8_length _ _ _ (by omega), hL2], ?_, ?_, ?_⟩
    · rw [ByteSlice.getD_write8 _ _ _ 0 0#8 (by omega), ite_eq_right (by omega),
          ByteSlice.getD_write16 _ _ _ 0 0#8 (by omega), ite_eq_right (by omega),
          ByteSlice.getD_write8 _ _ _ 0 0#8 (by omega), ite_eq_right (by omega), h0]
    · rw [ByteSlice.getD_write8 _ _ _ (16 * off) 0#8 (by omega), ite_eq_left rfl]
    · intro k hk
      rw [ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega),
          ByteSlice.getD_write16 _ _ _ k 0#8 (by omega), ite_eq_right (by omega),
          ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega)]

private theorem enframeB2_props (bs1 : List (BitVec 8)) (off idx totOff16 stride : Nat)
    (hLen : bs1.length = stride) (hFit : 16 * off + 4 ≤ stride) :
    let bs2 := enframeB2 bs1 off idx totOff16
    bs2.length = stride ∧
    bs2.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 idx ∧
    bs2.getD (16 * off + 2) 0#8 = (BitVec.ofNat 16 totOff16).extractLsb' 0 8 ∧
    bs2.getD (16 * off + 3) 0#8 = (BitVec.ofNat 16 totOff16).extractLsb' 8 8 ∧
    (∀ k, (k ≤ 16 * off ∨ 4 + 16 * off ≤ k) → bs2.getD k 0#8 = bs1.getD k 0#8) := by
  dsimp only [enframeB2]
  have hL1 : (ByteSlice.write8 bs1 (16 * off + 1) (BitVec.ofNat 8 idx)).length = stride := by
    rw [ByteSlice.write8_length _ _ _ (by omega), hLen]
  refine ⟨by rw [ByteSlice.write16_length _ _ _ (by omega), hL1], ?_, ?_, ?_, ?_⟩
  · rw [ByteSlice.getD_write16 _ _ _ _ 0#8 (by omega), ite_eq_right (by omega),
        ByteSlice.getD_write8 _ _ _ _ 0#8 (by omega), ite_eq_left rfl]
  · rw [ByteSlice.getD_write16 _ _ _ _ 0#8 (by omega), ite_eq_left (by omega)]; congr 2; omega
  · rw [ByteSlice.getD_write16 _ _ _ _ 0#8 (by omega), ite_eq_left (by omega)]; congr 2; omega
  · intro k hk
    rw [ByteSlice.getD_write16 _ _ _ k 0#8 (by omega), ite_eq_right (by omega),
        ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega)]

private theorem enframeB3_props (bs2 : List (BitVec 8)) (off req stride res : Nat)
    (hLen : bs2.length = stride) (hRes : 4 + 16 * off + req + res = stride) :
    let bs3 := enframeB3 bs2 off req stride res
    bs3.length = stride ∧
    (∀ k, k < 4 + 16 * off + req → bs3.getD k 0#8 = bs2.getD k 0#8) ∧
    (1 ≤ res → bs3.getD (4 + 16 * off + req) 0#8 = 0#8) ∧
    (5 ≤ res → bs3.getD (stride - 5) 0#8 = 0#8 ∧
      ∀ j, j < 4 → bs3.getD (stride - 4 + j) 0#8 = (BitVec.ofNat 32 res).extractLsb' (8 * j) 8) := by
  dsimp only [enframeB3]; split
  · exact ⟨hLen, fun _ _ => rfl, fun h => by omega, fun h => by omega⟩
  · split
    · refine ⟨by rw [ByteSlice.write8_length _ _ _ (by omega), hLen],
        fun k hk => by rw [ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega)],
        fun _ => by rw [ByteSlice.getD_write8 _ _ _ _ 0#8 (by omega), ite_eq_left rfl],
        fun h => by omega⟩
    · have hL1 : (ByteSlice.write8 bs2 (4 + 16 * off + req) 0#8).length = stride := by
        rw [ByteSlice.write8_length _ _ _ (by omega), hLen]
      have hL2 : (ByteSlice.write8 (ByteSlice.write8 bs2 (4 + 16 * off + req) 0#8) (stride - 5) 0#8).length = stride := by
        rw [ByteSlice.write8_length _ _ _ (by omega), hL1]
      refine ⟨by rw [ByteSlice.write32_length _ _ _ (by omega), hL2], ?_, ?_, ?_⟩
      · intro k hk
        rw [ByteSlice.getD_write32 _ _ _ k 0#8 (by omega), ite_eq_right (by omega),
            ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega),
            ByteSlice.getD_write8 _ _ _ k 0#8 (by omega), ite_eq_right (by omega)]
      · intro _
        rw [ByteSlice.getD_write32 _ _ _ _ 0#8 (by omega), ite_eq_right (by omega),
            ByteSlice.getD_write8 _ _ _ _ 0#8 (by omega)]
        split
        · rfl
        · rw [ByteSlice.getD_write8 _ _ _ _ 0#8 (by omega), ite_eq_left rfl]
      · intro _
        refine ⟨by rw [ByteSlice.getD_write32 _ _ _ _ 0#8 (by omega), ite_eq_right (by omega),
                       ByteSlice.getD_write8 _ _ _ _ 0#8 (by omega), ite_eq_left rfl], ?_⟩
        intro j hj
        rw [ByteSlice.getD_write32 _ _ _ _ 0#8 (by omega), ite_eq_left (by omega)]
        congr 2; omega

theorem enframe_slotBytes_props {st1 : MallocngSt} {g : GroupDesc} {idx req off : Nat}
    (hgw : GroupWf st1 g) (hIdx : idx < g.slots.length) (_hClaimed : g.slots[idx]'hIdx = .claimed)
    (_hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8) :
    let start := g.slotStart idx
    let p := start + BitVec.ofNat 64 (16 * off)
    let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
    let totOff16 := (p.toNat - g.storage.toNat) / 16
    let res := (g.slotEnd idx).toNat - (p.toNat + req)
    let bs1 := enframeB1 slotBs off
    let bs2 := enframeB2 bs1 off idx totOff16
    let bs3 := enframeB3 bs2 off req g.stride res
    let newSlotBytes := ByteSlice.write8 bs3 (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
    let val' := writeBytesToMap st1.byteVal (start - 4#64) newSlotBytes
    bs1.length = g.stride ∧
    bs2.length = g.stride ∧
    bs3.length = g.stride ∧
    newSlotBytes.length = g.stride ∧
    bs3.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 idx ∧
    val' (start - 4#64) = 0#8 ∧
    val' (p - 4#64) = 0#8 ∧
    val' (p - 3#64) = BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx) ∧
    readBytesFromMap val' (p - 2#64) 2 = unpack16 (BitVec.ofNat 16 totOff16) ∧
    (1 ≤ res → val' (p + BitVec.ofNat 64 req) = 0#8) ∧
    (5 ≤ res → val' (g.slotEnd idx - 5#64) = 0#8 ∧
      readBytesFromMap val' (g.slotEnd idx - 4#64) 4 = unpack32 (BitVec.ofNat 32 res)) ∧
    (g.isMmapped = true → readBytesFromMap val' p req = List.replicate req 0#8) := by
  intro start p slotBs totOff16 res bs1 bs2 bs3 newSlotBytes val'
  obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
  obtain ⟨_, _, hStartNat, hSub4Nat, hEndNat, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hStartEq : start.toNat = g.mem.toNat + 16 + idx * g.stride := hStartNat
  have hSub4Eq : (start - 4#64).toNat = g.mem.toNat + 12 + idx * g.stride := hSub4Nat
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hPNat : p.toNat = start.toNat + 16 * off := bv64_add_toNat (by omega)
  have hResSum : 4 + 16 * off + req + res = g.stride := by dsimp only [res]; omega
  have hSlotLen : slotBs.length = g.stride := readBytesFromMap_length _ _ _
  have hSlot0 : slotBs.getD 0 0#8 = 0#8 := by
    have h0 : 0 < g.stride := by omega
    have hG := readBytesFromMap_getElem st1.byteVal (start - 4#64) g.stride 0
      (by rw [readBytesFromMap_length]; exact h0)
    have hSw : st1.byteVal (start - 4#64) = 0#8 :=
      (hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx).1
    simpa [slotBs, List.getD_eq_getElem?_getD, hSlotLen, h0] using hG.trans (by simpa using hSw)
  obtain ⟨hBs1Len, hBs1_0, hBs1_off, hBs1_hi⟩ := enframeB1_props slotBs off g.stride hSlotLen (by omega) hSlot0
  obtain ⟨hBs2Len, hBs2_1, hBs2_2, hBs2_3, hBs2_out⟩ := enframeB2_props bs1 off idx totOff16 g.stride hBs1Len (by omega)
  obtain ⟨hBs3Len, hBs3_lo, hBs3_r1, hBs3_r5⟩ := enframeB3_props bs2 off req g.stride res hBs2Len hResSum
  have hBs3Len' : bs3.length = g.stride := hBs3Len
  have hNewLen : newSlotBytes.length = g.stride := by
    dsimp only [newSlotBytes]; rw [ByteSlice.write8_length _ _ _ (by omega), hBs3Len']
  have hNewAt : ∀ k, newSlotBytes.getD k 0#8 =
      if k = 16 * off + 1 then BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx) else bs3.getD k 0#8 := fun k =>
    ByteSlice.getD_write8 bs3 (16 * off + 1) _ k 0#8 (by omega)
  have hValAt : ∀ k < g.stride, val' ((start - 4#64) + BitVec.ofNat 64 k) = newSlotBytes.getD k 0#8 := by
    intro k hk; have hk' : k < newSlotBytes.length := hNewLen ▸ hk
    simpa [val', List.getD_eq_getElem?_getD, hk'] using
      writeBytesToMap_in st1.byteVal (start - 4#64) newSlotBytes hk' (by omega)
  have hPAddr (m : Nat) : p + BitVec.ofNat 64 m = (start - 4#64) + BitVec.ofNat 64 (4 + 16 * off + m) := by
    dsimp only [p]; simp only [BitVec.ofNat_add]; bv_lin
  refine ⟨hBs1Len, hBs2Len, hBs3Len, hNewLen, (hBs3_lo _ (by omega)).trans hBs2_1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show start - 4#64 = (start - 4#64) + BitVec.ofNat 64 0 by bv_lin, hValAt 0 (by omega),
        hNewAt 0, ite_eq_right (by omega), hBs3_lo 0 (by omega), hBs2_out 0 (by omega), hBs1_0]
  · rw [show p - 4#64 = (start - 4#64) + BitVec.ofNat 64 (16 * off) by dsimp only [p]; bv_lin,
        hValAt (16 * off) (by omega), hNewAt (16 * off), ite_eq_right (by omega),
        hBs3_lo (16 * off) (by omega), hBs2_out (16 * off) (by omega), hBs1_off]
  · rw [show p - 3#64 = (start - 4#64) + BitVec.ofNat 64 (16 * off + 1) by
          dsimp only [p]; simp only [BitVec.ofNat_add]; bv_lin,
        hValAt (16 * off + 1) (by omega), hNewAt (16 * off + 1), ite_eq_left rfl]
  · simp only [readBytesFromMap_succ, readBytesFromMap_zero, unpack16, List.cons.injEq, and_true]
    exact ⟨by rw [show p - 2#64 = (start - 4#64) + BitVec.ofNat 64 (16 * off + 2) by
                    dsimp only [p]; simp only [BitVec.ofNat_add]; bv_lin,
                  hValAt (16 * off + 2) (by omega), hNewAt (16 * off + 2), ite_eq_right (by omega),
                  hBs3_lo _ (by omega), hBs2_2],
           by rw [show p - 2#64 + 1#64 = (start - 4#64) + BitVec.ofNat 64 (16 * off + 3) by
                    dsimp only [p]; simp only [BitVec.ofNat_add]; bv_lin,
                  hValAt (16 * off + 3) (by omega), hNewAt (16 * off + 3), ite_eq_right (by omega),
                  hBs3_lo _ (by omega), hBs2_3]⟩
  · intro hRes1
    rw [hPAddr req, hValAt (4 + 16 * off + req) (by omega),
        hNewAt (4 + 16 * off + req), ite_eq_right (by omega), hBs3_r1 hRes1]
  · intro hRes5
    obtain ⟨hR5_5, hR5_4⟩ := hBs3_r5 hRes5
    refine ⟨?_, ?_⟩
    · have hE5 : g.slotEnd idx - 5#64 = (start - 4#64) + BitVec.ofNat 64 (g.stride - 5) := by
        dsimp only [GroupDesc.slotEnd]; rw [show g.stride - 4 = (g.stride - 5) + 1 by omega]
        simp only [BitVec.ofNat_add]; dsimp only [start]; bv_lin
      rw [hE5, hValAt (g.stride - 5) (by omega), hNewAt (g.stride - 5), ite_eq_right (by omega), hR5_5]
    · have hAj (j : Nat) (hj : j < 4) : val' ((start - 4#64) + BitVec.ofNat 64 (g.stride - 4 + j)) =
          (BitVec.ofNat 32 res).extractLsb' (8 * j) 8 := by
        rw [hValAt (g.stride - 4 + j) (by omega), hNewAt (g.stride - 4 + j), ite_eq_right (by omega), hR5_4 j hj]
      simp only [readBytesFromMap_succ, readBytesFromMap_zero, unpack32, List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show g.slotEnd idx - 4#64 = (start - 4#64) + BitVec.ofNat 64 (g.stride - 4 + 0) by
              dsimp only [GroupDesc.slotEnd, start]; simp only [BitVec.ofNat_add]; bv_lin]; exact hAj 0 (by omega)
      · rw [show g.slotEnd idx - 4#64 + 1#64 = (start - 4#64) + BitVec.ofNat 64 (g.stride - 4 + 1) by
              dsimp only [GroupDesc.slotEnd, start]; simp only [BitVec.ofNat_add]; bv_lin]; exact hAj 1 (by omega)
      · rw [show g.slotEnd idx - 4#64 + 1#64 + 1#64 = (start - 4#64) + BitVec.ofNat 64 (g.stride - 4 + 2) by
              dsimp only [GroupDesc.slotEnd, start]; simp only [BitVec.ofNat_add]; bv_lin]; exact hAj 2 (by omega)
      · rw [show g.slotEnd idx - 4#64 + 1#64 + 1#64 + 1#64 = (start - 4#64) + BitVec.ofNat 64 (g.stride - 4 + 3) by
              dsimp only [GroupDesc.slotEnd, start]; simp only [BitVec.ofNat_add]; bv_lin]; exact hAj 3 (by omega)
  · intro hMm
    apply List.ext_getElem (by rw [readBytesFromMap_length, List.length_replicate])
    intro j hj1 _
    have hj : j < req := by simpa using hj1
    rw [readBytesFromMap_getElem _ _ _ j (by rw [readBytesFromMap_length]; exact hj), List.getElem_replicate, hPAddr j,
        hValAt (4 + 16 * off + j) (by omega), hNewAt (4 + 16 * off + j), ite_eq_right (by omega),
        hBs3_lo (4 + 16 * off + j) (by omega), hBs2_out (4 + 16 * off + j) (by omega),
        hBs1_hi (4 + 16 * off + j) (by omega)]
    have hkStr : 4 + 16 * off + j < g.stride := by omega
    have hG := readBytesFromMap_getElem st1.byteVal (start - 4#64) g.stride (4 + 16 * off + j)
      (by rw [readBytesFromMap_length]; exact hkStr)
    have hAddrEq : (start - 4#64) + BitVec.ofNat 64 (4 + 16 * off + j) = start + BitVec.ofNat 64 (16 * off + j) := by
      simp only [BitVec.ofNat_add]; bv_lin
    have hInStart : InRegion start g.stride (start + BitVec.ofNat 64 (16 * off + j)) := by
      rw [inRegion_iff_toNat (by omega), bv64_add_toNat (by omega)]; omega
    simpa [slotBs, List.getD_eq_getElem?_getD, hSlotLen, hkStr, hAddrEq] using hG.trans (hAddrEq ▸ hZeroMm hMm _ hInStart)

/-! ## `get_stride`, `enframe_bv_props`, and `ByteMap` slice extractions -/

private theorem sizeClass_le_8191 {sc : Nat} (h : sc < 48) : sizeClass sc ≤ 8191 := by
  have hAll : (List.range 48).all (fun s => decide (sizeClass s ≤ 8191)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hAll sc (List.mem_range.mpr h))

theorem getStride_props {st1 : MallocngSt} {g : GroupDesc} (hgw : GroupWf st1 g) :
    let b32 := g.metaBytes.getD 32 0#8
    let h32 := pack16 (g.metaBytes.getD 32 0#8) (g.metaBytes.getD 33 0#8)
    (((b32.zeroExtend 32).zeroExtend 64 &&& 0x1f#64) == 0#64) = decide (g.lastIdx = 0) ∧
    (g.lastIdx = 0 →
      0 < g.maplen ∧
      ((g.packedWord &&& 0xfffffffffffff000#64) == 0#64) = false ∧
      (g.packedWord &&& 0xfffffffffffff000#64) - 0x10#64 = BitVec.ofNat 64 g.stride) ∧
    (g.lastIdx ≠ 0 →
      g.sc < 48 ∧
      (((h32.zeroExtend 32).zeroExtend 64 >>> 6) &&& 0x3f#64) = BitVec.ofNat 64 g.sc ∧
      (BitVec.ofNat 64 g.sc <<< 1) = BitVec.ofNat 64 (2 * g.sc) ∧
      (((BitVec.ofNat 16 (sizeClass g.sc)).zeroExtend 32).zeroExtend 64 &&& 0xffff#64) <<< 4 =
        BitVec.ofNat 64 g.stride) := by
  obtain ⟨_, _, _, hB32, hH32, _, _⟩ := metaBytes_ops g 0 0#32 .claimed
  have hLast31 : g.lastIdx ≤ 31 := hgw.2.1
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hTotLe : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hgw.2.2.2.2.2.2.1
  dsimp only; rw [hH32, hB32]
  refine ⟨?_, ?_, ?_⟩
  · have hEq : ((g.packedWord.extractLsb' 0 8).zeroExtend 32).zeroExtend 64 &&& 0x1f#64 =
        BitVec.ofNat 64 g.lastIdx := by
      rw [show ((g.packedWord.extractLsb' 0 8).zeroExtend 32).zeroExtend 64 &&& 0x1f#64 =
          BitVec.ofNat 64 g.lastIdx &&& 0x1f#64 by unfold GroupDesc.packedWord; bv_bits]
      have hAll : (List.range 32).all (fun k => decide (BitVec.ofNat 64 k &&& 0x1f#64 = BitVec.ofNat 64 k)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.mp hAll g.lastIdx (List.mem_range.mpr (by omega)))
    rw [hEq]
    by_cases h0 : g.lastIdx = 0
    · rw [h0]; rfl
    · simp only [h0, decide_false, beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt (by omega : g.lastIdx < 2 ^ 64)] at this; omega
  · intro hZ
    have hMapPos : 0 < g.maplen :=
      Decidable.byContradiction fun hNP => by
        have hM0 : g.maplen = 0 := by omega
        have h1 := (hgw.2.2.2.2.2.2.2.2.2.2.2.2.1 hM0).1; omega
    have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMapPos]
    have hMap48 : g.maplen * 4096 ≤ 2 ^ 48 := by omega
    have hMask : g.packedWord &&& 0xfffffffffffff000#64 = BitVec.ofNat 64 (g.maplen * 4096) := by
      rw [show g.packedWord &&& 0xfffffffffffff000#64 = BitVec.ofNat 64 g.maplen <<< 12 by
        unfold GroupDesc.packedWord; bv_bits]
      exact BitVec.eq_of_toNat_eq (by simp [Nat.shiftLeft_eq])
    have hStrEq : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hZ, hMapPos]
    clear hgw; rw [hMask, hStrEq]
    refine ⟨hMapPos, beq_eq_false_iff_ne.mpr fun h => ?_, by bv_omega⟩
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt (by omega : g.maplen * 4096 < 2 ^ 64)] at this; omega
  · intro hNZ
    have hSc48 : g.sc < 48 := hgw.1.elim id (fun h63 => False.elim (hNZ (hgw.2.2.2.1 h63).1))
    have hStrEq : g.stride = 16 * sizeClass g.sc := by simp [GroupDesc.stride, hNZ, slotStride]
    have hScValLt : sizeClass g.sc ≤ 8191 := sizeClass_le_8191 hSc48
    clear hgw
    refine ⟨hSc48, ?_, by bv_omega, ?_⟩
    · rw [show (((g.packedWord.truncate 16).zeroExtend 32).zeroExtend 64 >>> 6) &&& 0x3f#64 =
          BitVec.ofNat 64 g.sc &&& 0x3f#64 by unfold GroupDesc.packedWord; bv_bits]
      have hAll : (List.range 48).all (fun k => decide (BitVec.ofNat 64 k &&& 0x3f#64 = BitVec.ofNat 64 k)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.mp hAll g.sc (List.mem_range.mpr hSc48))
    · rw [hStrEq]
      have h1 : (((BitVec.ofNat 16 (sizeClass g.sc)).zeroExtend 32).zeroExtend 64 &&& 0xffff#64) =
          (BitVec.ofNat 16 (sizeClass g.sc)).zeroExtend 64 := by bv_bits
      rw [h1]; bv_omega

theorem meta_and_slot_extract {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st1 : MallocngSt} (hwf1 : MallocngWFInflight 1 base brkStart brk liveCost peakCost st1)
    (hNoRes : st1.reservedMetas = []) {g : GroupDesc} (hg : g ∈ st1.groups)
    {idx : Nat} (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed) :
    let start := g.slotStart idx
    ByteMap st1.masterDom (fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) st1.byteVal =
      ((g.metaPtr ↦ₛ g.metaBytes) ∗
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧
          ¬ InRegion g.metaPtr 40 a) st1.byteVal) := by
  intro start
  obtain ⟨hMetaOwn, hSlotOwn⟩ := group_meta_and_claimed_ownedRw hwf1 hNoRes hg
  have hNN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hClaimed]; intro _ h; cases h
  have hNU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c := by rw [hClaimed]; intro _ _ _ h; cases h
  have hMetaBytes : readBytesFromMap st1.byteVal g.metaPtr 40 = g.metaBytes :=
    (hwf1.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hExt := ByteMap_extract_slice hwf1.masterDom_wf.1
    (keep := fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a)
    st1.byteVal g.metaPtr (n := 40) (by omega)
    (fun a ha => (hMetaOwn a ha).2)
    (fun a ha => ⟨(hMetaOwn a ha).1, fun hInS => (hSlotOwn idx hIdx hNN hNU a hInS).2.2 ha⟩)
  rwa [hMetaBytes] at hExt

theorem slot_extract {base brkStart brk : BitVec 64} {liveCost peakCost : Nat}
    {st1 : MallocngSt} (hwf1 : MallocngWFInflight 1 base brkStart brk liveCost peakCost st1)
    (hNoRes : st1.reservedMetas = []) {g : GroupDesc} (hg : g ∈ st1.groups)
    {idx : Nat} (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed) :
    let start := g.slotStart idx
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal =
      (((start - 4#64) ↦ₛ readBytesFromMap st1.byteVal (start - 4#64) g.stride) ∗
        ByteMap st1.masterDom (fun a => OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) st1.byteVal) := by
  intro start
  have hgw := hwf1.groups_wf g hg
  obtain ⟨_, hSlotOwn⟩ := group_meta_and_claimed_ownedRw hwf1 hNoRes hg
  obtain ⟨hIdxCnt, _, _, _, _, _, _, _, _⟩ := group_slot_bounds hgw hIdx
  have hNN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hClaimed]; intro _ h; cases h
  have hNU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c := by rw [hClaimed]; intro _ _ _ h; cases h
  have hStrLe : g.stride ≤ 2 ^ 64 := by
    have : 1 * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ (by omega)
    have := hgw.2.2.2.2.2.2.2.1; omega
  exact ByteMap_extract_slice hwf1.masterDom_wf.1 (keep := OwnedRwByte st1) st1.byteVal (start - 4#64)
    (n := g.stride) hStrLe
    (fun a ha => (hSlotOwn idx hIdx hNN hNU a ha).2.1)
    (fun a ha => (hSlotOwn idx hIdx hNN hNU a ha).1)

private theorem r5_add_idx_eq_or {r idx : Nat} (hr : r ≤ 5) (hi : idx < 32) :
    (r <<< 5) + idx = ((r <<< 5) ||| idx) := by
  have hAll : (List.range 6).all (fun x => (List.range 32).all (fun y =>
      decide ((x <<< 5) + y = ((x <<< 5) ||| y)))) = true := by decide
  have h1 := List.all_eq_true.mp hAll r (List.mem_range.mpr (by omega))
  exact of_decide_eq_true (List.all_eq_true.mp h1 idx (List.mem_range.mpr hi))

theorem enframe_bv_props {st1 : MallocngSt} {g : GroupDesc} {idx req : Nat}
    (hgw : GroupWf st1 g) (hIdx : idx < g.slots.length) (hFit0 : req + 4 ≤ g.stride)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195) :
    let str64 := BitVec.ofNat 64 g.stride
    let req64 := BitVec.ofNat 64 req
    let idx64 := BitVec.ofNat 64 idx
    let idx32 := BitVec.ofNat 32 idx
    let start := g.slotStart idx
    g.stride - 4 - req < 1048576 ∧
    (str64 - req64) - 4#64 = BitVec.ofNat 64 (g.stride - 4 - req) ∧
    str64 - 4#64 = BitVec.ofNat 64 (g.stride - 4) ∧
    (BitVec.ofNat 64 (g.stride - 4 - req)) >>> 4 = BitVec.ofNat 64 ((g.stride - 4 - req) / 16) ∧
    g.storage + str64 * idx64 = start ∧
    (∀ w1 : BitVec 32, w1 &&& 255#32 = w1 →
      (BitVec.ofNat 64 ((g.stride - 4 - req) / 16)).ult (w1.signExtend 64) = false →
      w1.toNat ≤ 255 ∧ 16 * w1.toNat + req ≤ g.stride - 4 ∧ w1 = BitVec.ofNat 32 w1.toNat) ∧
    (∀ off : Nat, off ≤ 255 → 16 * off + req ≤ g.stride - 4 →
      let p := start + BitVec.ofNat 64 (16 * off)
      let totOff16 := (p.toNat - g.storage.toNat) / 16
      let res := (g.slotEnd idx).toNat - (p.toNat + req)
      ((BitVec.ofNat 32 off <<< 4).signExtend 64) = BitVec.ofNat 64 (16 * off) ∧
      (0xffffffe0#32).truncate 8 = 0xe0#8 ∧
      (p - g.storage) >>> 4 = BitVec.ofNat 64 totOff16 ∧
      (idx32 &&& 0xff#32) = idx32 ∧
      (idx32 &&& 0x1f#32) = idx32 ∧
      idx32.truncate 8 = BitVec.ofNat 8 idx ∧
      ((g.slotEnd idx - p).truncate 32) - req64.truncate 32 = BitVec.ofNat 32 res ∧
      (((g.slotEnd idx - p).truncate 32 - req64.truncate 32) == 0#32) = decide (res = 0) ∧
      (res ≠ 0 → g.slotEnd idx + (0#32 - BitVec.ofNat 32 res).signExtend 64 =
        (start - 4#64) + BitVec.ofNat 64 (4 + 16 * off + req)) ∧
      (res ≠ 0 → BitVec.sle (BitVec.ofNat 32 res) 4#32 = decide (res ≤ 4)) ∧
      (res ≤ 4 → ((BitVec.ofNat 32 res &&& 7#32) <<< 5) = BitVec.ofNat 32 (min res 5 <<< 5)) ∧
      (5 ≤ res → 0xa0#32 = BitVec.ofNat 32 (min res 5 <<< 5)) ∧
      (BitVec.ofNat 32 (min res 5 <<< 5) + idx32).truncate 8 = BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx)) := by
  obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
  obtain ⟨hIdxCnt, hStorNat, hStartNat, _, hEndNat, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hLast31 : g.lastIdx ≤ 31 := hgw.2.1
  have hIdx32 : idx < 32 := by dsimp [GroupDesc.cnt] at hIdxCnt; omega
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hStrLt : g.stride < 2 ^ 48 := by
    have : 1 * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ (by omega)
    have := hgw.2.2.2.2.2.2.2.1; omega
  have hSlackLt : g.stride - 4 - req < 1048576 := by
    rcases hgw.1 with hSc48 | h63
    · by_cases hZ : (g.lastIdx == 0 && 0 < g.maplen) = true
      · have hZ' : g.lastIdx = 0 ∧ 0 < g.maplen := by simpa using hZ
        have hM := ((hgw.2.2.2.2.2.2.2.2.2.2.2.1 hZ'.2).2.2.2 hSc48).1
        have hS : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hZ'.1, hZ'.2]
        omega
      · have hZFalse : (g.lastIdx == 0 && decide (0 < g.maplen)) = false := by
          cases hB : (g.lastIdx == 0 && decide (0 < g.maplen)) <;> simp_all
        have hS : g.stride = 16 * sizeClass g.sc := by
          unfold GroupDesc.stride; rw [ite_eq_right (by simp [hZFalse])]; rfl
        have := sizeClass_le_8191 hSc48; omega
    · obtain ⟨hZ, hMP, _, _⟩ := hgw.2.2.2.1 h63
      have hS : g.stride = g.maplen * 4096 - 16 := by simp [GroupDesc.stride, hZ, hMP]
      have h63B := hSc63 h63
      change g.maplen * 4096 ≤ max req 65536 + 8195 at h63B
      omega
  clear hgw hSc63
  dsimp only
  refine ⟨hSlackLt, by bv_omega, by bv_omega, by bv_omega, ?_, ?_, ?_⟩
  · dsimp only [GroupDesc.slotStart]
    rw [show BitVec.ofNat 64 g.stride * BitVec.ofNat 64 idx = BitVec.ofNat 64 (idx * g.stride) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mul_comm]]
  · intro w1 hw1 hUlt
    have hw1Eq : w1 = (w1.truncate 8).zeroExtend 32 := by revert hw1; bv_bits
    have hw1_255 : w1.toNat ≤ 255 := by
      have : w1.toNat = w1.toNat % 256 := congrArg BitVec.toNat hw1Eq
      omega
    have hSNat : (w1.signExtend 64).toNat = w1.toNat := by
      have hS : w1.signExtend 64 = (w1.truncate 8).zeroExtend 64 := by rw [hw1Eq]; bv_bits
      rw [hS]; simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : w1.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : w1.toNat < 2 ^ 8)]
    have hLe : w1.toNat ≤ (g.stride - 4 - req) / 16 := by
      simp only [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : (g.stride - 4 - req) / 16 < 2 ^ 64), hSNat] at hUlt
      omega
    exact ⟨hw1_255, by omega, by simp⟩
  · intro off hOff255 hFit
    generalize hp : g.slotStart idx + BitVec.ofNat 64 (16 * off) = p
    generalize hRes : (g.slotEnd idx).toNat - (p.toNat + req) = res
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hPNat : p.toNat = (g.slotStart idx).toNat + 16 * off := by rw [← hp]; exact bv64_add_toNat (by omega)
    have hResSum : 4 + 16 * off + req + res = g.stride := by omega
    have hResLt : res < 1048576 := by omega
    have hPS : p - g.storage = BitVec.ofNat 64 (p.toNat - g.storage.toNat) := by
      rw [show p.toNat - g.storage.toNat = idx * g.stride + 16 * off by omega, ← hp]
      dsimp only [GroupDesc.slotStart]; simp only [BitVec.ofNat_add]; bv_lin
    have hEP : g.slotEnd idx - p = BitVec.ofNat 64 (req + res) := by
      rw [← hp]; dsimp only [GroupDesc.slotEnd]
      rw [show g.stride - 4 = 16 * off + (req + res) by omega]
      simp only [BitVec.ofNat_add]; bv_lin
    have hSub32 : (g.slotEnd idx - p).truncate 32 - (BitVec.ofNat 64 req).truncate 32 = BitVec.ofNat 32 res := by
      rw [hEP]; bv_omega
    have hMsbRes : (BitVec.ofNat 32 res).msb = false :=
      BitVec.msb_eq_false_iff_two_mul_lt.mpr (by simp only [BitVec.toNat_ofNat]; omega)
    have hOffSE : (BitVec.ofNat 32 off <<< 4).signExtend 64 = BitVec.ofNat 64 (16 * off) := by
      have hShl : BitVec.ofNat 32 off <<< 4 = BitVec.ofNat 32 (16 * off) :=
        BitVec.eq_of_toNat_eq (by simp [Nat.shiftLeft_eq]; omega)
      have hM : (BitVec.ofNat 32 (16 * off)).msb = false :=
        BitVec.msb_eq_false_iff_two_mul_lt.mpr (by simp only [BitVec.toNat_ofNat]; omega)
      rw [hShl, BitVec.signExtend_eq_setWidth_of_msb_false hM]; bv_omega
    have hIdxMask : (BitVec.ofNat 32 idx &&& 0xff#32) = BitVec.ofNat 32 idx ∧
        (BitVec.ofNat 32 idx &&& 0x1f#32) = BitVec.ofNat 32 idx := by
      have hAll : (List.range 32).all (fun k =>
          decide ((BitVec.ofNat 32 k &&& 0xff#32) = BitVec.ofNat 32 k ∧
                  (BitVec.ofNat 32 k &&& 0x1f#32) = BitVec.ofNat 32 k)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr hIdx32))
    refine ⟨hOffSE, rfl, by rw [hPS]; bv_omega, hIdxMask.1, hIdxMask.2, by bv_omega, hSub32, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hSub32]
      by_cases h0 : res = 0
      · subst h0; rfl
      · simp only [h0, decide_false, beq_eq_false_iff_ne]; intro h
        have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt (by omega : res < 2 ^ 32)] at this; omega
    · intro _
      have hNeg' : (0#32 - BitVec.ofNat 32 res).signExtend 64 = 0#64 - BitVec.ofNat 64 res := by
        rw [BitVec.zero_sub, BitVec.zero_sub,
            BitVec.signExtend_neg_of_ne_intMin _ (BitVec.ne_intMin_of_msb_eq_false (by decide) hMsbRes),
            BitVec.signExtend_eq_setWidth_of_msb_false hMsbRes]
        congr 1; bv_omega
      rw [hNeg']; dsimp only [GroupDesc.slotEnd]
      rw [show g.stride - 4 = 16 * off + req + res by omega]
      simp only [BitVec.ofNat_add]; bv_lin
    · intro _
      rw [BitVec.sle_eq_ule_of_msb_eq (by rw [hMsbRes]; rfl), BitVec.ule_eq_decide]
      simp [Nat.mod_eq_of_lt (by omega : res < 2 ^ 32)]
    · intro hLe4
      rw [show min res 5 = res by omega]
      have hAll : (List.range 5).all (fun k =>
          decide (((BitVec.ofNat 32 k &&& 7#32) <<< 5) = BitVec.ofNat 32 (k <<< 5))) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.mp hAll res (List.mem_range.mpr (by omega)))
    · intro hGe5; rw [show min res 5 = 5 by omega]; rfl
    · rw [← r5_add_idx_eq_or (Nat.min_le_right res 5) hIdx32]
      have : min res 5 ≤ 5 := Nat.min_le_right res 5
      bv_omega

/-! ## `perm`- and `CodeLoaded`-preserving subword store rules -/

namespace MallocImplH4
theorem step_str8_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := by
    rw [← bitvec_truncate8_truncate32]; exact hval
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write8 _ _ _) (Memory.keepsFrozen_write8 hcan val)) hm'

theorem step_str16_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 16 = val) (hstore : SepStore16 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 16 = val := by
    rw [← bitvec_truncate16_truncate32]; exact hval
  let m' := s.mem.write16 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 2 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .H16 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write16 _ _ _) (Memory.keepsFrozen_write16 hcan val)) hm'
end MallocImplH4
export MallocImplH4 (step_str8_perm_kf step_str16_perm_kf)

scoped macro "wp_str8_cl" m:ident hm:ident hcl_prev:ident hcl_new:ident : tactic => `(tactic| (
  apply step_str8_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf
  have $hcl_new:ident := ($hcl_prev:ident).of_keepsFrozen _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str16_cl" m:ident hm:ident hcl_prev:ident hcl_new:ident : tactic => `(tactic| (
  apply step_str16_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf
  have $hcl_new:ident := ($hcl_prev:ident).of_keepsFrozen _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str8_perm" m:ident hm:ident : tactic => `(tactic| (
  apply step_str8_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str16_perm" m:ident hm:ident : tactic => `(tactic| (
  apply step_str16_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str32_perm" m:ident hm:ident : tactic => `(tactic| (
  apply step_str32_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_str64_perm" m:ident hm:ident : tactic => `(tactic| (
  apply step_str64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

scoped macro "wp_stp64_perm" m:ident hm:ident : tactic => `(tactic| (
  apply step_stp64_perm_kf; (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); wp_close_fetch_cl
  (wp_focus_close (first | wp_norm_lhs | wp_norm_goal)); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs); (wp_focus_close wp_norm_lhs)
  (wp_focus_close wp_sep_access); (wp_focus_close wp_sep_access); (wp_focus_close wp_norm_lhs)
  intro $m:ident $hm:ident _hkf; clear _hkf
  try simp only [arm64_norm] at $hm:ident; try wp_norm_state))

/-! ## Lock/unlock leaf contracts and success postcondition -/

private theorem blk23_unlockNoop_perm [MallocngMultiPlacement] (lk : BitVec 64) :
    subroutine_ok (mallocngBlockProg mmpl 23 msvc) (mbase 23) {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗
        (lk ↦₃₂ 0#32)
    } := by
  have _hw := hasWords_blk_relocFree (i := 23) (by decide)
    (ws := unlockFnWords) (by decide +kernel)
  wp_init x s0; subst lk; wp_steps; wp_done

theorem placed_unlockNoop_perm_ok [MallocngMultiPlacement] {P : Program} (lk : BitVec 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 23) (withCL mmpl {
      pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 = lk⌝ ∗ (lk ↦₃₂ 0#32)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗
        (lk ↦₃₂ 0#32)
    }) :=
  subroutine_ok_block_to_block_plain (j := 23) (by decide) (blk23_unlockNoop_perm lk) hext hsvc

private theorem blk22_lockNoop_perm [MallocngMultiPlacement] (lk : BitVec 64) :
    subroutine_ok (mallocngBlockProg mmpl 22 msvc) (mbase 22) {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = lk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8)
    } := by
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 22) (by decide)
    (ws := lockFnWords) (R := VerifiedLibraries.mallocng_blk22_lock.relocs) (by decide +kernel)
  wp_init x s0; subst lk; wp_steps; wp_done

theorem placed_lockNoop_perm_ok [MallocngMultiPlacement] {P : Program} (lk : BitVec 64)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 22) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.readReg64 .x0 = lk⌝ ∗ ((maddrs.libc + 3#64) ↦₈ 0#8)
      post := fun _ s0 sf =>
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.mem.perm = s0.mem.perm⌝ ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8)
    }) :=
  subroutine_ok_block_to_block_plain (j := 22) (by decide) (blk22_lockNoop_perm lk) hext hsvc

def MallocImplUntouchedCS (s0 s : State) : Prop :=
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem untouchedCS_step {s0 s s' : State} (h : MallocImplUntouchedCS s0 s)
    (h26 : s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (h27 : s'.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5))
    (h28 : s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5))
    (hv : calleeSavedVRegs s' = calleeSavedVRegs s) : MallocImplUntouchedCS s0 s' :=
  ⟨h26.trans h.1, h27.trans h.2.1, h28.trans h.2.2.1, hv.trans h.2.2.2⟩

theorem sp_sub_80_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    ((sp - 80#64) &&& 15#64 == 0#64) = true := by revert h; bv_bits

theorem procPres_trans {s0 s1 s2 : State}
    (h01 : MallocngProcPreserved s0 s1) (h12 : MallocngProcPreserved s1 s2) :
    MallocngProcPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem procPres_setPC {s0 s : State} {pc : BitVec 64} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (s.setPC pc) := by cases s; exact h
theorem procPres_advancePC {s0 s : State} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 s.advancePC := by cases s; exact h
theorem procPres_setPState {s0 s : State} {ps : PState} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (s.setPState ps) := by cases s; exact h
theorem procPres_writeReg64 {s0 s : State} {r : Reg} {v : BitVec 64} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (s.writeReg64 r v) := by cases s; exact h
theorem procPres_writeReg32 {s0 s : State} {r : Reg} {v : BitVec 32} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (s.writeReg32 r v) := by cases s; exact h
theorem procPres_setMem {s0 s : State} {m : Memory} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (s.setMem m) := by cases s; exact h
theorem procPres_applyWriteback {s0 s : State} {wb : Option (Reg × BitVec 64)} (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 (applyWriteback s wb) := by cases wb <;> cases s <;> exact h

theorem mappedDelta_congr_perm_right {k b : Nat} {m0 m1 m2 : Memory}
    (h : MallocngMappedDelta k b m0 m1) (hp : m2.perm = m1.perm) :
    MallocngMappedDelta k b m0 m2 := by
  obtain ⟨ivs, hl, hs, hc⟩ := h
  exact ⟨ivs, hl, hs, fun a ha => hc a (hp ▸ ha)⟩

def mallocImplSuccessBody24 [MallocngMultiPlacement] (γ : GhostName)
    (tp brkStart : BitVec 64) (bud : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (req : Nat) (s0 sf : State) : SepProp :=
  let bf := mallocngAllocBudget true req bud
  stackFrame s0 704 ∗
  ∃∗ p : BitVec 64, ∃∗ bs : List (BitVec 8), ∃∗ st' : MallocngSt,
    ⌜sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
     MallocngBlockWf p req ∧ bs.length = req ∧
     MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
     ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
       g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
       p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
       (g'.isMmapped = true → bs = List.replicate req 0#8) ∧
       (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
       (g'.sc = 24 → nominalSlotCap 23 < max req MallocngMinBlockCost) ∧
       (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115)⌝ ∗
    MallocngRoTablesA maddrs ∗
    MallocngCoreStA γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st' ∗
    MallocngRuntime maddrs tp ∗
    (p ↦ₛ bs) ∗
    MallocngBlockTokenK γ p req 0

def mallocImplSuccessPost24 [MallocngMultiPlacement] (γ : GhostName)
    (tp brkStart : BitVec 64) (bud : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (req : Nat) (s0 sf : State) : SepProp :=
  ⌜MallocngProcPreserved s0 sf ∧
   MallocngMappedDelta 16 (MallocngTightStepBound req bud.peakCount) s0.mem sf.mem⌝ ∗
  mallocImplSuccessBody24 γ tp brkStart bud ivs0 req s0 sf

end VerifiedLibraries.Mallocng.Proofs
