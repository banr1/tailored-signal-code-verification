/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WPp

/-!
# `<spqr::encoding::polynomial::PolyDecoder>::into_pb`: Inner Serialization Loop and Helpers

Proves pure `Pt` big-endian serialization bridges, the inner serialization loop (`+204..+300`), OOM
panic blocks (`+384`, `+396`), and outer-iteration finish (`+300 → +148 / +328`), at fixed base and
on Block `377`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.DecoderPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Pure & Framing Helpers for `Pt` Serialization -/

/-- Serialize a list of `Pt` elements into big-endian 4-byte chunks. -/
def serializePtList (pts : List Pt) : List (BitVec 8) :=
  pts.flatMap Pt.serialize

@[simp] theorem serializePtList_nil :
    serializePtList [] = [] := rfl

@[simp] theorem serializePtList_cons (pt : Pt) (pts : List Pt) :
    serializePtList (pt :: pts) = pt.serialize ++ serializePtList pts := rfl

@[simp] theorem length_pt_serialize (pt : Pt) :
    pt.serialize.length = 4 := rfl

@[simp] theorem length_serializePtList :
    ∀ pts : List Pt, (serializePtList pts).length = 4 * pts.length
  | [] => rfl
  | pt :: pts => by
    rw [serializePtList_cons, List.length_append, length_pt_serialize,
        length_serializePtList pts, List.length_cons]
    omega

theorem intoPb_pts (ss : List SortedSetPt) :
    ss.map (fun s => s.vec.flatMap Pt.serialize) =
      (ss.map SortedSetPt.vec).map serializePtList := by
  rw [List.map_map]; rfl

theorem pointsTo32_rev_orr_eq_pt_serialize (a : BitVec 64) (pt : Pt) :
    (a ↦₃₂ BitVec.truncate 32
      (rev32_64
        (BitVec.zeroExtend 64
          (BitVec.zeroExtend 32 pt.y.value ||| BitVec.zeroExtend 32 pt.x.value <<< 16)))) =
      (a ↦ₛ pt.serialize) := by
  rw [pointsTo32_eq_pointsToBytes]
  congr 1
  simp only [unpack32, Pt.serialize, u16ToBeBytes, rev32_64, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  refine ⟨by bv_slice, by bv_slice, by bv_slice, by bv_slice⟩

theorem memRegion_four_cons (dstPtr : BitVec 64) (done n : Nat)
    (hbound : 4 * (n + 1) < 2 ^ 63) :
    memRegion (dstPtr + BitVec.ofNat 64 (4 * done)) (4 * (n + 1)) =
      (∃∗ v : BitVec 32, (dstPtr + BitVec.ofNat 64 (4 * done)) ↦₃₂ v) ∗
        memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * n) := by
  have hmul : 4 * (n + 1) = 4 + 4 * n := by omega
  have hadd : dstPtr + BitVec.ofNat 64 (4 * done) + 4#64 =
      dstPtr + BitVec.ofNat 64 (4 * (done + 1)) := by
    rw [BitVec.add_assoc]
    congr 1
    simp [Nat.mul_add, BitVec.ofNat_add]
  rw [hmul, ProofLib.memRegion_split (dstPtr + BitVec.ofNat 64 (4 * done)) 4 (4 * n) (by omega),
      ProofLib.memRegion_four, hadd]

theorem off_add_four (done : Nat) :
    BitVec.ofNat 64 (4 * done) + 4#64 = BitVec.ofNat 64 (4 * (done + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]; bv_omega

theorem rem_bytes_not_ule_three {done remLen total : Nat}
    (htot : done + (remLen + 1) = total) (hmax : 4 * total < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 (4 * total) - BitVec.ofNat 64 (4 * done)) 3#64 = false := by
  have hsub : BitVec.ofNat 64 (4 * total) - BitVec.ofNat 64 (4 * done) =
      BitVec.ofNat 64 (4 * (remLen + 1)) := by
    have h1 : 4 * total = 4 * done + 4 * (remLen + 1) := by omega
    rw [h1, BitVec.ofNat_add]
    bv_omega
  rw [hsub]
  have hlt : 4 * (remLen + 1) < 2 ^ 64 := by omega
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, decide_eq_false_iff_not]
  change ¬ (4 * (remLen + 1) ≤ 3)
  omega

theorem bne_one_of_pos {n : Nat} (hpos : 0 < n) (hlt : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (n + 1) != 1#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n + 1 = 1 at ht
  omega

@[local arm64_norm, local wp_norm]
theorem fp64_sub_24 (fsp : BitVec 64) :
    (fsp + 64#64) + 18446744073709551592#64 = fsp + 40#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp64_sub_16 (fsp : BitVec 64) :
    (fsp + 64#64) + 18446744073709551600#64 = fsp + 48#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp64_sub_8 (fsp : BitVec 64) :
    (fsp + 64#64) + 18446744073709551608#64 = fsp + 56#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem fp64_sub_24_int (fsp : BitVec 64) :
    (fsp + 64#64) + (-24 : Int64).toBitVec = fsp + 40#64 := fp64_sub_24 fsp

@[local arm64_norm, local wp_norm]
theorem fp64_sub_16_int (fsp : BitVec 64) :
    (fsp + 64#64) + (-16 : Int64).toBitVec = fsp + 48#64 := fp64_sub_16 fsp

@[local arm64_norm, local wp_norm]
theorem fp64_sub_8_int (fsp : BitVec 64) :
    (fsp + 64#64) + (-8 : Int64).toBitVec = fsp + 56#64 := fp64_sub_8 fsp

@[local arm64_norm, local wp_norm]
theorem sp_add_40_add_8 (fsp : BitVec 64) :
    (fsp + 40#64) + 8#64 = fsp + 48#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem srcCur_add_2_sub_2 (srcCur : BitVec 64) :
    (srcCur + 2#64) + 18446744073709551614#64 = srcCur := by bv_omega

@[local arm64_norm, local wp_norm]
theorem srcCur_add_2_sub_2_int (srcCur : BitVec 64) :
    (srcCur + 2#64) + (-2 : Int64).toBitVec = srcCur := srcCur_add_2_sub_2 srcCur

theorem srcCur_add_4_add_2 (srcCur : BitVec 64) :
    srcCur + 6#64 = (srcCur + 4#64) + 2#64 := by bv_omega

/-! ## Fetch Helper Macro for `<PolyDecoder>::into_pb` -/

gen_decodes libsignalSessionCode_tree spqrDecoderIntoPbBin
  [0x5dc38 → 0x5ddd0]

@[simp, arm64_norm] theorem decoderIntoPb_fnOff :
    libsignalSessionCode.fnOff decoderIntoPbName =
      num% (ls_off% "<spqr::encoding::polynomial::PolyDecoder>::into_pb") :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb"

open Lean Elab Tactic in
scoped elab "into_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic => do
  let off ← ProofLib.CodeLookup.lookupOff ``CryptoVerification.libsignalSessionCode "<spqr::encoding::polynomial::PolyDecoder>::into_pb"
  let offLit := Syntax.mkNumLit (toString off.val)
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode spqrDecoderIntoPbBin $b $H decoderIntoPb_fnOff $offLit $k0 $len))

/-! ## Inner Serialization Loop (`0x630fc..0x63134`, `+204 -> +300`) -/

/-- Inner serialization loop for `Pt` elements (`0x630fc..0x63134`, `+204 -> +300`). -/
theorem pts_inner_loop {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 4 * total < 2 ^ 63)
    (rem : List Pt) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (4 * done))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur + 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 300#64)
      s
      (arrayAt ptAt 4 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (4 * done)) (4 * rem.length) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
        ((fsp + 56#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt ptAt 4 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList rem) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 204 60
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  examples_hide_fetches
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons pt rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 4 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (4 * total) - BitVec.ofNat 64 (4 * done)) 3#64 = false :=
      rem_bytes_not_ule_three htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_four_cons dstPtr done rem'.length hrem_bound]
    dsimp only [ptAt, gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v32
    refine DropGlueFacts.seq_clean (mid := entry + 232#64)
      (P_mid :=
        (srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
          arrayAt ptAt 4 (srcCur + 4#64) rem' ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦₃₂ v32) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * rem'.length) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (4 * done) ∧
        sm.readReg64 .x8 = (((pt.y.value.zeroExtend 64).setWidth 32 |||
          (pt.x.value.zeroExtend 64).setWidth 32 <<< 16).zeroExtend 64) ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx8_1, hx25_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx28_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 4 * (done + 1) = 4 * total := by simp at htot'; omega
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx25_1 ⊢
        wp_steps
        rw [off_add_four done, hdone_tot, pointsTo32_rev_orr_eq_pt_serialize]
        have hser1 : serializePtList [pt] = pt.serialize := by
          simp [serializePtList]
        rw [hser1, arrayAt_cons]
        dsimp only [ptAt, gf16At]
        simp only [arrayAt_nil, sepConj_emp]
        wp_done
      | cons pt2 rem'' =>
        have hne' : pt2 :: rem'' ≠ [] := List.cons_ne_nil pt2 rem''
        have hpos' : 0 < (pt2 :: rem'').length := by simp
        have hlt' : (pt2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((pt2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := entry + 204#64)
          (P_mid :=
            arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * (pt2 :: rem'').length) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (done + 1))) ∗
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 64#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (4 * (done + 1)) ∧
            sm.readReg64 .x25 = BitVec.ofNat 64 (pt2 :: rem'').length ∧
            sm.readReg64 .x21 = (srcCur + 4#64) + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · wp_steps
          rw [off_add_four done, ofNat_succ_sub_one (pt2 :: rem'').length,
            srcCur_add_4_add_2 srcCur, pointsTo32_rev_orr_eq_pt_serialize]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx25_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 4#64)
            (BitVec.ofNat 64 (4 * (done + 1)))
            ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
              Frame)
            hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx25_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htrace2 hvregs2 hpc2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt ptAt 4 srcCur (pt :: pt2 :: rem'') =
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value)) ∗
                arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') := by
            rw [arrayAt_cons]
            rfl
          have hser : ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList (pt :: pt2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * (done + 1))) ↦ₛ serializePtList (pt2 :: rem'')) := by
            rw [serializePtList_cons]
            exact pointsToBytes_append_off dstPtr (4 * done) (4 * (done + 1))
              pt.serialize (serializePtList (pt2 :: rem''))
              (by simp [length_pt_serialize]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

/-! ## OOM Panic Helpers (`+0x180 = +384` and `+0x18c = +396`) -/

abbrev intoPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- OOM panic block at `+0x180` (`+384..+392`: `mov w0, #1; mov x1, x21; bl handle_error`). -/
theorem into_pb_panic_384 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 384#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := decoderIntoPbName) (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb" "alloc::raw_vec::handle_error"))
  into_pb_fetches_range b (Rust.withPanics ext) 384 12
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-- OOM panic block at `+0x18c` (`+396..+404`: `mov w0, #8; mov w1, #0x180; bl handle_error`). -/
theorem into_pb_panic_396 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 396#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := decoderIntoPbName) (k := num% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb" "alloc::raw_vec::handle_error"))
  into_pb_fetches_range b (Rust.withPanics ext) 396 12
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb" "alloc::raw_vec::handle_error"))
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## Outer Loop Helpers and Finish-Iteration Block (`+300 -> +104 -> +148/+328`) -/

@[local arm64_norm, local wp_norm]
theorem ofNat_add_one (j : Nat) :
    BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.ofNat_add]

@[local arm64_norm, local wp_norm]
theorem madd_24_eq (base : BitVec 64) (j : Nat) :
    base + BitVec.ofNat 64 j * 24#64 = base + BitVec.ofNat 64 (24 * j) := by
  congr 1
  rw [Nat.mul_comm, BitVec.ofNat_mul]

theorem off_24_succ (base : BitVec 64) (j : Nat) :
    (base + BitVec.ofNat 64 (24 * j)) + 24#64 = base + BitVec.ofNat 64 (24 * (j + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem ofNat_ne_16 {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 64 j != 16#64) = true := by
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change j = 16 at ht
  omega

theorem ofNat_beq_16_false {j : Nat} (hj : j < 16) :
    (BitVec.ofNat 64 j == 16#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change j = 16 at ht
  omega

theorem memRegion_24_cons (base : BitVec 64) (j n : Nat) (h : j + (n + 1) ≤ 16) :
    memRegion (base + BitVec.ofNat 64 (24 * j)) (24 * (n + 1)) =
      (∃∗ v0 : BitVec 64, (base + BitVec.ofNat 64 (24 * j)) ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, ((base + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, ((base + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ v2) ∗
      memRegion (base + BitVec.ofNat 64 (24 * (j + 1))) (24 * n) := by
  have hmul : 24 * (n + 1) = 24 + 24 * n := by omega
  let el := base + BitVec.ofNat 64 (24 * j)
  have h24 : memRegion el 24 =
      (∃∗ v0 : BitVec 64, el ↦₆₄ v0) ∗
      (∃∗ v1 : BitVec 64, (el + 8#64) ↦₆₄ v1) ∗
      (∃∗ v2 : BitVec 64, (el + 16#64) ↦₆₄ v2) := by
    have h88 : (el + 8#64) + 8#64 = el + 16#64 := by bv_omega
    rw [show (24 : Nat) = 8 + (8 + 8) by rfl,
        ProofLib.memRegion_split el 8 (8 + 8) (by decide),
        ProofLib.memRegion_split (el + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        h88]
  rw [hmul, ProofLib.memRegion_split el 24 (24 * n) (by omega), h24, off_24_succ,
      sepConj_assoc, sepConj_assoc]

theorem vecU8_slot_intro (A : RustAlloc) (el cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
      ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢
    vecU8 A el bs := by
  have heq :
      (el ↦₆₄ cap) ∗ ((el + 8#64) ↦₆₄ ptr) ∗
        ((el + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs =
      vecU8At A el cap ptr bs := by
    rw [vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl
  rw [heq]
  exact vecU8At_entails_vecU8 A el cap ptr bs

/-- Finish one iteration of the `pts` outer loop (`+300 -> +104 -> +148 / +328`). -/
theorem pts_outer_finish_iter {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      (if j + 1 = 16 then
        (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 328#64
       else
        (tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName + 148#64)
      s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  into_pb_fetches_range b (Rust.withPanics ext) 300 16
  into_pb_fetches_range b (Rust.withPanics ext) 104 44
  dsimp only [tripleRatchetProgAtExt, decoderIntoPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr
    "<spqr::encoding::polynomial::PolyDecoder>::into_pb" = entry
  examples_hide_fetches
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_pts j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_pts + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    have hgroup :
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs ∗
          ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        ((((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs) ∗
          ((fsp ↦₆₄ 16#64) ∗
            ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
            ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 40#64) ↦₆₄ cap_c) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left hslot) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

/-! ## Relocatable (`[LibsignalPlacement]`) Proofs for Block `377` -/

theorem pts_inner_loop_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (s0 : State) (fsp dstPtr : BitVec 64)
    (total : Nat) (hmax : 4 * total < 2 ^ 63)
    (rem : List Pt) (hne : rem ≠ [])
    (done : Nat) (htot : done + rem.length = total)
    (s : State) (srcCur lenVal : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx0 : s.readReg64 .x0 = dstPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (4 * done))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rem.length)
    (hx21 : s.readReg64 .x21 = srcCur + 2#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = s0.readReg64 .x22)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23)
    (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      ((blkPl_377).base + 300#64)
      s
      (arrayAt ptAt 4 srcCur rem ∗
        memRegion (dstPtr + BitVec.ofNat 64 (4 * done)) (4 * rem.length) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
        ((fsp + 56#64) ↦₆₄ lenVal) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ arrayAt ptAt 4 srcCur rem ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList rem) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  induction rem generalizing s done srcCur lenVal Frame with
  | nil => exact (hne rfl).elim
  | cons pt rem' ih =>
    have htot' : done + (rem'.length + 1) = total := by
      simpa [List.length_cons] using htot
    have hrem_bound : 4 * (rem'.length + 1) < 2 ^ 63 := by omega
    have hnot_ule : BitVec.ule (BitVec.ofNat 64 (4 * total) - BitVec.ofNat 64 (4 * done)) 3#64 = false :=
      rem_bytes_not_ule_three htot' hmax
    nth_rw 1 [arrayAt_cons]
    nth_rw 1 [List.length_cons]
    rw [memRegion_four_cons dstPtr done rem'.length hrem_bound]
    dsimp only [ptAt, gf16At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_left; intro v32
    refine DropGlueFacts.seq_clean (mid := (blkPl_377).base + 232#64)
      (P_mid :=
        (srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
          arrayAt ptAt 4 (srcCur + 4#64) rem' ∗
          ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦₃₂ v32) ∗
          memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * rem'.length) ∗
          ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
          ((fsp + 56#64) ↦₆₄ lenVal) ∗
          Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x0 = dstPtr ∧
        sm.readReg64 .x1 = BitVec.ofNat 64 (4 * done) ∧
        sm.readReg64 .x8 = (((pt.y.value.zeroExtend 64).setWidth 32 |||
          (pt.x.value.zeroExtend 64).setWidth 32 <<< 16).zeroExtend 64) ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (rem'.length + 1) ∧
        sm.readReg64 .x21 = srcCur + 2#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧
        sm.readReg64 .x23 = s0.readReg64 .x23 ∧
        sm.readReg64 .x24 = s0.readReg64 .x24 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · wp_steps
      wp_done
    · intro s1 hpc1 hrun1 ⟨hsp1, hx29_1, hx0_1, hx1_1, hx8_1, hx25_1, hx21_1,
        hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx28_1, htrace1, hvregs1⟩
      cases rem' with
      | nil =>
        have hdone_tot : 4 * (done + 1) = 4 * total := by simp at htot'; omega
        simp only [List.length_nil, Nat.zero_add, Nat.mul_zero, memRegion_zero, sepConj_emp] at hx25_1 ⊢
        wp_steps
        rw [off_add_four done, hdone_tot, pointsTo32_rev_orr_eq_pt_serialize]
        have hser1 : serializePtList [pt] = pt.serialize := by
          simp [serializePtList]
        rw [hser1, arrayAt_cons]
        dsimp only [ptAt, gf16At]
        simp only [arrayAt_nil, sepConj_emp]
        wp_done
      | cons pt2 rem'' =>
        have hne' : pt2 :: rem'' ≠ [] := List.cons_ne_nil pt2 rem''
        have hpos' : 0 < (pt2 :: rem'').length := by simp
        have hlt' : (pt2 :: rem'').length + 1 < 2 ^ 64 := by simp at htot'; omega
        have hsubs_ne : (BitVec.ofNat 64 ((pt2 :: rem'').length + 1) != 1#64) = true :=
          bne_one_of_pos hpos' hlt'
        refine DropGlueFacts.seq_clean (mid := (blkPl_377).base + 204#64)
          (P_mid :=
            arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') ∗
              memRegion (dstPtr + BitVec.ofNat 64 (4 * (done + 1))) (4 * (pt2 :: rem'').length) ∗
              ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 (4 * total)) ∗
              ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 (4 * (done + 1))) ∗
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                Frame))
          (Q := fun sm =>
            sm.sp = fsp ∧
            sm.readReg64 .x29 = fsp + 64#64 ∧
            sm.readReg64 .x0 = dstPtr ∧
            sm.readReg64 .x1 = BitVec.ofNat 64 (4 * (done + 1)) ∧
            sm.readReg64 .x25 = BitVec.ofNat 64 (pt2 :: rem'').length ∧
            sm.readReg64 .x21 = (srcCur + 4#64) + 2#64 ∧
            sm.readReg64 .x19 = s0.readReg64 .x19 ∧
            sm.readReg64 .x20 = s0.readReg64 .x20 ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧
            sm.readReg64 .x23 = s0.readReg64 .x23 ∧
            sm.readReg64 .x24 = s0.readReg64 .x24 ∧
            sm.readReg64 .x28 = s0.readReg64 .x28 ∧
            sm.trace = s0.trace ∧
            calleeSavedVRegs sm = calleeSavedVRegs s0)
          ?_ ?_
        · wp_steps
          rw [off_add_four done, ofNat_succ_sub_one (pt2 :: rem'').length,
            srcCur_add_4_add_2 srcCur, pointsTo32_rev_orr_eq_pt_serialize]
          refine DropGlueFacts.align_pre (by ac_rfl) ?_
          wp_done
        · intro s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx0_2, hx1_2, hx25_2, hx21_2,
            hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx28_2, htrace2, hvregs2⟩
          have hih := ih hne' (done + 1) (by omega) s2 (srcCur + 4#64)
            (BitVec.ofNat 64 (4 * (done + 1)))
            ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value) ∗
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
              Frame)
            hpc2 hrun2 hsp2 hx29_2 hx0_2 hx1_2 hx25_2 hx21_2
            hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx28_2 htrace2 hvregs2
          refine SepWP.strengthen_entails_const ?_ hih
          have harr : arrayAt ptAt 4 srcCur (pt :: pt2 :: rem'') =
              ((srcCur ↦₁₆ pt.x.value) ∗ ((srcCur + 2#64) ↦₁₆ pt.y.value)) ∗
                arrayAt ptAt 4 (srcCur + 4#64) (pt2 :: rem'') := by
            rw [arrayAt_cons]
            rfl
          have hser : ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ serializePtList (pt :: pt2 :: rem'')) =
              ((dstPtr + BitVec.ofNat 64 (4 * done)) ↦ₛ pt.serialize) ∗
                ((dstPtr + BitVec.ofNat 64 (4 * (done + 1))) ↦ₛ serializePtList (pt2 :: rem'')) := by
            rw [serializePtList_cons]
            exact pointsToBytes_append_off dstPtr (4 * done) (4 * (done + 1))
              pt.serialize (serializePtList (pt2 :: rem''))
              (by simp [length_pt_serialize]; omega)
          rw [harr, hser]
          exact Entails.of_eq (by ac_rfl)

theorem into_pb_panic_384_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_377).base + 384#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic : ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem into_pb_panic_396_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_377).base + 396#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ intoPbOnPanic s0 sf ∗ R)) := by
  have hpanic : ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (SpqrV1.Alloc.spqr_externAt?_of_mem).trans h_panic
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [intoPbOnPanic, sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

theorem pts_outer_finish_iter_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (s0 : State) (fsp ptr_pts : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j remLen : Nat) (htot : j + (remLen + 1) = 16)
    (bs : List (BitVec 8)) (cap_c ptr_c : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_377).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 64#64)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = 24#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (if j + 1 = 16 then
        (blkPl_377).base + 328#64
       else
        (blkPl_377).base + 148#64)
      s
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 j) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * j)) (24 * (remLen + 1)) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          (fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 64#64 ∧
        sm.readReg64 .x19 = s0.readReg64 .x19 ∧
        sm.readReg64 .x20 = s0.readReg64 .x20 ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x23 = 24#64 ∧
        sm.readReg64 .x24 = 1#64 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧
        sm.trace = s0.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  have hj_lt : j < 16 := by omega
  have hne16 : (BitVec.ofNat 64 j != 16#64) = true := ofNat_ne_16 hj_lt
  have hbeq16 : (BitVec.ofNat 64 j == 16#64) = false := ofNat_beq_16_false hj_lt
  rw [memRegion_24_cons ptr_pts j remLen (by omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro d0
  apply SepWP.exists_left; intro d1
  apply SepWP.exists_left; intro d2
  have hslot := vecU8_slot_intro A (ptr_pts + BitVec.ofNat 64 (24 * j)) cap_c ptr_c bs
  have hent :
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap_c ptr_c bs ∗
        ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
        (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) ⊢
      ((fsp ↦₆₄ 16#64) ∗
        ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
        ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
        ((fsp + 40#64) ↦₆₄ cap_c) ∗
        ((fsp + 48#64) ↦₆₄ ptr_c) ∗
        ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8 A (ptr_pts + BitVec.ofNat 64 (24 * j)) bs ∗
        memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
        Frame) := by
    have hgroup :
        ((fsp ↦₆₄ 16#64) ∗
          ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
          ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
          ((fsp + 40#64) ↦₆₄ cap_c) ∗
          ((fsp + 48#64) ↦₆₄ ptr_c) ∗
          ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs ∗
          ((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
          Frame) =
        ((((ptr_pts + BitVec.ofNat 64 (24 * j)) ↦₆₄ cap_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ ptr_c) ∗
          (((ptr_pts + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecU8Buf A cap_c ptr_c bs) ∗
          ((fsp ↦₆₄ 16#64) ∗
            ((fsp + 8#64) ↦₆₄ ptr_pts) ∗
            ((fsp + 16#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
            ((fsp + 40#64) ↦₆₄ cap_c) ∗
            ((fsp + 48#64) ↦₆₄ ptr_c) ∗
            ((fsp + 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            memRegion (ptr_pts + BitVec.ofNat 64 (24 * (j + 1))) (24 * remLen) ∗
            Frame)) := by ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left hslot) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hdone : j + 1 = 16
  · have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = true := by simp [hdone]
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = false := by simp [hdone]
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)
  · have hj1_lt : j + 1 < 16 := by omega
    have hj1_beq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := ofNat_beq_16_false hj1_lt
    have hj1_ne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := ofNat_ne_16 hj1_lt
    conv => arg 2; simp only [hdone, ↓reduceIte]
    clear hdone
    wp_steps
    exact SepWP.weaken_pre hent (by wp_done)

end CryptoVerification.SpqrV1.Poly.DecoderPb
