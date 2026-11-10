/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Phase 1 and Top-Level Verification of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`

Verifies wire-type checking and varint dispatch (Phase 1) and proves `bytes_merge_ok`,
`bytes_merge_ok_x`, and `bytes_merge_placed_ok`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.VarintBridge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    calleeSavedVRegs (s.writeReg64 r v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    calleeSavedVRegs (s.writeReg32 r v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setPC (s : State) (v : BitVec 64) :
    calleeSavedVRegs (s.setPC v) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setPState (s : State) (p : PState) :
    calleeSavedVRegs (s.setPState p) = calleeSavedVRegs s := rfl
@[simp, arm64_norm, wp_norm] theorem calleeSavedVRegs_setMem (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge_fnOff
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## Phase 1 and `bytes_merge_ok` -/

theorem mergeBytes_ne_lengthDelimited {wt : WireType} {bs : List (BitVec 8)}
    (hwt : wt ≠ .lengthDelimited) :
    mergeBytes wt bs = none := by
  cases wt <;> simp_all [mergeBytes]

theorem mergeBytes_nil {wt : WireType} :
    mergeBytes wt [] = none := by
  cases wt <;> simp [mergeBytes, decodeVarint, decodeVarintAux]

theorem mergeBytes_of_decodeVarint_none {wt : WireType} {bs : List (BitVec 8)}
    (h : decodeVarint bs = none) :
    mergeBytes wt bs = none := by
  cases wt <;> simp [mergeBytes, h]

namespace BytesMergeFacts

theorem bitvec8_forall {P : BitVec 8 → Prop}
    (h : ∀ i : Fin 256, P (BitVec.ofFin i)) : ∀ (b : BitVec 8), P b := by
  intro b
  simpa using h b.toFin

theorem setWidth32_and_255_eq (w : BitVec 64) :
    w.setWidth 32 &&& 255#32 = (w.setWidth 8).zeroExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth]
  change (w.toNat % 4294967296 &&& (2 ^ 8 - 1)) = (w.toNat % 256) % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem truncate32_zeroExtend64_and_255_eq (w : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 w) &&& 255#64) =
      (w.setWidth 8).zeroExtend 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and]
  change (((w.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) =
    (w.toNat % 256) % 4294967296
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

end BytesMergeFacts

theorem decodeVarint_cons_of_signExtend_63_false {b0 : BitVec 8} {bs' : List (BitVec 8)}
    (h : (b0.signExtend 64).getLsbD 63 = false) :
    decodeVarint (b0 :: bs') = some (b0.signExtend 64, bs') := by
  have h1 : b0.toNat ≤ 127 := by
    have hlt : b0.ult 128#8 = true := by revert h b0; apply BytesMergeFacts.bitvec8_forall; decide
    have hlt' : b0.toNat < 128 := by simpa [BitVec.ult] using hlt
    omega
  have h2 : (BitVec.setWidth 64 b0 &&& 127#64) = b0.signExtend 64 := by
    revert h b0; apply BytesMergeFacts.bitvec8_forall; decide
  simp [decodeVarint, decodeVarintAux, h1, h2]

theorem fold_sliceCursorAfter_from_consumed (slot ptr : BitVec 64) (bs rest0 : List (BitVec 8))
    (hle : rest0.length ≤ bs.length) :
    (slot ↦₆₄ (ptr + BitVec.ofNat 64 (bs.length - rest0.length))) ∗
      ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest0.length))) ∗
      (ptr ↦ₛ bs) ⊢
      sliceCursorAfter slot ptr bs rest0 := by
  have hsub : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest0.length) =
      BitVec.ofNat 64 rest0.length := by
    have h1 : bs.length = (bs.length - rest0.length) + rest0.length := by omega
    conv => lhs; lhs; rw [h1, BitVec.ofNat_add]
    bv_omega
  rw [hsub]
  exact Entails.refl _

theorem fold_memRegion_48_sret_err (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  have e1 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have e2 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  have h1 : memRegion (a + 16#64) 8 ∗ memRegion (a + 24#64) 24 = memRegion (a + 16#64) 32 := by
    rw [show (32 : Nat) = 8 + 24 from rfl, memRegion_split (a + 16#64) 8 24 (by decide), e2]
  rw [h1]
  refine Entails.trans (sepConj_mono_right ?_) (memRegion_cons a w0 (n := 48) (by decide) (by decide))
  have c := memRegion_cons (a + 8#64) w1 (n := 40) (by decide) (by decide)
  rwa [e1] at c

theorem fold_memRegion_48_sret_ok (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ memRegion (a + 24#64) 24 ⊢
      memRegion a 48 := by
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (pointsTo64_entails_memRegion (a + 16#64) w2)))) ?_
  exact fold_memRegion_48_sret_err a w0 w1

theorem varintSlow_none_iff (l : List (BitVec 8)) :
    varintSlow l = none ↔ decodeVarint l = none := by
  rw [decodeVarint_eq_varintSlow, Option.map_eq_none_iff]


theorem fold_sliceCursorAfter_drop (slot ptr : BitVec 64) (bs : List (BitVec 8)) (k : Nat)
    (hkl : k ≤ bs.length) :
    (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
      (ptr ↦ₛ bs) ⊢
      sliceCursorAfter slot ptr bs (bs.drop k) := by
  unfold sliceCursorAfter
  have h1 : bs.length - (bs.drop k).length = k := by rw [List.length_drop]; omega
  rw [h1, List.length_drop]
  exact Entails.refl _


theorem SepWPp.unfold_cells_64 {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : BitVec 64, SepWPp prog ret s
      (((sp0 - 64#64) ↦₆₄ c0) ∗ ((sp0 - 56#64) ↦₆₄ c1) ∗
        ((sp0 - 48#64) ↦₆₄ c2) ∗ ((sp0 - 40#64) ↦₆₄ c3) ∗
        ((sp0 - 32#64) ↦₆₄ c4) ∗ ((sp0 - 24#64) ↦₆₄ c5) ∗
        ((sp0 - 16#64) ↦₆₄ c6) ∗ ((sp0 - 8#64) ↦₆₄ c7) ∗ P) Q Qp) :
    SepWPp prog ret s (cells (sp0 - 64#64) 8 ∗ P) Q Qp := by
  refine SepWPp.unfold_cell_sub (off := 64) (k := 7) (h := fun c0 => ?_)
  refine SepWPp.unfold_cell_sub (off := 56) (k := 6) (h := fun c1 => ?_)
  refine SepWPp.unfold_cell_sub (off := 48) (k := 5) (h := fun c2 => ?_)
  refine SepWPp.unfold_cell_sub (off := 40) (k := 4) (h := fun c3 => ?_)
  refine SepWPp.unfold_cell_sub (off := 32) (k := 3) (h := fun c4 => ?_)
  refine SepWPp.unfold_cell_sub (off := 24) (k := 2) (h := fun c5 => ?_)
  refine SepWPp.unfold_cell_sub (off := 16) (k := 1) (h := fun c6 => ?_)
  rw [cells_succ, cells_zero, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun c7 => ?_
  exact SepWPp.weaken_pre (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, sepConj_emp]; ac_rfl))
    (h c0 c1 c2 c3 c4 c5 c6 c7)

theorem SepWPp.unfold_memRegion_216_invalidWireType {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 64) (b0 b1 : BitVec 8), SepWPp prog ret s
      (((sp0 - 216#64) ↦₆₄ w0) ∗ ((sp0 - 216#64 + 8#64) ↦₈ b0) ∗
        ((sp0 - 216#64 + 9#64) ↦₈ b1) ∗ memRegion (sp0 - 216#64 + 10#64) 38 ∗ P) Q Qp) :
    SepWPp prog ret s (memRegion (sp0 - 216#64) 48 ∗ P) Q Qp := by
  rw [memRegion_48_invalidWireType (sp0 - 216#64), sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w0 => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun b0 => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun b1 => ?_
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (h w0 b0 b1)

theorem bm_pointsToBytes_split_last (ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.dropLast) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 0xffffffffffffffff#64) ↦₈ bs.getLast hne) := by
  have hbs : bs = bs.dropLast ++ [bs.getLast hne] := (List.dropLast_append_getLast hne).symm
  have hpos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hdl : bs.dropLast.length = bs.length - 1 := List.length_dropLast
  have had : ptr + BitVec.ofNat 64 bs.dropLast.length =
      ptr + BitVec.ofNat 64 bs.length + 0xffffffffffffffff#64 := by
    rw [hdl]
    have h1 : bs.length = (bs.length - 1) + 1 := by omega
    conv => rhs; lhs; rhs; rw [h1, BitVec.ofNat_add]
    bv_omega
  conv => lhs; rw [hbs, pointsToBytes_append, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, had]

theorem fold_sliceCursorAfter_cons (slot ptr : BitVec 64) (b0 : BitVec 8) (bs' : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 1#64)) ∗
      ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 (b0 :: bs').length - 1#64)) ∗
      (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs') ⊢
      sliceCursorAfter slot ptr (b0 :: bs') bs' := by
  unfold sliceCursorAfter
  have h1 : (b0 :: bs').length - bs'.length = 1 := by simp
  have h2 : BitVec.ofNat 64 (b0 :: bs').length - 1#64 = BitVec.ofNat 64 bs'.length := by
    simp only [List.length_cons, BitVec.ofNat_add]
    bv_omega
  rw [h1, h2, pointsToBytes_cons]
  exact Entails.of_eq (by ac_rfl)

theorem toNat_le_0x7f_of_getLsbD_7_false {b : BitVec 8}
    (h : b.getLsbD 7 = false) :
    b.toNat ≤ 0x7F := by
  have h2 : b.ult 128#8 = true := by revert h b; apply BytesMergeFacts.bitvec8_forall; decide
  have h3 : b.toNat < 128 := by simpa [BitVec.ult] using h2
  omega


theorem mask_ff_32_of_setWidth8 {w : BitVec 64} {b : BitVec 8} (h : w.setWidth 8 = b) :
    (w.setWidth 32 &&& 255#32).zeroExtend 64 = b.zeroExtend 64 := by
  rw [BytesMergeFacts.setWidth32_and_255_eq, h]
  clear h w
  revert b
  apply BytesMergeFacts.bitvec8_forall
  decide

theorem SepWPp.to_subroutineOutcome {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePost A x s0 R) (MergePanic A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMergeSpec A img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim


theorem bmPreBound_elim {reqCap : Bool} {s0 : State} {x : BytesMergeGhost}
    (h : bmPreBound reqCap s0 x) :
    (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
    s0.readReg64 .x1 = x.valPtr ∧ s0.readReg64 .x2 = x.bufRef ∧
    bmLenBound reqCap x.bs.length ∧ bmCapCond reqCap x.valCap x.bs.length := by
  cases reqCap
  · obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, h3, h4, trivial⟩
  · exact h

theorem SepWPp.to_subroutineOutcome_gen {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {errStack : Nat} {reqCap : Bool}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMergeSpecGen A errStack reqCap img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

section FnOffShield
attribute [local irreducible] _root_.Arm64.Program.fnOff

private theorem phase1_from_0x08c_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A errStack).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmShimSpecGen errStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((rustAllocSpecWithStack A hStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecBMGen A errStack).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpre : VarintSlicePre x.bs)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 140#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcall_slice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeVarintSliceSpecBMGen A errStack).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMergeName) (callee := decodeVarintSliceName) (k := bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))]
    exact hVarintSlice
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_err_0x0a4_gen img A H errStack reqCap hbnd x s0 s R hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableSlot hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  clear hVarintSlice hBytesFromVec hReserve hVtableDrop
  merge_fetches_H img.base H bytesMerge_fnOff 140 84
  dsimp only [sliceCursorAt] at hpc hcall_slice herr_exit h0e0_exit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  rw [memRegion_48_sret24 (s0.sp - 216#64)]
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  refine SepWPp.bm_call_frame_inv
    (x := ({ ret := s0.sp - 216#64, ptr := x.ptr, bs := x.bs } : DecodeVarintSliceGhost))
    (T := memRegion (s0.sp - 216#64) 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hcall_slice hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen, arm64_norm, hsp]; rfl)
    (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1],
               by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8, hbs_toNat],
               bmLenBound_lt63 hbs_len, hpre⟩)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeVarintSliceSpecBMGen,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_vs hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · dsimp only [varintSliceResultAt]
    refine SepWPp.weaken_pre (P' :=
      (∃∗ e : BitVec 64, ⌜e ≠ 0#64⌝ ∗ ((s0.sp - 216#64 + 8#64) ↦₆₄ e) ∗ decodeErrorAtStackLen A e 0) ∗
        (((s0.sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 216#64 + 16#64) 8 ∗
          (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64 + 24#64) 24 ∗
          memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0))
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun e => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun he => ?_
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (164))
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_err (s0.sp - 216#64) 1#64 e) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact he)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
  · dsimp only [varintSliceResultAt]
    have hrest0_le : rest0.length ≤ x.bs.length := by
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      rw [hpfx, List.length_append]
      omega
    have hcons_toNat : (BitVec.ofNat 64 (x.bs.length - rest0.length)).toNat = x.bs.length - rest0.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hult_cons : (BitVec.ofNat 64 x.bs.length).ult (BitVec.ofNat 64 (x.bs.length - rest0.length)) = false := by
      simp [BitVec.ult, hbs_toNat, hcons_toNat]
    have hule_cons : (BitVec.ofNat 64 (x.bs.length - rest0.length)).ule (BitVec.ofNat 64 x.bs.length) = true := by
      simp [BitVec.ule, hbs_toNat, hcons_toNat]
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (224))
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_ok (s0.sp - 216#64) 0#64 len
      (BitVec.ofNat 64 (x.bs.length - rest0.length))) (by sep_focus)
    apply SepWP.fold (fold_sliceCursorAfter_from_consumed x.slot x.ptr x.bs rest0 hrest0_le) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len rest0 hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by ac_rfl)

private theorem phase1_from_0x398_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A errStack).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmShimSpecGen errStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((rustAllocSpecWithStack A hStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + errStack)).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hcall_slow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeVarintSlowSpecWithStack A (64 + errStack)).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMergeName) (callee := varintSlowName) (k := bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))]
    exact hVarintSlow
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_err_0x0a4_gen img A H errStack reqCap hbnd x s0 s R hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableSlot hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  clear hVarintSlow hBytesFromVec hReserve hVtableDrop
  merge_fetches_H img.base H bytesMerge_fnOff 920 28
  dsimp only [sliceCursorAt] at hpc hcall_slow herr_exit h0e0_exit ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  refine SepWPp.bm_call_frame_inv
    (x := (x.bufRef, x.slot, x.ptr, x.bs))
    (T := (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (64 + errStack))
    hcall_slow hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSlowSpecWithStack, arm64_norm, hsp, hx21]; rfl)
    (by omega) (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeVarintSlowSpecWithStack,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_vs hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSlowSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]; exact Entails.refl _) (by sep_focus)
  rcases hvs : varintSlow x.bs with _ | ⟨len, k⟩
  · dsimp only
    have hvar : decodeVarint x.bs = none := (varintSlow_none_iff x.bs).mp hvs
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 1#64 ∧ sf_vs.readReg64 .x1 ≠ 0#64⌝ ∗
        (decodeErrorAtStackLen A (sf_vs.readReg64 .x1) 0 ∗
          (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length)) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (164))
    wp_steps
    apply SepWP.fold (fold_slot_16 x.slot
      (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))
      (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
  · dsimp only
    obtain ⟨hk1, hkl, hvar⟩ := (varintSlow_some_iff x.bs len k).mp hvs
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 0#64 ∧ sf_vs.readReg64 .x1 = len⌝ ∗
        ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - k)) ∗
          (x.ptr ↦ₛ x.bs) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (224))
    wp_steps
    apply SepWP.fold (fold_sliceCursorAfter_drop x.slot x.ptr x.bs k hkl) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len (x.bs.drop k) hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by ac_rfl)

private theorem phase1_from_0x074_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A errStack).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmShimSpecGen errStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((rustAllocSpecWithStack A hStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + errStack)).inImage img))
    (hVarintSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecBMGen A errStack).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hne : x.bs ≠ [])
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h08c_exit := fun {s : State} (hpre : VarintSlicePre x.bs) =>
    @phase1_from_0x08c_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hVarintSlice hBytesFromVec
      hReserve hVtableSlot hVtableDrop x s0 s R hwt hbs_len hcapOk hpre
  have h398_exit := fun {s : State} =>
    @phase1_from_0x398_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hVarintSlow hBytesFromVec
      hReserve hVtableSlot hVtableDrop x s0 s R hwt hbs_len hcapOk
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  merge_fetches_H img.base H bytesMerge_fnOff 116 24
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym
    (mid := if (10#64).ult (BitVec.ofNat 64 x.bs.length) = true then entry + bv% (140) else entry + bv% (128))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  by_cases h11 : (10#64).ult (BitVec.ofNat 64 x.bs.length) = true
  · simp only [h11, ↓reduceIte] at hfl1 hsym1 ⊢
    have hge11 : 11 ≤ x.bs.length := by
      have : 10 < x.bs.length := by simpa [BitVec.ult, hbs_toNat] using h11
      omega
    have hpre : VarintSlicePre x.bs := Or.inl hge11
    exact h08c_exit hpre
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8, h11])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
      hfl1 hsym1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29])
  · have h11_eq : (10#64).ult (BitVec.ofNat 64 x.bs.length) = false := Bool.eq_false_iff.mpr h11
    simp only [h11_eq, Bool.false_eq_true, ↓reduceIte] at hfl1 hsym1 ⊢
    dsimp only [sliceCursorAt]
    rw [bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
    by_cases hlast : (x.bs.getLast hne).getLsbD 7 = true
    · have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = true := by
        revert hlast; generalize x.bs.getLast hne = b; revert b; apply BytesMergeFacts.bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (920))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hfl2 hsym2
      refine SepWPp.weaken_pre ?_ (h398_exit
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
        hfl2 hsym2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by ac_rfl)
    · have hlast_eq : (x.bs.getLast hne).getLsbD 7 = false := Bool.eq_false_iff.mpr hlast
      have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = false := by
        revert hlast_eq; generalize x.bs.getLast hne = b; revert b; apply BytesMergeFacts.bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (140))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hfl2 hsym2
      have hpre : VarintSlicePre x.bs := Or.inr ⟨hne, toNat_le_0x7f_of_getLsbD_7_false hlast_eq⟩
      refine SepWPp.weaken_pre ?_ (h08c_exit hpre
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
        hfl2 hsym2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by ac_rfl)


theorem bytes_merge_ok_of_contracts_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A errStack).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmShimSpecGen errStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((rustAllocSpecWithStack A hStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + errStack)).inImage img))
    (hVarintSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecBMGen A errStack).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName)
      (bytesMergeSpecGen A errStack reqCap img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp_align =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  rw [bytesMergeSpecGen, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hfl, hsym⟩, hpre⟩ := hpre
  rw [bytesMergeRawSpecGen, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpreB, hm⟩ := hpre
  obtain ⟨hw0, hx1, hx2, hbs_len, hcapOk⟩ := bmPreBound_elim hpreB
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_gen_some img A H errStack reqCap hbnd hdef x s0 s R w hw hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableSlot hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  have h074_exit := fun {s : State} (hwt : x.wt = .lengthDelimited) (hne : x.bs ≠ []) =>
    @phase1_from_0x074_gen img A H hStack errStack reqCap hbnd hres_le himg hdef hmc hshim halloc hpanic hVarintSlow hVarintSlice
      hBytesFromVec hReserve hVtableSlot hVtableDrop x s0 s R hwt hne hbs_len hcapOk
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  suffices hwp : _ by
    obtain ⟨sf, hsteps, hout⟩ := SepWPp.to_subroutineOutcome_gen hsp_align hm hL hwp
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMergeGen_entry s0.sp errStack hbnd]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  merge_fetches_H img.base H bytesMerge_fnOff 0 116
  merge_fetches_H img.base H bytesMerge_fnOff 244 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (36))
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    rcases hbs : x.bs with _ | ⟨b0, bs'⟩
    · have hmerge : mergeBytes x.wt x.bs = none := by rw [hbs]; exact mergeBytes_nil
      dsimp only [sliceCursorAt]
      refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
        (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
          (x.ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
      refine SepWPp.unfold_memRegion_216 fun w216 => ?_
      apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (248))
      wp_steps
      apply SepWP.fold (fold_slot_16 x.slot x.ptr 0#64) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hfl2 hsym2
      refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000001#64 (by simp [KindNoHeap]) hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
        hfl2 hsym2)
      rw [hbs]
      exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
    · have hbs_ne : x.bs ≠ [] := by simp [hbs]
      have hbs_len' : (b0 :: bs').length < 2 ^ 63 := by simpa [hbs] using bmLenBound_lt63 hbs_len
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs').length).toNat = (b0 :: bs').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hlen_ne0 : (BitVec.ofNat 64 (b0 :: bs').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      dsimp only [sliceCursorAt]
      rw [pointsToBytes_cons]
      by_cases hb0 : (b0.signExtend 64).getLsbD 63 = false
      · apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (64))
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hfl2 hsym2
        have hvar : decodeVarint x.bs = some (b0.signExtend 64, bs') := by
          rw [hbs]
          exact decodeVarint_cons_of_signExtend_63_false hb0
        apply SepWPp.bm_of_sepWP_inv hfl2 hsym2 (mid := entry + bv% (224))
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + 1#64)) ∗
            ((x.slot + 8#64) ↦₆₄ (BitVec.ofNat 64 (b0 :: bs').length - 1#64)) ∗
            (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
            sliceCursorAfter x.slot x.ptr x.bs bs' from by
          rw [hbs]
          exact fold_sliceCursorAfter_cons x.slot x.ptr b0 bs') (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hfl3 hsym3
        refine SepWPp.weaken_pre ?_ (h0e0_exit (b0.signExtend 64) bs' hwt hvar
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hfl3 hsym3
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by ac_rfl)
      · have hb0_eq : (b0.signExtend 64).getLsbD 63 = true :=
          Bool.eq_true_of_not_eq_false hb0
        apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (116))
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hfl2 hsym2
        apply SepWPp.fold (T' := sliceCursorAt x.slot x.ptr x.bs)
          (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bs').length) ∗
              (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
              sliceCursorAt x.slot x.ptr x.bs from by
            unfold sliceCursorAt
            rw [hbs, pointsToBytes_cons]
            exact Entails.of_eq (by ac_rfl)) (by sep_focus)
        refine SepWPp.weaken_pre ?_ (h074_exit hwt hbs_ne
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hfl2 hsym2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hbs])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (248))
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl1 hsym1
    refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hfl1 hsym1)
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)


end FnOffShield

theorem SepWPp.to_subroutineOutcome_x {prog : Program} {A : RustAlloc} {img : Obj.Image}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P (MergePostX A x s0 R) (MergePanicX A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (bytesMergeSpecX A img) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim


/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]` meets
`bytesMergeSpec A img` on any `libsignalSessionCode.rebase img.base H`. -/
theorem bytes_merge_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (decodeErrorFromSpec A))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      framelessMemcpySpec)
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      noAllocShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (rustAllocSpec A))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr varintSlowName)
      (decodeVarintSlowSpec A))
    (hVarintSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName)
      (bytesMergeSpec A img) :=
  bytes_merge_ok_of_contracts_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) himg
    (subroutine_ok_inImage_of_subroutine_ok img hdef)
    (bmMemcpy_inImage_of_frameless hmc)
    (bmShim_inImage_of_noAllocShim hshim)
    (subroutine_ok_inImage_of_subroutine_ok img halloc)
    hpanic
    (subroutine_ok_inImage_of_subroutine_ok img hVarintSlow)
    (subroutine_ok_inImage_of_subroutine_ok img hVarintSlice)
    hBytesFromVec
    (subroutine_ok_inImage_of_subroutine_ok img hReserve)
    hVtableSlot hVtableDrop

theorem bytes_merge_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts img.base A ext)
    (hDecodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hVarintSlow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      (decodeVarintSlowSpec A))
    (hVarintSlice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    BytesMergeOkExt img A ext :=
  bytes_merge_ok_of_contracts himg
    (sub_ok_at_of_fnAddr hDecodeErrorFrom bytesMergeName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.session_memcpy_region_ok_at bytesMergeName (num% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.shim_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.alloc_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (panic_at_handle_error_ext img.base ext bytesMergeName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableSlot hVtableDrop

theorem bytes_merge_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hDecodeErrorFrom : AllocHooks A abs)
    (hVarintSlow : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A))
    (hVarintSlice : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr decodeVarintSliceName)
      (decodeVarintSliceSpec A))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr doReserveName) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    BytesMergeOk img C A ctl abs := by
  have hAlloc := AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA
  exact bytes_merge_ok_of_contracts himg
    (decodeErrorFrom_ok_at_tripleRatchet (A := A) (b := img.base) (C := C) (ctl := ctl)
      (abs := abs) hDecodeErrorFrom (name := bytesMergeName) (k := num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.session_memcpy_region_ok_at bytesMergeName (num% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.shim_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (hAlloc.alloc_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    (panic_at_handle_error_ext img.base (tripleRatchetExterns C ctl abs) bytesMergeName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")))
    hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableSlot hVtableDrop


/-- `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]` meets
`bytesMergeSpecX A img` on any `libsignalSessionCode.rebase img.base H`. -/
theorem bytes_merge_ok_of_contracts_x {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (session2MemcpySpecBMX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (session2ShimSpecBMX.inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A varintSlowStackX).inImage img))
    (hVarintSlice : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecX A).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecX A).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName)
      (bytesMergeSpecX A img) :=
  bytes_merge_ok_of_contracts_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) himg
    hdef hmc hshim halloc hpanic hVarintSlow hVarintSlice hBytesFromVec hReserve
    hVtableSlot hVtableDrop

private theorem bm_decodeErrorFromSpecWithStack_inImage_mono {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustAlloc} {n m : Nat}
    (hnm : n ≤ m) (hm : m ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((decodeErrorFromSpecWithStack A n).inImage img)) :
    subroutine_ok prog entry ((decodeErrorFromSpecWithStack A m).inImage img) := by
  refine subroutine_ok_outcome_intro fun (p, w) R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt s0.sp m =
      memRegion (s0.sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt s0.sp n := by
    have h1 := stackAt_split_sub s0.sp (m - n) n (by omega)
    rwa [Nat.sub_add_cancel hnm] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 m) (m - n) ∗ R
  have hpre' : s0.mem ⊨ ((decodeErrorFromSpecWithStack A n).inImage img).pre (p, w) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome (p, w) R' s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hpreserve, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · refine Or.inl ⟨hret, hpreserve, ?_⟩
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited _hoom_post).elim

private theorem bm_decodeVarintSlowSpecWithStack_inImage_mono {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {A : RustAlloc} {n m : Nat}
    (hnm : n ≤ m) (hm : m ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((decodeVarintSlowSpecWithStack A n).inImage img)) :
    subroutine_ok prog entry ((decodeVarintSlowSpecWithStack A m).inImage img) := by
  refine subroutine_ok_outcome_intro fun (slotA, slot, ptr, bs) R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt s0.sp m =
      memRegion (s0.sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt s0.sp n := by
    have h1 := stackAt_split_sub s0.sp (m - n) n (by omega)
    rwa [Nat.sub_add_cancel hnm] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 m) (m - n) ∗ R
  have hpre' : s0.mem ⊨ ((decodeVarintSlowSpecWithStack A n).inImage img).pre (slotA, slot, ptr, bs) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome (slotA, slot, ptr, bs) R' s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hpreserve, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · refine Or.inl ⟨hret, hpreserve, ?_⟩
    dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack, R'] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited _hoom_post).elim

private theorem bm_shim_ok_at_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMergeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (session2ShimSpecBMX.inImage img) := by
  have h := hA.shim_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) decodeVarintSliceStackX (by decide) (by decide) (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionShimSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionShimSpec, session2ShimSpecBMX] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine (h.to_outcome x R s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem bm_memcpy_ok_at_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      (session2MemcpySpecBMX.inImage img) := by
  have h := hA.session_memcpy_region_ok_at bytesMergeName (num% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) decodeVarintSliceStackX (by decide) (by decide) (by fnoff_eq)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec decodeVarintSliceStackX).inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine (h.to_outcome x R s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, withStack, sessionMemcpyRegionSpec, memcpyRegionSpec, session2MemcpySpecBMX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem bytes_merge_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContractsX img A ext)
    (hDecodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A decodeErrorHookStackX).inImage img))
    (hVarintSlow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A varintSlowStackX).inImage img))
    (hVarintSlice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeVarintSliceName)
      ((decodeVarintSliceSpecX A).inImage img))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserveName) ((doReserveSpecX A).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img)) :
    BytesMergeOkExtX img A ext :=
  bytes_merge_ok_of_contracts_x himg
    (sub_ok_at_of_fnAddr (bm_decodeErrorFromSpecWithStack_inImage_mono (m := decodeErrorHookStackX) (by decide) (by decide) hDecodeErrorFrom) bytesMergeName (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) (by fnoff_eq))
    (bm_memcpy_ok_at_ext_x hAlloc)
    (bm_shim_ok_at_ext_x hAlloc)
    (hAlloc.alloc_ok_at bytesMergeName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) (by fnoff_eq))
    (panic_at_handle_error_ext img.base ext bytesMergeName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) (by fnoff_eq))
    (bm_decodeVarintSlowSpecWithStack_inImage_mono (by decide) (by decide) hVarintSlow)
    hVarintSlice hBytesFromVec hReserve hVtableSlot hVtableDrop

/-! ## Relocatable `[LibsignalPlacement]` Phase 1 and `bytes_merge_placed_ok` -/

theorem SepWPp.to_subroutineOutcome_placed_gen [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {errStack : Nat} {reqCap : Bool}
    {x : BytesMergeGhost} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecGen A errStack reqCap)) x R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem phase1_from_0x08c_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A hStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) ((withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48)))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpre : VarintSlicePre x.bs)
    (hpc : s.pc = (blkPl_7).base + 140#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_err_0x0a4_placed_gen _ A H errStack reqCap hbnd x s0 s R hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAt] at hpc hVarintSlice herr_exit h0e0_exit ⊢
  rw [memRegion_48_sret24 (s0.sp - 216#64)]
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 76)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := ({ ret := s0.sp - 216#64, ptr := x.ptr, bs := x.bs } : DecodeVarintSliceGhost))
    (T := memRegion (s0.sp - 216#64) 24 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hVarintSlice hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen, arm64_norm, hsp]; rfl)
    (by exact ⟨by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1],
               by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8, hbs_toNat],
               bmLenBound_lt63 hbs_len, hpre⟩)
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeVarintSliceSpecBMGen,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSliceSpecBMGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  rcases hvar : decodeVarint x.bs with _ | ⟨len, rest0⟩
  · dsimp only [varintSliceResultAt]
    refine SepWPp.weaken_pre (P' :=
      (∃∗ e : BitVec 64, ⌜e ≠ 0#64⌝ ∗ ((s0.sp - 216#64 + 8#64) ↦₆₄ e) ∗ decodeErrorAtStackLen A e 0) ∗
        (((s0.sp - 216#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 216#64 + 16#64) 8 ∗
          (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - 224#64) 8 ∗ memRegion (s0.sp - 216#64 + 24#64) 24 ∗
          memRegion (s0.sp - 168#64) 104 ∗ savedRegsStack s0.sp s0))
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun e => ?_
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun he => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (164))
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_err (s0.sp - 216#64) 1#64 e) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact he)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
  · dsimp only [varintSliceResultAt]
    have hrest0_le : rest0.length ≤ x.bs.length := by
      obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
      rw [hpfx, List.length_append]
      omega
    have hcons_toNat : (BitVec.ofNat 64 (x.bs.length - rest0.length)).toNat = x.bs.length - rest0.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hult_cons : (BitVec.ofNat 64 x.bs.length).ult (BitVec.ofNat 64 (x.bs.length - rest0.length)) = false := by
      simp [BitVec.ult, hbs_toNat, hcons_toNat]
    have hule_cons : (BitVec.ofNat 64 (x.bs.length - rest0.length)).ule (BitVec.ofNat 64 x.bs.length) = true := by
      simp [BitVec.ule, hbs_toNat, hcons_toNat]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (224))
    wp_steps
    apply SepWP.fold (fold_memRegion_48_sret_ok (s0.sp - 216#64) 0#64 len
      (BitVec.ofNat 64 (x.bs.length - rest0.length))) (by sep_focus)
    apply SepWP.fold (fold_sliceCursorAfter_from_consumed x.slot x.ptr x.bs rest0 hrest0_le) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len rest0 hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hult_cons, hule_cons])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by ac_rfl)

private theorem phase1_from_0x398_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A hStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecWithStack A (64 + errStack))))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 920#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = x.bufRef)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have herr_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_err_0x0a4_placed_gen _ A H errStack reqCap hbnd x s0 s R hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAt] at hpc hVarintSlow herr_exit h0e0_exit ⊢
  rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 293)
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := (x.bufRef, x.slot, x.ptr, x.bs))
    (T := (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      (x.ptr ↦ₛ x.bs) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (64 + errStack))
    hVarintSlow hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [decodeVarintSlowSpecWithStack, arm64_norm, hsp, hx21]; rfl)
    (by omega) (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      simp only [bytesMergeRawSpecGen, decodeVarintSlowSpecWithStack,
        State.trace_setPC, State.trace_writeReg64, allocFailedIn, htrace] at hm ⊢
      exact allowPanic_frame id hm) ?_
  intro sf_vs hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx21, hx29] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [decodeVarintSlowSpecWithStack, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun htr => ?_
  apply SepWPp.fold (T' := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    (by rw [stackAt_sliceGen_split s0.sp errStack (64 + errStack) (by dsimp [bmSliceStack]; omega) hbnd]; exact Entails.refl _) (by sep_focus)
  rcases hvs : varintSlow x.bs with _ | ⟨len, k⟩
  · dsimp only
    have hvar : decodeVarint x.bs = none := (varintSlow_none_iff x.bs).mp hvs
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_of_decodeVarint_none hvar
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 1#64 ∧ sf_vs.readReg64 .x1 ≠ 0#64⌝ ∗
        (decodeErrorAtStackLen A (sf_vs.readReg64 .x1) 0 ∗
          (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length)) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (164))
    wp_steps
    apply SepWP.fold (fold_slot_16 x.slot
      (x.ptr + BitVec.ofNat 64 (min 10 x.bs.length))
      (BitVec.ofNat 64 (x.bs.length - min 10 x.bs.length))) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (herr_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm]; exact hx1_sf)
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self]))
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
  · dsimp only
    obtain ⟨hk1, hkl, hvar⟩ := (varintSlow_some_iff x.bs len k).mp hvs
    refine SepWPp.weaken_pre (P' :=
      ⌜sf_vs.readReg64 .x0 = 0#64 ∧ sf_vs.readReg64 .x1 = len⌝ ∗
        ((x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 k)) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - k)) ∗
          (x.ptr ↦ₛ x.bs) ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 216#64) 48 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.pure_elim fun ⟨hx0_sf, hx1_sf⟩ => ?_
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (224))
    wp_steps
    apply SepWP.fold (fold_sliceCursorAfter_drop x.slot x.ptr x.bs k hkl) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (h0e0_exit len (x.bs.drop k) hvar
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, hx0_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1_sf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
    exact Entails.of_eq (by ac_rfl)

private theorem phase1_from_0x074_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A hStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecWithStack A (64 + errStack))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    (hwt : x.wt = .lengthDelimited)
    (hne : x.bs ≠ [])
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx1 : s.readReg64 .x1 = x.ptr)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 x.bs.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hbs_toNat : (BitVec.ofNat 64 x.bs.length).toNat = x.bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h08c_exit := fun {s : State} (hpre : VarintSlicePre x.bs) =>
    @phase1_from_0x08c_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hVarintSlice hBytesFromVec
      hReserve hVtableDrop x s0 s R hwt hbs_len hcapOk hpre
  have h398_exit := fun {s : State} =>
    @phase1_from_0x398_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hVarintSlow hBytesFromVec
      hReserve hVtableDrop x s0 s R hwt hbs_len hcapOk
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if (10#64).ult (BitVec.ofNat 64 x.bs.length) = true then (blkPl_7).base + bv% (140) else (blkPl_7).base + bv% (128))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases h11 : (10#64).ult (BitVec.ofNat 64 x.bs.length) = true
  · simp only [h11, ↓reduceIte] at hcl1 hro1 ⊢
    have hge11 : 11 ≤ x.bs.length := by
      have : 10 < x.bs.length := by simpa [BitVec.ult, hbs_toNat] using h11
      omega
    have hpre : VarintSlicePre x.bs := Or.inl hge11
    exact h08c_exit hpre
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx8, h11])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl1 hro1
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29])
  · have h11_eq : (10#64).ult (BitVec.ofNat 64 x.bs.length) = false := Bool.eq_false_iff.mpr h11
    simp only [h11_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    dsimp only [sliceCursorAt]
    rw [bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
    by_cases hlast : (x.bs.getLast hne).getLsbD 7 = true
    · have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = true := by
        revert hlast; generalize x.bs.getLast hne = b; revert b; apply BytesMergeFacts.bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (920))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (h398_exit
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by ac_rfl)
    · have hlast_eq : (x.bs.getLast hne).getLsbD 7 = false := Bool.eq_false_iff.mpr hlast
      have hlast31 : (((x.bs.getLast hne).signExtend 32).zeroExtend 64).getLsbD 31 = false := by
        revert hlast_eq; generalize x.bs.getLast hne = b; revert b; apply BytesMergeFacts.bitvec8_forall; decide
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (140))
      wp_steps
      apply SepWP.fold (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (x.ptr ↦ₛ x.bs.dropLast) ∗
          ((x.ptr + BitVec.ofNat 64 x.bs.length + 0xffffffffffffffff#64) ↦₈ x.bs.getLast hne) ⊢
          sliceCursorAt x.slot x.ptr x.bs from by
        unfold sliceCursorAt
        rw [← bm_pointsToBytes_split_last x.ptr x.bs hne (bmLenBound_lt63 hbs_len)]
        exact Entails.of_eq (by ac_rfl)) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      have hpre : VarintSlicePre x.bs := Or.inr ⟨hne, toNat_le_0x7f_of_getLsbD_7_false hlast_eq⟩
      refine SepWPp.weaken_pre ?_ (h08c_exit hpre
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx1, hx8, h11_eq, hlast31])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_0, h26_0, h27_0, h28_0, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx8])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by ac_rfl)

theorem bytes_merge_placed_ok_of_contracts_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A errStack)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen errStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A hStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecWithStack A (64 + errStack))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecBMGen A errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length))) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecGen A errStack reqCap)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp_align =>
    reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMergeRawSpecGen, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpreB, hm⟩ := hpre
  obtain ⟨hw0, hx1, hx2, hbs_len, hcapOk⟩ := bmPreBound_elim hpreB
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hde_exit := fun (w : BitVec 64) (hw : KindNoHeap w) {s : State}
      (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_placed_gen _ A H errStack reqCap hbnd hdef x s0 s R w hw hmerge
  have h0e0_exit := fun (len : BitVec 64) (rest0 : List (BitVec 8)) {s : State}
      (hwt : x.wt = .lengthDelimited)
      (hvar : decodeVarint x.bs = some (len, rest0)) =>
    @BytesMergeFacts.phase2_from_0x0e0_export_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hBytesFromVec hReserve
      hVtableDrop x s0 s R len rest0 hwt hvar hbs_len hcapOk
  have h074_exit := fun {s : State} (hwt : x.wt = .lengthDelimited) (hne : x.bs ≠ []) =>
    @phase1_from_0x074_placed_gen _ A H hStack errStack reqCap hbnd hres_le hdef hmc hshim halloc hpanic hVarintSlow hVarintSlice
      hBytesFromVec hReserve hVtableDrop x s0 s R hwt hne hbs_len hcapOk
  clear hVarintSlow hVarintSlice hBytesFromVec hReserve hVtableDrop
  suffices hwp : _ by
    obtain ⟨sf, hsteps, hout⟩ := SepWPp.to_subroutineOutcome_placed_gen hsp_align hm hL hwp
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  rw [stackAt_bytesMergeGen_entry s0.sp errStack hbnd]
  refine SepWPp.weaken_pre (P' := cells (s0.sp - 64#64) 8 ∗
    (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.unfold_cells_64 fun c0 c1 c2 c3 c4 c5 c6 c7 => ?_
  by_cases hwt : x.wt = .lengthDelimited
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = false
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0, hwt]
      decide
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (36))
    wp_steps
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    rcases hbs : x.bs with _ | ⟨b0, bs'⟩
    · have hmerge : mergeBytes x.wt x.bs = none := by rw [hbs]; exact mergeBytes_nil
      dsimp only [sliceCursorAt]
      refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
        (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
          (x.ptr ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗
          stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
          memRegion (s0.sp - 224#64) 8 ∗
          memRegion (s0.sp - 168#64) 104 ∗
          savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
      refine SepWPp.unfold_memRegion_216 fun w216 => ?_
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (248))
      wp_steps
      apply SepWP.fold (fold_slot_16 x.slot x.ptr 0#64) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000001#64 (by simp [KindNoHeap]) hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
        hcl2 hro2)
      rw [hbs]
      exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm]; ac_rfl)
    · have hbs_ne : x.bs ≠ [] := by simp [hbs]
      have hbs_len' : (b0 :: bs').length < 2 ^ 63 := by simpa [hbs] using bmLenBound_lt63 hbs_len
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs').length).toNat = (b0 :: bs').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hlen_ne0 : (BitVec.ofNat 64 (b0 :: bs').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      dsimp only [sliceCursorAt]
      rw [pointsToBytes_cons]
      by_cases hb0 : (b0.signExtend 64).getLsbD 63 = false
      · apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (64))
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl2 hro2
        have hvar : decodeVarint x.bs = some (b0.signExtend 64, bs') := by
          rw [hbs]
          exact decodeVarint_cons_of_signExtend_63_false hb0
        apply SepWPp.bm_of_sepWP_lscl hcl2 hro2 (mid := (blkPl_7).base + bv% (224))
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + 1#64)) ∗
            ((x.slot + 8#64) ↦₆₄ (BitVec.ofNat 64 (b0 :: bs').length - 1#64)) ∗
            (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
            sliceCursorAfter x.slot x.ptr x.bs bs' from by
          rw [hbs]
          exact fold_sliceCursorAfter_cons x.slot x.ptr b0 bs') (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl3 hro3
        refine SepWPp.weaken_pre ?_ (h0e0_exit (b0.signExtend 64) bs' hwt hvar
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hcl3 hro3
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by ac_rfl)
      · have hb0_eq : (b0.signExtend 64).getLsbD 63 = true :=
          Bool.eq_true_of_not_eq_false hb0
        apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (116))
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        intro hcl2 hro2
        apply SepWPp.fold (T' := sliceCursorAt x.slot x.ptr x.bs)
          (show (x.slot ↦₆₄ x.ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bs').length) ∗
              (x.ptr ↦₈ b0) ∗ ((x.ptr + 1#64) ↦ₛ bs') ⊢
              sliceCursorAt x.slot x.ptr x.bs from by
            unfold sliceCursorAt
            rw [hbs, pointsToBytes_cons]
            exact Entails.of_eq (by ac_rfl)) (by sep_focus)
        refine SepWPp.weaken_pre ?_ (h074_exit hwt hbs_ne
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx2, hw0_br, hlen_ne0, hb0_eq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
          hcl2 hro2
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx2])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hbs])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx1])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm]))
        exact Entails.of_eq (by ac_rfl)
  · have hw0_br :
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      change (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 .x0)) &&& 255#64) != 2#32) = true
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, hw0]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_ne_lengthDelimited hwt
    dsimp only [sliceCursorAt]
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (((s0.sp - 64#64) ↦₆₄ c0) ∗ ((s0.sp - 56#64) ↦₆₄ c1) ∗
        ((s0.sp - 48#64) ↦₆₄ c2) ∗ ((s0.sp - 40#64) ↦₆₄ c3) ∗
        ((s0.sp - 32#64) ↦₆₄ c4) ∗ ((s0.sp - 24#64) ↦₆₄ c5) ∗
        ((s0.sp - 16#64) ↦₆₄ c6) ∗ ((s0.sp - 8#64) ↦₆₄ c7) ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ (x.slot ↦₆₄ x.ptr) ∗
        ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216_invalidWireType fun w0_216 b0_216 b1_216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).base + bv% (248))
    wp_steps
    apply SepWP.fold (fold_memRegion_40_bytes (s0.sp - 216#64)
      (BitVec.ofNat 8 x.wt.toNat) 2#8) (by sep_focus)
    apply SepWP.fold (fold_slot_16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (show
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
        savedRegsStack s0.sp s0 from Entails.refl _) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl1 hro1
    refine SepWPp.weaken_pre ?_ (hde_exit 0x8000000000000006#64 (by simp [KindNoHeap]) hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hw0_br, hw0, mask_ff_32_of_setWidth8])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, and_self])
      hcl1 hro1)
    exact Entails.of_eq (by dsimp only [savedRegsStack]; simp (config := { decide := true }) only [arm64_norm]; ac_rfl)

theorem bytes_merge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpec A)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen decodeErrorHookStack)))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl (bmShimSpecGen decodeErrorHookStack)))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpec A)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpec A)))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpec A)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) (withLsCl lsmpl (doReserveSpec A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpec A tmpPtr v v.length))) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A)) :=
  bytes_merge_placed_ok_of_contracts_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) hdef hmc hshim halloc hpanic hVarintSlow hVarintSlice
    hBytesFromVec hReserve hVtableDrop

theorem bytes_merge_placed_ok_of_contracts_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdef : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromSpecWithStack A decodeErrorHookStackX)))
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl session2MemcpySpecBMX))
    (hshim : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustNoAllocShimSym)
      (withLsCl lsmpl session2ShimSpecBMX))
    (halloc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ lsRustAllocSym)
      (withLsCl lsmpl (rustAllocSpecWithStack A extHookStack)))
    (hpanic : ((blkPC_7).rebase (blkPl_7).base H).externAt?
      ((blkPl_7).ρ lsHandleErrorSym) =
      some Rust.panicked)
    (hVarintSlow : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecWithStack A (64 + decodeErrorHookStackX))))
    (hVarintSlice : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecX A)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13) (withLsCl lsmpl (doReserveSpecX A)))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecX A tmpPtr v v.length))) :
    subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (blkPl_7).base
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A)) :=
  bytes_merge_placed_ok_of_contracts_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) hdef hmc hshim halloc hpanic hVarintSlow hVarintSlice
    hBytesFromVec hReserve hVtableDrop

end CryptoVerification.LibsignalTripleRatchet.Prost
