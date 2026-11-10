/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Bytes.BytesCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Phases 2 and 3 of `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`

Verifies Phase 2 (length check, `BytesMut::with_capacity`, `memcpy`, `bytes::from_vec`) and
Phase 3 (`Vec::clear`, `Vec::reserve`, `memcpy`, `vtable.drop`) for
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]>`.
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bytesMerge_fnOff
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero

/-! ## Phase 3: `Vec::clear`, `Vec::reserve`, `memcpy`, and `vtable.drop` -/

private theorem decodeVarintAux_length_lt (i : Nat) (acc : BitVec 64) (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h
        simp; omega

private theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩
    rw [hvar] at h
    dsimp only at h
    split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega


theorem fold_vecU8At_sp136 (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((sp0 - 136#64) ↦₆₄ cap) ∗ ((sp0 - 128#64) ↦₆₄ ptr) ∗
      ((sp0 - 120#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      bm_vecU8Buf A cap ptr bs ⊢
      vecU8At A (sp0 - 136#64) cap ptr bs := by
  rw [bm_vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  have e1 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  have e2 : sp0 - 136#64 + 16#64 = sp0 - 120#64 := by bv_omega
  rw [e1, e2, sepConj_assoc, sepConj_assoc]
  exact Entails.refl _

theorem unfold_vecHeader_sp136 (sp0 cap ptr len : BitVec 64) :
    vecHeader (sp0 - 136#64) cap ptr len =
      ((sp0 - 136#64) ↦₆₄ cap) ∗ ((sp0 - 128#64) ↦₆₄ ptr) ∗ ((sp0 - 120#64) ↦₆₄ len) := by
  dsimp only [vecHeader]
  have e1 : sp0 - 136#64 + 8#64 = sp0 - 128#64 := by bv_omega
  have e2 : sp0 - 136#64 + 16#64 = sp0 - 120#64 := by bv_omega
  rw [e1, e2]

theorem unfold_bytesAt_sp112 (A : RustAlloc) (b sp0 ptr : BitVec 64) (bs : List (BitVec 8)) :
    bytesAt A b (sp0 - 112#64) ptr bs =
      ((sp0 - 112#64) ↦₆₄ bytesVtable b ptr bs.length) ∗
      ((sp0 - 104#64) ↦₆₄ bytesPtr ptr bs.length) ∗
      ((sp0 - 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp0 - 88#64) ↦₆₄ bytesData ptr bs.length) ∗
      bytesBoxU8Buf A ptr bs := by
  dsimp only [bytesAt, bytesHeader]
  have e1 : sp0 - 112#64 + 8#64 = sp0 - 104#64 := by bv_omega
  have e2 : sp0 - 112#64 + 16#64 = sp0 - 96#64 := by bv_omega
  have e3 : sp0 - 112#64 + 24#64 = sp0 - 88#64 := by bv_omega
  rw [e1, e2, e3, sepConj_assoc, sepConj_assoc, sepConj_assoc]


/-! ## Phase 2: length check and `copy_to_bytes` -/

theorem decodeVarintAux_suffix (i : Nat) (acc : BitVec 64) (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) :
    ∃ pfx, bs = pfx ++ rest0 := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact ⟨[b], rfl⟩
    · split at h
      · contradiction
      · obtain ⟨pfx, rfl⟩ := ih _ _ h
        exact ⟨b :: pfx, rfl⟩

theorem bm_decodeVarint_suffix {bs rest0 : List (BitVec 8)} {len : BitVec 64}
    (h : decodeVarint bs = some (len, rest0)) :
    ∃ pfx, bs = pfx ++ rest0 :=
  decodeVarintAux_suffix 0 0 bs rest0 len h

theorem mergeBytes_lengthDelimited_underflow {wt : WireType} {bs rest0 : List (BitVec 8)} {len : BitVec 64}
    (hwt : wt = .lengthDelimited) (hvar : decodeVarint bs = some (len, rest0))
    (hult : rest0.length < len.toNat) :
    mergeBytes wt bs = none := by
  subst hwt
  simp [mergeBytes, hvar, hult]

theorem mergeBytes_lengthDelimited_ok {wt : WireType} {bs rest0 : List (BitVec 8)} {len : BitVec 64}
    (hwt : wt = .lengthDelimited) (hvar : decodeVarint bs = some (len, rest0))
    (hle : len.toNat ≤ rest0.length) :
    mergeBytes wt bs = some (rest0.take len.toNat, rest0.drop len.toNat) := by
  subst hwt
  have hnot : ¬ (rest0.length < len.toNat) := by omega
  simp [mergeBytes, hvar, hnot]

theorem vecU8Buf_nil_one (A : RustAlloc) :
    emp ⊢ bm_vecU8Buf A (BitVec.ofNat 64 ([] : List (BitVec 8)).length) 1#64 [] := by
  unfold bm_vecU8Buf
  simp only [List.length_nil, BitVec.toNat_ofNat, Nat.zero_mod,
    le_refl, ↓reduceIte]
  exact Entails.pure_right ⟨ trivial, by decide, by decide ⟩ (Entails.refl _)

theorem sliceCursorAfter_to_err (slot ptr : BitVec 64) (bs rest0 : List (BitVec 8)) :
    sliceCursorAfter slot ptr bs rest0 ⊢ memRegion slot 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAfter
  rw [← sepConj_assoc]
  exact sepConj_mono_left (fold_slot_16 slot _ _)

theorem sliceCursorAfter_split_copy (slot ptr : BitVec 64) (bs pfx rest0 : List (BitVec 8))
    (n : Nat) (hpfx : bs = pfx ++ rest0) (_hle : n ≤ rest0.length) :
    let v := rest0.take n
    let rest := rest0.drop n
    let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest0.length)
    sliceCursorAfter slot ptr bs rest0 =
      ((slot ↦₆₄ ptr1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗
        (ptr ↦ₛ pfx) ∗ (ptr1 ↦ₛ v) ∗ ((ptr1 + BitVec.ofNat 64 v.length) ↦ₛ rest)) := by
  dsimp only [sliceCursorAfter]
  have hpfx_len : bs.length - rest0.length = pfx.length := by
    rw [hpfx, List.length_append, Nat.add_sub_cancel]
  have hrest0 : rest0 = rest0.take n ++ rest0.drop n := (List.take_append_drop n rest0).symm
  have hbs_eq : bs = pfx ++ (rest0.take n ++ rest0.drop n) := by
    rw [← hrest0, hpfx]
  conv =>
    lhs
    rw [hbs_eq, pointsToBytes_append, pointsToBytes_append]
  rw [← hbs_eq, hpfx_len]

theorem sliceCursorAfter_advance_fold (slot ptr : BitVec 64) (bs pfx rest0 : List (BitVec 8))
    (n : Nat) (hpfx : bs = pfx ++ rest0) (hle : n ≤ rest0.length) (hbs : bs.length < 2 ^ 63) :
    let v := rest0.take n
    let rest := rest0.drop n
    let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest0.length)
    ((slot ↦₆₄ (ptr1 + BitVec.ofNat 64 v.length)) ∗
      ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 rest0.length - BitVec.ofNat 64 v.length)) ∗
      (ptr ↦ₛ pfx) ∗ (ptr1 ↦ₛ v) ∗ ((ptr1 + BitVec.ofNat 64 v.length) ↦ₛ rest)) ⊢
      sliceCursorAfter slot ptr bs rest := by
  dsimp only [sliceCursorAfter]
  have hpfx_len : bs.length - rest0.length = pfx.length := by
    rw [hpfx, List.length_append, Nat.add_sub_cancel]
  have hv_len : (rest0.take n).length = n := List.length_take_of_le hle
  have hrest_len : (rest0.drop n).length = rest0.length - n := List.length_drop
  have hbs_len : bs.length = pfx.length + rest0.length := by rw [hpfx, List.length_append]
  have hsub_len : bs.length - (rest0.drop n).length = (bs.length - rest0.length) + (rest0.take n).length := by
    omega
  have hptr_eq :
      ptr + BitVec.ofNat 64 (bs.length - rest0.length) + BitVec.ofNat 64 (rest0.take n).length =
        ptr + BitVec.ofNat 64 (bs.length - (rest0.drop n).length) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hsub_len]
  have hrem_eq :
      BitVec.ofNat 64 rest0.length - BitVec.ofNat 64 (rest0.take n).length =
        BitVec.ofNat 64 (rest0.drop n).length := by
    rw [hv_len, hrest_len]
    apply BitVec.eq_of_toNat_eq
    have h1 : rest0.length < 2 ^ 64 := by omega
    have h2 : n < 2 ^ 64 := by omega
    have h3 : rest0.length - n < 2 ^ 64 := by omega
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3]
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]
      omega
  have hrest0 : rest0 = rest0.take n ++ rest0.drop n := (List.take_append_drop n rest0).symm
  have hbs_eq : bs = pfx ++ (rest0.take n ++ rest0.drop n) := by rw [← hrest0, hpfx]
  have hpts : (ptr ↦ₛ bs) =
      (ptr ↦ₛ pfx) ∗ ((ptr + BitVec.ofNat 64 (bs.length - rest0.length)) ↦ₛ rest0.take n) ∗
        ((ptr + BitVec.ofNat 64 (bs.length - rest0.length) + BitVec.ofNat 64 (rest0.take n).length) ↦ₛ rest0.drop n) := by
    conv => lhs; rw [hbs_eq, pointsToBytes_append, pointsToBytes_append]
    rw [← hpfx_len, ← sepConj_assoc]
  rw [← hpts, hptr_eq, hrem_eq]
  exact Entails.refl _

theorem fold_vecU8Buf_nonempty (A : RustAlloc) (tmpPtr : BitVec 64)
    (v : List (BitVec 8)) (hpos : 0 < v.length) (hv_len : v.length < 2 ^ 63)
    (htmp : tmpPtr ≠ 0#64) :
    A.live tmpPtr v.length 1 ∗ (tmpPtr ↦ₛ v) ⊢
      bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v := by
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 v.length ≠ 0#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat, BitVec.toNat_ofNat, Nat.zero_mod] at h2
    omega
  unfold bm_vecU8Buf
  simp only [hlen_toNat, hcap_ne, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨le_refl _, by omega, htmp⟩ (Entails.refl _)

@[arm64_norm, local simp]
theorem bitvec_ult_33bits_of_lt32 {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ult 0x200000000#64 = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

@[arm64_norm, local simp]
theorem bitvec_msb_false_of_lt32 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  exact Nat.testBit_lt_two_pow (by omega)

@[arm64_norm, local simp]
theorem bitvec_getLsbD_63_of_lt32 {n : Nat} (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false :=
  bitvec_msb_false_of_lt32 hn

@[arm64_norm, local simp]
theorem bitvec_ult_self (w : BitVec 64) : w.ult w = false :=
  ProofLib.bitvec_ult_self w

@[arm64_norm, local simp]
theorem bitvec_sub_self_64 (w : BitVec 64) : w - w = 0#64 :=
  BitVec.sub_self w

@[arm64_norm, local simp]
theorem bitvec_if_zero_ult_self (d : BitVec 64) :
    (if (0#64).ult d = true then 0#64 else d) = 0#64 := by
  by_cases h : (0#64).ult d = true
  · simp [h]
  · simp only [h, ↓reduceIte]
    have h0 : d.toNat = 0 := by simp [BitVec.ult] at h; omega
    exact BitVec.eq_of_toNat_eq h0


theorem SepWPp.unfold_memRegion_216 {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ w : BitVec 64, SepWPp prog ret s
      (((sp0 - 216#64) ↦₆₄ w) ∗ memRegion (sp0 - 216#64 + 8#64) 40 ∗ P) Q Qp) :
    SepWPp prog ret s (memRegion (sp0 - 216#64) 48 ∗ P) Q Qp := by
  rw [memRegion_48_simple (sp0 - 216#64), sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  rw [sepConj_assoc]
  exact h w

theorem SepWPp.unfold_cell_sub {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {off k : Nat} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h1 : 8 < off := by decide) (h2 : off < 2 ^ 64 := by decide)
    (h : ∀ w : BitVec 64, SepWPp prog ret s
      (cells (sp0 - BitVec.ofNat 64 (off - 8)) k ∗ ((sp0 - BitVec.ofNat 64 off) ↦₆₄ w) ∗ P) Q Qp) :
    SepWPp prog ret s (cells (sp0 - BitVec.ofNat 64 off) (k + 1) ∗ P) Q Qp := by
  rw [cells_sub_succ sp0 off k h1 h2, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w => ?_
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (h w)

theorem SepWPp.unfold_memRegion_168 {prog : Program} {ret : BitVec 64} {s : State}
    {sp0 : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64, SepWPp prog ret s
      (((sp0 - 168#64) ↦₆₄ w0) ∗ ((sp0 - 160#64) ↦₆₄ w1) ∗
        ((sp0 - 152#64) ↦₆₄ w2) ∗ ((sp0 - 144#64) ↦₆₄ w3) ∗
        ((sp0 - 136#64) ↦₆₄ w4) ∗ ((sp0 - 128#64) ↦₆₄ w5) ∗
        ((sp0 - 120#64) ↦₆₄ w6) ∗
        memRegion (sp0 - 112#64) 32 ∗
        ((sp0 - 80#64) ↦₆₄ w80) ∗ memRegion (sp0 - 72#64) 8 ∗ P) Q Qp) :
    SepWPp prog ret s (memRegion (sp0 - 168#64) 104 ∗ P) Q Qp := by
  rw [memRegion_104_unfold sp0, sepConj_assoc, sepConj_assoc]
  refine SepWPp.unfold_cell_sub (off := 168) (k := 6) (h := fun w0 => ?_)
  refine SepWPp.unfold_cell_sub (off := 160) (k := 5) (h := fun w1 => ?_)
  refine SepWPp.unfold_cell_sub (off := 152) (k := 4) (h := fun w2 => ?_)
  refine SepWPp.unfold_cell_sub (off := 144) (k := 3) (h := fun w3 => ?_)
  refine SepWPp.unfold_cell_sub (off := 136) (k := 2) (h := fun w4 => ?_)
  refine SepWPp.unfold_cell_sub (off := 128) (k := 1) (h := fun w5 => ?_)
  refine SepWPp.unfold_cell_sub (off := 120) (k := 0) (h := fun w6 => ?_)
  rw [cells_zero, emp_sepConj]
  refine SepWPp.weaken_pre (P' := (∃∗ w80 : BitVec 64, ((sp0 - 80#64) ↦₆₄ w80) ∗ memRegion (sp0 - 72#64) 8) ∗
    (((sp0 - 168#64) ↦₆₄ w0) ∗ ((sp0 - 160#64) ↦₆₄ w1) ∗
      ((sp0 - 152#64) ↦₆₄ w2) ∗ ((sp0 - 144#64) ↦₆₄ w3) ∗
      ((sp0 - 136#64) ↦₆₄ w4) ∗ ((sp0 - 128#64) ↦₆₄ w5) ∗
      ((sp0 - 120#64) ↦₆₄ w6) ∗ memRegion (sp0 - 112#64) 32 ∗ P))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun w80 => ?_
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (h w0 w1 w2 w3 w4 w5 w6 w80)


abbrev bmLenBound (reqCap : Bool) (n : Nat) : Prop :=
  match reqCap with
  | true => n < 2 ^ 63
  | false => n < 2 ^ 62

theorem bmLenBound_lt63 {reqCap : Bool} {n : Nat} (h : bmLenBound reqCap n) : n < 2 ^ 63 := by
  cases reqCap <;> omega

theorem bm_reserveCap_bound (reqCap : Bool) {cap : BitVec 64} {vLen restLen bsLen : Nat}
    (h : bmCapCond reqCap cap bsLen) (hult : cap.toNat < vLen)
    (hsum : 1 + vLen + restLen ≤ bsLen) (hbs : bmLenBound reqCap bsLen) :
    reserveCap cap.toNat 0 vLen ≤ 9223372036854775807 := by
  cases reqCap
  · dsimp only [bmLenBound] at hbs
    dsimp [reserveCap]
    omega
  · exact bytesMergeCapOk_reserveCap_bound h hult hsum hbs

theorem bmShim_inImage_of_noAllocShim {img : Obj.Image} {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr ((bmShimSpecGen errStack).inImage img) := by
  apply subroutine_ok_inImage_of_subroutine_ok img
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, noAllocShimSpec, bmShimSpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem epilogue_decodeErrorFrom_gen_some {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)} {errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hdef : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((decodeErrorFromSpecWithStack A errStack).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp} {w : BitVec 64}
    (hw : KindNoHeap w) (hmerge : mergeBytes x.wt x.bs = none)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 224#64) (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace) (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 216#64) ↦₆₄ w) ∗ memRegion (s0.sp - 216#64 + 8#64) 40 ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) :=
  epilogue_decodeErrorFrom_gen (oimg := some img) (errStack := errStack) (reqCap := reqCap)
    hbnd hdef hw hmerge hpc hrun hsp hsp_align htrace hhigh ⟨hfl, hsym⟩

section FnOffShield
attribute [local irreducible] _root_.Arm64.Program.fnOff

private theorem mergePanicGen_of_allocFailed {errStack : Nat} {reqCap : Bool} {A : RustAlloc}
    {x : BytesMergeGhost} {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpecGen A errStack reqCap).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpecGen, allocFailedIn] at hm ⊢
  rw [htr] at hm
  exact allowPanic_frame id hm

private theorem phase3_from_0x294_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 660#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesVtable img.base tmpPtr v.length) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hReserve' : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((doReserveSpecWithStack A (hStack + 48)).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMergeName) (callee := doReserveName) (k := bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))]
    exact hReserve
  clear hReserve
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hp3 := fun (cap' ptr' : BitVec 64) {s : State}
      (hcapOk' : bmCapCond reqCap cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x2b4_gen img A H hStack errStack reqCap hbnd (by omega) himg hmc hVtableSlot x s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A x.valPtr x.valCap x.valBuf x.valBs]
  merge_fetches_H img.base H bytesMerge_fnOff 660 32
  merge_fetches_H img.base H bytesMerge_fnOff 800 52
  dsimp only [vecHeader] at hpc hReserve' hp3 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then entry + bv% (800) else entry + bv% (676))
  wp_steps
  apply SepWP.fold (fold_vecU8At_clear A x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hfl1 hsym1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound : reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bm_reserveCap_bound reqCap hcapOk hcap_lt hsum hbs_len
    have hcapOk' : bmCapCond reqCap (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bmCapCond_after_reserve hcapOk hcap_lt hsum hbs63
    have hnewCap_ge : v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]
    refine SepWPp.bm_call_frame_inv
      (x := { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length })
      (T := vecU8At A x.valPtr x.valCap x.valBuf [] ∗ A.pool ∗ stackAt (s0.sp - 224#64) ((hStack + 48) + 64))
      hReserve' hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpecWithStack, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨hlen_toNat, hnewCap_bound⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; exact mergePanicGen_of_allocFailed (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace]) hm) ?_
    intro sf_res hpcf hrunf hspf hcsf hflf hsymf
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
    dsimp only [doReserveSpecWithStack, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (692))
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hfl3 hsym3
    refine SepWPp.weaken_pre (P' :=
      vecU8At A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]; ac_rfl)) ?_
    exact hp3 (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hcapOk' hnewCap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hfl3 hsym3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hfl1 hsym1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : bmCapCond reqCap x.valCap rest.length :=
      bmCapCond_mono hcapOk (by omega)
    apply SepWPp.bm_of_sepWP_inv hfl1 hsym1
      (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then entry + bv% (844) else entry + bv% (692))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    exact hp3 x.valCap x.valBuf hcapOk' hcap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])

private theorem phase2_from_0x23c_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr v.length)
      ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hBytesFromVec' : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bytesFromVecSpec A img.base).inImage img) := by
    rw [fnAddr_offset_eq_H (name := bytesMergeName) (callee := bytesFromVecName) (k := bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))]
    exact hBytesFromVec
  have hp3 := fun {s : State} =>
    @phase3_from_0x294_gen img A H hStack errStack reqCap hbnd hres_le himg hmc hReserve hVtableSlot x s0 s R v rest tmpPtr
      hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  merge_fetches_H img.base H bytesMerge_fnOff 572 88
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "<bytes::bytes::Bytes as core::convert::From<alloc::vec::Vec<u8>>>::from" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
  wp_steps
  apply SepWP.fold (fold_vecU8At_sp136 A s0.sp (BitVec.ofNat 64 v.length) tmpPtr v) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]
  refine SepWPp.bm_call_frame_inv
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec' hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesFromVecSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesFromVecSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  dsimp only [bytesFromVecSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  rw [unfold_vecHeader_sp136, unfold_bytesAt_sp112]
  apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (660))
  wp_steps
  apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
    (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
    (bytesVtable img.base tmpPtr v.length) (bytesPtr tmpPtr v.length)
    (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hfl2 hsym2
  refine SepWPp.weaken_pre (P' :=
    vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      bytesBoxU8Buf A tmpPtr v ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0)
    (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]; ac_rfl)) ?_
  exact hp3
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
    hfl2 hsym2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

private theorem phase2_from_0x168_nonempty_gen {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (himg : Obj.Loads libsignalSessionImage img)
    (hmc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      ((bmMemcpySpecGen errStack).inImage img))
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok (libsignalSessionCode.rebase img.base H)
      (bytesDropFnAddr img.base tmpPtr (b0 :: v').length)
      ((bytesVtableDropSpecBMGen A hStack tmpPtr (b0 :: v') (b0 :: v').length).inImage img))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  set v := b0 :: v'
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hv_len : v.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
      then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
    by_cases hlt : v.length < rest0.length
    · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
        simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
      simp [hult]
    · have heq : rest0.length = v.length := by omega
      simp [heq]
  have hrest0_ult_v : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 v.length) = false := by
    simp [BitVec.ult, hlen_toNat, hrest0_toNat, hle]
  have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by dsimp [v]; omega)
  have hmerge : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
    have hm := mergeBytes_lengthDelimited_ok hwt hvar (by rw [hlen_toNat]; exact hle)
    rwa [hlen_toNat, hv_take] at hm
  have hp2 := fun {s : State} =>
    @phase2_from_0x23c_gen img A H hStack errStack reqCap hbnd hres_le himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
      (1#64 ||| (if (64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10))).ult 7#64 = true
        then 64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10)) else 7#64) <<< 2)
      w4 w5 w6 w80 hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs63
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  merge_fetches_H img.base H bytesMerge_fnOff 360 212
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  apply SepWPp.bm_of_sepWP_inv hfl hsym (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  refine SepWPp.bm_call_frame_inv
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v) ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hmc hfl1 hsym1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_mc hpcf hrunf hspf hcsf hflf hsymf
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
  apply SepWPp.bm_of_sepWP_inv hflf hsymf (mid := entry + bv% (572))
  wp_steps
  apply SepWP.fold (fold_vecU8Buf_nonempty A tmpPtr v hpos hv_len htmp_ne) (by sep_focus)
  apply SepWP.fold hadv (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hfl2 hsym2
  refine SepWPp.weaken_pre ?_
    (hp2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hfl2 hsym2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by simp only [ProofLib.ofNat_countLeadingZeros64]; ac_rfl)

private theorem phase2_from_0x0e0_gen {img : Obj.Image} {A : RustAlloc}
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
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hde_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_gen_some img A H errStack reqCap hbnd hdef x s0 s R 0x8000000000000007#64
      (by simp [KindNoHeap]) hmerge
  have h23c_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0)) =>
    @phase2_from_0x23c_gen img A H hStack errStack reqCap hbnd hres_le himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 []) hmerge (by decide) hbs_len hcapOk
  have h168_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64)
      {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x168_nonempty_gen img A H hStack errStack reqCap hbnd hres_le himg hmc hBytesFromVec hReserve hVtableSlot x s0 s R
      pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
  merge_fetches_H img.base H bytesMerge_fnOff 224 24
  merge_fetches_H img.base H bytesMerge_fnOff 280 140
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName = entry
  examples_hide_fetches
  dsimp only [sliceCursorAfter]
  apply SepWPp.bm_of_sepWP_inv hfl hsym
    (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then entry + bv% (280) else entry + bv% (240))
  wp_steps
  apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
      sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hfl1 hsym1
  by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
  · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hfl1 hsym1 ⊢
    have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216 fun w216 => ?_
    apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (248))
    wp_steps
    apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hfl2 hsym2
    refine SepWPp.weaken_pre ?_ (hde_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hfl2 hsym2)
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
  · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
      Bool.eq_true_of_not_eq_false hule
    simp only [hule_eq, ↓reduceIte] at hfl1 hsym1 ⊢
    have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
    have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
    have hlen_lt32 : len.toNat < 2 ^ 63 := by omega
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
    rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
    · have hlen0 : len = 0#64 := by
        have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
        rw [List.length_take_of_le hle] at hv_len0
        exact BitVec.eq_of_toNat_eq hv_len0
      have hmerge : mergeBytes x.wt x.bs = some ([], rest0) := by
        have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
        have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
        have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
        rwa [hv, hdrop0] at hm
      clear hv
      have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
        bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
      dsimp only [sliceCursorAfter]
      rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
      apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (572))
      wp_steps
      apply SepWP.fold (vecU8Buf_nil_one A) (by sep_focus)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hfl2 hsym2
      refine SepWPp.weaken_pre ?_ (h23c_exit w4 w5 w6 w80 hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
        hfl2 hsym2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
    · have hlen_v : len = BitVec.ofNat 64 (b0 :: v').length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
      have hle' : (b0 :: v').length ≤ rest0.length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        omega
      have hv_take' : rest0.take (b0 :: v').length = b0 :: v' := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq]; exact hv
      clear hv
      have hpos : 0 < (b0 :: v').length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
      have hv_len : (b0 :: v').length < 2 ^ 63 := by omega
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: v').length).toNat = (b0 :: v').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hmsb : (BitVec.ofNat 64 (b0 :: v').length).getLsbD 63 = false :=
        bitvec_getLsbD_63_of_lt32 hv_len
      have hlen_ne : (BitVec.ofNat 64 (b0 :: v').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      apply SepWPp.bm_of_sepWP_inv hfl1 hsym1 (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
          bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hfl2 hsym2
      refine SepWPp.bm_call_frame_inv (x := ()) (T := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
        hshim hfl2 hsym2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
          bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
        (by simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp]) trivial (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (by intro _ _ hm; dsimp only [bmShimSpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
      intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hflf_sh hsymf_sh
      obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh⟩ := hcsf_sh
      simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx2, hx19, hx29, hlen_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh
      simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp]
      refine SepWPp.pure_elim fun htr_sh => ?_
      apply SepWPp.bm_of_sepWP_inv hflf_sh hsymf_sh (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      intro hfl3 hsym3
      rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]
      refine SepWPp.bm_call_frame_inv (x := ((b0 :: v').length, 1))
        (T := A.pool ∗ stackAt (s0.sp - 224#64) hStack)
        halloc hfl3 hsym3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
        (by simp (config := { decide := true }) only [rustAllocSpecWithStack, arm64_norm, hspf_sh, h21_sh]; rfl)
        (by refine ⟨hlen_toNat, hpos, ⟨0, rfl⟩, by simp only [List.length_cons] at hv_len ⊢; omega⟩)
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (by intro _ _ hm; dsimp only [rustAllocSpecWithStack] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
      intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hflf_al hsymf_al
      obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al⟩ := hcsf_al
      simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al
      simp (config := { decide := true }) only [rustAllocSpecWithStack, arm64_norm, htr_sh, htrace]
      by_cases h0 : sf_al.readReg64 .x0 = 0
      · simp only [h0, ↓reduceIte]
        refine SepWPp.weaken_pre (P' :=
          ⌜sf_al.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt (s0.sp - 224#64) hStack ∗
              ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
              ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
              ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
              ((s0.sp - 120#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 112#64) 32 ∗
              ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
              vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
              (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
              bmExtraStack s0.sp errStack hStack ∗
              memRegion (s0.sp - 224#64) 8 ∗
              memRegion (s0.sp - 216#64) 48 ∗
              savedRegsStack s0.sp s0))
          (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; ac_rfl)) ?_
        refine SepWPp.pure_elim fun htr_al => ?_
        have h0_64 : sf_al.readReg64 .x0 = 0#64 := h0
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]"))
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        refine SepWPp.panic
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64, hpanic])
          fun hm => ?_
        dsimp only [bytesMergeRawSpecGen]
        exact allowPanic_panicked (allocFailedIn_of_eq (by simp (config := { decide := true }) only [Rust.panicked, wp_norm, arm64_norm, htr_al])) hm
      · have h0_64 : sf_al.readReg64 .x0 ≠ 0#64 := h0
        have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
        simp only [h0, ↓reduceIte]
        refine SepWPp.weaken_pre (P' :=
          ⌜(sf_al.readReg64 .x0).toNat % 1 = 0 ∧ sf_al.trace = s0.trace⌝ ∗
            (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
              ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
              ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
              ((s0.sp - 120#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 112#64) 32 ∗
              ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
              A.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗ memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗
              vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
              (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
              stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
              memRegion (s0.sp - 224#64) 8 ∗
              memRegion (s0.sp - 216#64) 48 ∗
              savedRegsStack s0.sp s0))
          (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]; ac_rfl)) ?_
        refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
        dsimp only [sliceCursorAfter]
        apply SepWPp.bm_of_sepWP_inv hflf_al hsymf_al (mid := entry + bv% (360))
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
            ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
            sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        intro hfl4 hsym4
        have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
        obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
        refine SepWPp.weaken_pre ?_ (h168_exit b0 v' (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
          hvar' hle' hv_take' h0_64
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_al, h26_al, h27_al, h28_al, h29_al, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, h25_0, h26_0, h27_0, h28_0, and_self])
          hfl4 hsym4
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
        exact Entails.of_eq (by ac_rfl)


namespace BytesMergeFacts

theorem phase2_from_0x0e0_export_gen {img : Obj.Image} {A : RustAlloc}
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
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName)
      ((doReserveSpecWithStack A (hStack + 48)).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecBMGen A hStack tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) :=
  phase2_from_0x0e0_gen hbnd hres_le himg hdef hmc hshim halloc hpanic hBytesFromVec hReserve
    hVtableSlot hVtableDrop hwt hvar hbs_len hcapOk hpc hrun hsp hsp_align htrace hhigh hfl hsym
    hx0 hx2 hx19 hx29

end BytesMergeFacts

end FnOffShield

namespace BytesMergeFacts

theorem phase2_from_0x0e0_export {img : Obj.Image} {A : RustAlloc}
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
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStack ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePost A x s0 R) (MergePanic A x s0 R) :=
  phase2_from_0x0e0_export_gen (hStack := allocHookStack) (errStack := decodeErrorHookStack)
    (reqCap := true) (by decide) (by decide) himg
    (subroutine_ok_inImage_of_subroutine_ok img hdef)
    (bmMemcpy_inImage_of_frameless hmc)
    (bmShim_inImage_of_noAllocShim hshim)
    (subroutine_ok_inImage_of_subroutine_ok img halloc)
    hpanic hBytesFromVec
    (subroutine_ok_inImage_of_subroutine_ok img hReserve)
    hVtableSlot hVtableDrop hwt hvar hbs_len hcapOk hpc hrun hsp hsp_align htrace hhigh
    hfl hsym hx0 hx2 hx19 hx29

theorem phase2_from_0x0e0_export_x {img : Obj.Image} {A : RustAlloc}
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
    (hBytesFromVec : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr doReserveName) ((doReserveSpecX A).inImage img))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (libsignalSessionCode.rebase img.base H)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpecX A tmpPtr v v.length).inImage img))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : x.bs.length < 2 ^ 63)
    (hcapOk : BytesMergeCapOk x.valCap x.bs.length)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr bytesMergeName + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) decodeVarintSliceStackX ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostX A x s0 R) (MergePanicX A x s0 R) :=
  phase2_from_0x0e0_export_gen (hStack := extHookStack) (errStack := decodeErrorHookStackX)
    (reqCap := true) (by decide) (by decide) himg hdef hmc hshim halloc hpanic hBytesFromVec
    hReserve hVtableSlot hVtableDrop hwt hvar hbs_len hcapOk hpc hrun hsp hsp_align htrace hhigh
    hfl hsym hx0 hx2 hx19 hx29

end BytesMergeFacts

/-! ## Relocatable `[LibsignalPlacement]` Phase 2 and 3 lemmas -/

theorem unfold_bytesPlacedAt_sp112 [LibsignalPlacement] (A : RustAlloc) (sp0 ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    bytesPlacedAt A (sp0 - 112#64) ptr bs =
      ((sp0 - 112#64) ↦₆₄ bytesPlacedVtable ptr bs.length) ∗
      ((sp0 - 104#64) ↦₆₄ bytesPtr ptr bs.length) ∗
      ((sp0 - 96#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp0 - 88#64) ↦₆₄ bytesData ptr bs.length) ∗
      bytesBoxU8Buf A ptr bs := by
  dsimp only [bytesPlacedAt, bytesHeader]
  have e1 : sp0 - 112#64 + 8#64 = sp0 - 104#64 := by bv_omega
  have e2 : sp0 - 112#64 + 16#64 = sp0 - 96#64 := by bv_omega
  have e3 : sp0 - 112#64 + 24#64 = sp0 - 88#64 := by bv_omega
  rw [e1, e2, e3, sepConj_assoc, sepConj_assoc, sepConj_assoc]

theorem bmShim_placed_of_noAllocShim [LibsignalPlacement] {prog : Program} {addr : BitVec 64}
    {errStack : Nat} (hshim : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (withLsCl lsmpl (bmShimSpecGen errStack)) := by
  apply subroutine_ok_withLsCl_of_plain
  have h := subroutine_ok_withStack_of_subroutine_ok hshim (bmSliceStack errStack)
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec (bmSliceStack errStack)).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, bmShimSpecGen] at hpre ⊢
    simpa only [pure_true, emp_sepConj, sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, noAllocShimSpec, bmShimSpecGen] at hpost ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem phase3_from_0x294_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 660#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = bytesPtr tmpPtr v.length)
    (hx22 : s.readReg64 .x22 = bytesData tmpPtr v.length)
    (hx24 : s.readReg64 .x24 = bytesPlacedVtable tmpPtr v.length) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hsum : 1 + v.length + rest.length ≤ x.bs.length := mergeBytes_length_sum hmerge
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun (cap' ptr' : BitVec 64) {s : State}
      (hcapOk' : bmCapCond reqCap cap' rest.length) (hcap' : v.length ≤ cap'.toNat) =>
    @phase3_from_0x2b4_placed_gen _ A H hStack errStack reqCap hbnd (by omega) hmc x s0 s R v rest tmpPtr cap' ptr'
      hVtableDrop hmerge hcapOk' hcap' hv_len
  rw [bm_vecU8At_eq_header_sep_buf A x.valPtr x.valCap x.valBuf x.valBs]
  dsimp only [vecHeader] at hpc hReserve hp3 ⊢
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if x.valCap.ult (BitVec.ofNat 64 v.length) = true then (blkPl_7).base + bv% (800) else (blkPl_7).base + bv% (676))
  wp_steps
  apply SepWP.fold (fold_vecU8At_clear A x.valPtr x.valCap x.valBuf x.valBs) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hult : x.valCap.ult (BitVec.ofNat 64 v.length) = true
  · simp only [hult, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_lt : x.valCap.toNat < v.length := by
      simpa [BitVec.ult, hlen_toNat] using hult
    have hnewCap_bound : reserveCap x.valCap.toNat ([] : List (BitVec 8)).length v.length ≤ 9223372036854775807 :=
      bm_reserveCap_bound reqCap hcapOk hcap_lt hsum hbs_len
    have hcapOk' : bmCapCond reqCap (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) rest.length :=
      bmCapCond_after_reserve hcapOk hcap_lt hsum hbs63
    have hnewCap_ge : v.length ≤ (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)).toNat := by
      dsimp [reserveCap] at hnewCap_bound ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hnewCap_ule :
        (BitVec.ofNat 64 v.length).ule (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) = true := by
      simp only [BitVec.ule, hlen_toNat, decide_eq_true_eq]
      exact hnewCap_ge
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]
    refine SepWPp.bm_call_frame_lscl
      (x := { v := x.valPtr, cap := x.valCap, ptr := x.valBuf, bs := [], additional := v.length })
      (T := vecU8At A x.valPtr x.valCap x.valBuf [] ∗ A.pool ∗ stackAt (s0.sp - 224#64) ((hStack + 48) + 64))
      hReserve hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
      (by simp (config := { decide := true }) only [doReserveSpecWithStack, arm64_norm, hsp, hx19, hx20]; rfl)
      (by exact ⟨hlen_toNat, hnewCap_bound⟩)
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (by intro _ _ hm; exact mergePanicGen_of_allocFailed (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace]) hm) ?_
    intro sf_res hpcf hrunf hspf hcsf hclf hrof
    obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
    obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
    simp (config := { decide := true }) only [arm64_norm, hsp] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
    dsimp only [doReserveSpecWithStack, List.length_nil]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWPp.pure_elim fun htr => ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun ptr' => ?_
    rw [bm_vecU8At_eq_header_sep_buf A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' []]
    dsimp only [vecHeader, List.length_nil]
    apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (692))
    wp_steps
    apply SepWP.fold
      (fold_vecU8At_clear A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [])
      (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    intro hcl3 hro3
    refine SepWPp.weaken_pre (P' :=
      vecU8At A x.valPtr (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' [] ∗
        bytesBoxU8Buf A tmpPtr v ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_sliceGen_split s0.sp errStack ((hStack + 48) + 64) hres_le hbnd]; ac_rfl)) ?_
    exact hp3 (BitVec.ofNat 64 (reserveCap x.valCap.toNat 0 v.length)) ptr' hcapOk' hnewCap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f, hx20, hnewCap_ule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl3 hro3
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h22f, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h23f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24f, hx24])
  · have hult_eq : x.valCap.ult (BitVec.ofNat 64 v.length) = false :=
      Bool.eq_false_iff.mpr hult
    simp only [hult_eq, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hcap_ge : v.length ≤ x.valCap.toNat := by
      simp [BitVec.ult, hlen_toNat] at hult_eq
      exact hult_eq
    have hcapOk' : bmCapCond reqCap x.valCap rest.length :=
      bmCapCond_mono hcapOk (by omega)
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1
      (mid := (blkPl_7).base + bv% (692))
    wp_steps
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    exact hp3 x.valCap x.valBuf hcapOk' hcap_ge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx20, hult_eq])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx20])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx21])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx22])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx24])

private theorem phase2_from_0x23c_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {v rest : List (BitVec 8)} {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr v.length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    (hmerge : mergeBytes x.wt x.bs = some (v, rest))
    (hv_len : v.length < 2 ^ 63)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 v.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 v.length)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx22 : s.readReg64 .x22 = bytesMutDataWord (BitVec.ofNat 64 v.length))
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        bm_vecU8Buf A (BitVec.ofNat 64 v.length) tmpPtr v ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp3 := fun {s : State} =>
    @phase3_from_0x294_placed_gen _ A H hStack errStack reqCap hbnd hres_le hmc hReserve x s0 s R v rest tmpPtr
      hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hReserve
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := lsmpl.base 250)
  wp_steps
  apply SepWP.fold (fold_vecU8At_sp136 A s0.sp (BitVec.ofNat 64 v.length) tmpPtr v) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]
  refine SepWPp.bm_call_frame_lscl
    (x := (s0.sp - 136#64, s0.sp - 112#64, BitVec.ofNat 64 v.length, tmpPtr, v))
    (T := vecU8At A (s0.sp - 136#64) (BitVec.ofNat 64 v.length) tmpPtr v ∗
      memRegion (s0.sp - 112#64) 32 ∗
      stackAt (s0.sp - 224#64) bytesFromVecStack)
    hBytesFromVec hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx21, hx22, hx29, hsp,
      bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bytesFromVecPlacedSpec, arm64_norm, hsp, hx29])
    hlen_toNat
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bytesFromVecPlacedSpec] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_bfv hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx19, hx20, hx21, hx22, hx29,
    bytesMutDataWord_getElem_zero, bytesMutDataWord_lsr5, bitvec_ult_zero] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  dsimp only [bytesFromVecPlacedSpec]
  rw [sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_elim fun htr => ?_
  rw [unfold_vecHeader_sp136, unfold_bytesPlacedAt_sp112]
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (660))
  wp_steps
  apply SepWP.fold (memRegion_104_fold s0.sp w0 w1 w2 w3
    (BitVec.ofNat 64 v.length) tmpPtr (BitVec.ofNat 64 v.length)
    (bytesPlacedVtable tmpPtr v.length) (bytesPtr tmpPtr v.length)
    (BitVec.ofNat 64 v.length) (bytesData tmpPtr v.length) 0#64) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre (P' :=
    vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      bytesBoxU8Buf A tmpPtr v ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ A.pool ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
      memRegion (s0.sp - 224#64) 8 ∗
      memRegion (s0.sp - 216#64) 48 ∗
      memRegion (s0.sp - 168#64) 104 ∗
      savedRegsStack s0.sp s0)
    (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; rw [stackAt_sliceGen_split s0.sp errStack bytesFromVecStack (by dsimp [bmSliceStack, bytesFromVecStack]; omega) hbnd]; ac_rfl)) ?_
  exact hp3
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
    hsp_align
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr, htrace])
    (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
    hcl2 hro2
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm])

private theorem phase2_from_0x168_nonempty_placed_gen [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {hStack errStack : Nat} {reqCap : Bool}
    (hbnd : bmTotalStack errStack ≤ 2 ^ 64)
    (hres_le : (hStack + 48) + 64 ≤ bmSliceStack errStack)
    (hmc : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      ((blkPl_7).ρ "memcpy")
      (withLsCl lsmpl (bmMemcpySpecGen errStack)))
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {pfx rest0 : List (BitVec 8)} {b0 : BitVec 8} {v' : List (BitVec 8)}
    {tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64}
    (hVtableDrop : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (bytesPlacedDropFnAddr tmpPtr (b0 :: v').length)
      (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr (b0 :: v') (b0 :: v').length)))
    (hvar : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
    (hpfx : x.bs = pfx ++ rest0)
    (hle : (b0 :: v').length ≤ rest0.length)
    (hv_take : rest0.take (b0 :: v').length = b0 :: v')
    (hwt : x.wt = .lengthDelimited)
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (htmp_ne : tmpPtr ≠ 0#64)
    (hpc : s.pc = (blkPl_7).base + 360#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (b0 :: v').length)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 rest0.length)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx21 : s.readReg64 .x21 = tmpPtr)
    (hx24 : s.readReg64 .x24 = x.slot)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
        ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
        ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
        ((s0.sp - 120#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 112#64) 32 ∗
        ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
        A.live tmpPtr (b0 :: v').length 1 ∗ memRegion tmpPtr (b0 :: v').length ∗
        vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  set v := b0 :: v'
  have hpos : 0 < v.length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hv_len : v.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_v : (if (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true
      then BitVec.ofNat 64 v.length else BitVec.ofNat 64 rest0.length) = BitVec.ofNat 64 v.length := by
    by_cases hlt : v.length < rest0.length
    · have hult : (BitVec.ofNat 64 v.length).ult (BitVec.ofNat 64 rest0.length) = true := by
        simp [BitVec.ult, hlen_toNat, hrest0_toNat, hlt]
      simp [hult]
    · have heq : rest0.length = v.length := by omega
      simp [heq]
  have hrest0_ult_v : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 v.length) = false := by
    simp [BitVec.ult, hlen_toNat, hrest0_toNat, hle]
  have hlen_ne : (BitVec.ofNat 64 v.length == 0#64) = false := by
    apply beq_false_of_ne
    intro h
    have h2 := congrArg BitVec.toNat h
    rw [hlen_toNat] at h2
    exact absurd h2 (by dsimp [v]; omega)
  have hmerge : mergeBytes x.wt x.bs = some (v, rest0.drop v.length) := by
    have hm := mergeBytes_lengthDelimited_ok hwt hvar (by rw [hlen_toNat]; exact hle)
    rwa [hlen_toNat, hv_take] at hm
  have hp2 := fun {s : State} =>
    @phase2_from_0x23c_placed_gen _ A H hStack errStack reqCap hbnd hres_le hmc hBytesFromVec hReserve x s0 s R
      v (rest0.drop v.length) tmpPtr tmpPtr (BitVec.ofNat 64 v.length) (BitVec.ofNat 64 v.length)
      (1#64 ||| (if (64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10))).ult 7#64 = true
        then 64#64 - BitVec.ofNat 64 (countLeadingZeros (BitVec.ofNat 64 v.length >>> 10)) else 7#64) <<< 2)
      w4 w5 w6 w80 hVtableDrop hmerge hv_len hbs_len hcapOk
  clear hBytesFromVec hReserve
  rw [sliceCursorAfter_split_copy x.slot x.ptr x.bs pfx rest0 v.length hpfx hle]
  rw [hv_take]
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hadv := sliceCursorAfter_advance_fold x.slot x.ptr x.bs pfx rest0 v.length hpfx hle hbs63
  dsimp only at hadv
  rw [hv_take] at hadv
  clear hpfx
  apply SepWPp.bm_of_sepWP_lscl hcl hro (mid := (blkPl_7).ρ "memcpy")
  wp_steps
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  refine SepWPp.bm_call_frame_lscl
    (x := (tmpPtr, x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length), v))
    (T := memRegion tmpPtr v.length ∗ ((x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)) ↦ₛ v) ∗
      stackAt (s0.sp - 224#64) (bmSliceStack errStack))
    hmc hcl1 hro1
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
      bitvec_getLsbD_63_of_lt32, bitvec_ult_self, bitvec_sub_self_64, bitvec_if_zero_ult_self])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
    (by simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp]; rfl)
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hx8, hx21, hx24, hx29, hsp,
      hv_len, hmin_v, hrest0_ult_v, hlen_ne, hlen_toNat, and_self])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (by intro _ _ hm; dsimp only [bmMemcpySpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
  intro sf_mc hpcf hrunf hspf hcsf hclf hrof
  obtain ⟨h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f⟩ := hcsf
  obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
  simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx8, hx19, hx21, hx24, hx29, hmin_v] at hpcf hspf h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f
  simp (config := { decide := true }) only [bmMemcpySpecGen, arm64_norm, hsp, htrace]
  refine SepWPp.pure_elim fun ⟨_, htr⟩ => ?_
  apply SepWPp.bm_of_sepWP_lscl hclf hrof (mid := (blkPl_7).base + bv% (572))
  wp_steps
  apply SepWP.fold (fold_vecU8Buf_nonempty A tmpPtr v hpos hv_len htmp_ne) (by sep_focus)
  apply SepWP.fold hadv (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
  intro hcl2 hro2
  refine SepWPp.weaken_pre ?_
    (hp2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr])
      (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25f, h26f, h27f, h28f, h29f, h25_0, h26_0, h27_0, h28_0, and_self])
      hcl2 hro2
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h20f])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21f])
      (by simp (config := { decide := true }) only [bytesMutDataWord, wp_norm, arm64_norm, h22f, ProofLib.ofNat_countLeadingZeros64])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29f]))
  exact Entails.of_eq (by simp only [ProofLib.ofNat_countLeadingZeros64]; ac_rfl)

private theorem phase2_from_0x0e0_placed_gen [LibsignalPlacement] {A : RustAlloc}
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
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) := by
  have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
  have hal : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := spAligned_sub_224 hsp_align
  obtain ⟨pfx, hpfx⟩ := bm_decodeVarint_suffix hvar
  have hrest0_len : rest0.length ≤ x.bs.length := by rw [hpfx, List.length_append]; omega
  have hrest0_toNat : (BitVec.ofNat 64 rest0.length).toNat = rest0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hde_exit := fun {s : State} (hmerge : mergeBytes x.wt x.bs = none) =>
    @epilogue_decodeErrorFrom_placed_gen _ A H errStack reqCap hbnd hdef x s0 s R 0x8000000000000007#64
      (by simp [KindNoHeap]) hmerge
  have h23c_exit := fun (w4 w5 w6 w80 : BitVec 64) {s : State}
      (hmerge : mergeBytes x.wt x.bs = some ([], rest0)) =>
    @phase2_from_0x23c_placed_gen _ A H hStack errStack reqCap hbnd hres_le hmc hBytesFromVec hReserve x s0 s R
      [] rest0 1#64 1#64 0#64 0#64 1#64 w4 w5 w6 w80 (hVtableDrop 1#64 []) hmerge (by decide) hbs_len hcapOk
  have h168_exit := fun (b0 : BitVec 8) (v' : List (BitVec 8)) (tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 : BitVec 64)
      {s : State}
      (hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0))
      (hle' : (b0 :: v').length ≤ rest0.length)
      (hv_take' : rest0.take (b0 :: v').length = b0 :: v')
      (htmp_ne : tmpPtr ≠ 0#64) =>
    @phase2_from_0x168_nonempty_placed_gen _ A H hStack errStack reqCap hbnd hres_le hmc hBytesFromVec hReserve x s0 s R
      pfx rest0 b0 v' tmpPtr w0 w1 w2 w3 w4 w5 w6 w80 (hVtableDrop tmpPtr (b0 :: v'))
      hvar' hpfx hle' hv_take' hwt hbs_len hcapOk htmp_ne
  clear hBytesFromVec hReserve hVtableDrop
  dsimp only [sliceCursorAfter]
  apply SepWPp.bm_of_sepWP_lscl hcl hro
    (mid := if len.ule (BitVec.ofNat 64 rest0.length) = true then (blkPl_7).base + bv% (280) else (blkPl_7).base + bv% (240))
  wp_steps
  apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
      ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
      sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
  apply SepWP.done
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2])
    (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
  intro hcl1 hro1
  by_cases hule : len.ule (BitVec.ofNat 64 rest0.length) = false
  · simp only [hule, Bool.false_eq_true, ↓reduceIte] at hcl1 hro1 ⊢
    have hlt : rest0.length < len.toNat := by simp [BitVec.ule, hrest0_toNat] at hule; omega
    have hmerge : mergeBytes x.wt x.bs = none := mergeBytes_lengthDelimited_underflow hwt hvar hlt
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 216#64) 48 ∗
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_216 fun w216 => ?_
    apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (248))
    wp_steps
    apply SepWP.fold (sliceCursorAfter_to_err x.slot x.ptr x.bs rest0) (by sep_focus)
    apply SepWP.done
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
    intro hcl2 hro2
    refine SepWPp.weaken_pre ?_ (hde_exit hmerge
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hule])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
      hsp_align
      (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
      (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
      hcl2 hro2)
    exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
  · have hule_eq : len.ule (BitVec.ofNat 64 rest0.length) = true :=
      Bool.eq_true_of_not_eq_false hule
    simp only [hule_eq, ↓reduceIte] at hcl1 hro1 ⊢
    have hle : len.toNat ≤ rest0.length := by simpa [BitVec.ule, hrest0_toNat] using hule_eq
    have hbs63 : x.bs.length < 2 ^ 63 := bmLenBound_lt63 hbs_len
    have hlen_lt32 : len.toNat < 2 ^ 63 := by omega
    refine SepWPp.weaken_pre (P' := memRegion (s0.sp - 168#64) 104 ∗
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        savedRegsStack s0.sp s0)) (Entails.of_eq (by ac_rfl)) ?_
    refine SepWPp.unfold_memRegion_168 fun w0 w1 w2 w3 w4 w5 w6 w80 => ?_
    rcases hv : rest0.take len.toNat with _ | ⟨b0, v'⟩
    · have hlen0 : len = 0#64 := by
        have hv_len0 : (rest0.take len.toNat).length = 0 := by rw [hv]; rfl
        rw [List.length_take_of_le hle] at hv_len0
        exact BitVec.eq_of_toNat_eq hv_len0
      have hmerge : mergeBytes x.wt x.bs = some ([], rest0) := by
        have hv_len0 : len.toNat = 0 := by rw [hlen0]; rfl
        have hdrop0 : rest0.drop len.toNat = rest0 := by rw [hv_len0]; rfl
        have hm := mergeBytes_lengthDelimited_ok hwt hvar hle
        rwa [hv, hdrop0] at hm
      clear hv
      have hmin0 : (if (0#64).ult (BitVec.ofNat 64 rest0.length) = true then 0#64 else BitVec.ofNat 64 rest0.length) = 0#64 :=
        bitvec_if_zero_ult_self (BitVec.ofNat 64 rest0.length)
      dsimp only [sliceCursorAfter]
      rw [← emp_sepConj (((s0.sp - 168#64) ↦₆₄ w0) ∗ _)]
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).base + bv% (572))
      wp_steps
      apply SepWP.fold (vecU8Buf_nil_one A) (by sep_focus)
      apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
          ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.weaken_pre ?_ (h23c_exit w4 w5 w6 w80 hmerge
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp, hule_eq, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hsp])
        hsp_align
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htrace])
        (by obtain ⟨h25, h26, h27, h28⟩ := hhigh; simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25, h26, h27, h28, and_self])
        hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx19])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx0, hlen0, hmin0, bitvec_ult_zero, bitvec_ult_self, bitvec_sub_self_64])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, bytesMutDataWord_zero])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hx29]))
      exact Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hsp]; ac_rfl)
    · have hlen_v : len = BitVec.ofNat 64 (b0 :: v').length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq, BitVec.ofNat_toNat]; rfl
      have hle' : (b0 :: v').length ≤ rest0.length := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        omega
      have hv_take' : rest0.take (b0 :: v').length = b0 :: v' := by
        have hv_len_eq : (b0 :: v').length = len.toNat := by rw [← hv, List.length_take_of_le hle]
        rw [hv_len_eq]; exact hv
      clear hv
      have hpos : 0 < (b0 :: v').length := List.length_pos_of_ne_nil (List.cons_ne_nil b0 v')
      have hv_len : (b0 :: v').length < 2 ^ 63 := by omega
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: v').length).toNat = (b0 :: v').length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hmsb : (BitVec.ofNat 64 (b0 :: v').length).getLsbD 63 = false :=
        bitvec_getLsbD_63_of_lt32 hv_len
      have hlen_ne : (BitVec.ofNat 64 (b0 :: v').length == 0#64) = false := by
        apply beq_false_of_ne
        intro h
        have h2 := congrArg BitVec.toNat h
        rw [hlen_toNat] at h2
        exact absurd h2 (by simp)
      apply SepWPp.bm_of_sepWP_lscl hcl1 hro1 (mid := (blkPl_7).ρ lsRustNoAllocShimSym)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
          bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
      intro hcl2 hro2
      refine SepWPp.bm_call_frame_lscl (x := ()) (T := stackAt (s0.sp - 224#64) (bmSliceStack errStack))
        hshim hcl2 hro2
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpc, hx0, hx2, hx29, hsp,
          hule_eq, hlen_v, hv_len, hmsb, hlen_ne, bitvec_ult_33bits_of_lt32, bitvec_msb_false_of_lt32,
          bitvec_getLsbD_63_of_lt32])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrun])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hsp, hsp_align]) rfl
        (by simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp]) trivial (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (by intro _ _ hm; dsimp only [bmShimSpecGen] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
      intro sf_sh hpcf_sh hrunf_sh hspf_sh hcsf_sh hclf_sh hrof_sh
      obtain ⟨h19_sh, h20_sh, h21_sh, h22_sh, h23_sh, h24_sh, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh⟩ := hcsf_sh
      simp (config := { decide := true }) only [arm64_norm, hsp, hx0, hx2, hx19, hx29, hlen_v] at hpcf_sh hspf_sh h19_sh h20_sh h21_sh h22_sh h23_sh h24_sh h25_sh h26_sh h27_sh h28_sh h29_sh
      simp (config := { decide := true }) only [bmShimSpecGen, arm64_norm, hsp]
      refine SepWPp.pure_elim fun htr_sh => ?_
      apply SepWPp.bm_of_sepWP_lscl hclf_sh hrof_sh (mid := (blkPl_7).ρ lsRustAllocSym)
      wp_steps
      apply SepWP.done
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
      intro hcl3 hro3
      rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]
      refine SepWPp.bm_call_frame_lscl (x := ((b0 :: v').length, 1))
        (T := A.pool ∗ stackAt (s0.sp - 224#64) hStack)
        halloc hcl3 hro3
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_sh])
        (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_sh])
        (by rw [State.spAligned] at hsp_align ⊢; simp (config := { decide := true }) only [arm64_norm, hspf_sh, hsp_align]) rfl
        (by simp (config := { decide := true }) only [rustAllocSpecWithStack, arm64_norm, hspf_sh, h21_sh]; rfl)
        (by refine ⟨hlen_toNat, hpos, ⟨0, rfl⟩, by simp only [List.length_cons] at hv_len ⊢; omega⟩)
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (by intro _ _ hm; dsimp only [rustAllocSpecWithStack] at hm; rw [sepConj_assoc, satisfies_pure_sepConj] at hm; exact False.elim hm.1) ?_
      intro sf_al hpcf_al hrunf_al hspf_al hcsf_al hclf_al hrof_al
      obtain ⟨h19_al, h20_al, h21_al, h22_al, h23_al, h24_al, h25_al, h26_al, h27_al, h28_al, h29_al⟩ := hcsf_al
      simp (config := { decide := true }) only [arm64_norm, hspf_sh, h19_sh, h21_sh, h24_sh, h29_sh] at hpcf_al hspf_al h19_al h20_al h21_al h22_al h23_al h24_al h25_al h26_al h27_al h28_al h29_al
      simp (config := { decide := true }) only [rustAllocSpecWithStack, arm64_norm, htr_sh, htrace]
      by_cases h0 : sf_al.readReg64 .x0 = 0
      · simp only [h0, ↓reduceIte]
        refine SepWPp.weaken_pre (P' :=
          ⌜sf_al.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            (A.pool ∗ stackAt (s0.sp - 224#64) hStack ∗
              ((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
              ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
              ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
              ((s0.sp - 120#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 112#64) 32 ∗
              ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
              vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
              (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗
              bmExtraStack s0.sp errStack hStack ∗
              memRegion (s0.sp - 224#64) 8 ∗
              memRegion (s0.sp - 216#64) 48 ∗
              savedRegsStack s0.sp s0))
          (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; ac_rfl)) ?_
        refine SepWPp.pure_elim fun htr_al => ?_
        have h0_64 : sf_al.readReg64 .x0 = 0#64 := h0
        apply SepWPp.of_sepWP (mid := (blkPl_7).ρ lsHandleErrorSym)
        wp_steps
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        refine SepWPp.panic
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_64]; exact hpanic)
          fun hm => ?_
        dsimp only [bytesMergeRawSpecGen]
        exact allowPanic_panicked (allocFailedIn_of_eq (by simp (config := { decide := true }) only [Rust.panicked, wp_norm, arm64_norm, htr_al])) hm
      · have h0_64 : sf_al.readReg64 .x0 ≠ 0#64 := h0
        have h0_beq : (sf_al.readReg64 .x0 == 0#64) = false := beq_false_of_ne h0_64
        simp only [h0, ↓reduceIte]
        refine SepWPp.weaken_pre (P' :=
          ⌜(sf_al.readReg64 .x0).toNat % 1 = 0 ∧ sf_al.trace = s0.trace⌝ ∗
            (((s0.sp - 168#64) ↦₆₄ w0) ∗ ((s0.sp - 160#64) ↦₆₄ w1) ∗
              ((s0.sp - 152#64) ↦₆₄ w2) ∗ ((s0.sp - 144#64) ↦₆₄ w3) ∗
              ((s0.sp - 136#64) ↦₆₄ w4) ∗ ((s0.sp - 128#64) ↦₆₄ w5) ∗
              ((s0.sp - 120#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 112#64) 32 ∗
              ((s0.sp - 80#64) ↦₆₄ w80) ∗ memRegion (s0.sp - 72#64) 8 ∗
              A.live (sf_al.readReg64 .x0) (b0 :: v').length 1 ∗ memRegion (sf_al.readReg64 .x0) (b0 :: v').length ∗
              vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
              (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
              stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
              memRegion (s0.sp - 224#64) 8 ∗
              memRegion (s0.sp - 216#64) 48 ∗
              savedRegsStack s0.sp s0))
          (Entails.of_eq (by simp (config := { decide := true }) only [arm64_norm, hspf_sh]; rw [stackAt_sliceGen_split s0.sp errStack hStack (by omega) hbnd]; ac_rfl)) ?_
        refine SepWPp.pure_elim fun ⟨_, htr_al⟩ => ?_
        dsimp only [sliceCursorAfter]
        apply SepWPp.bm_of_sepWP_lscl hclf_al hrof_al (mid := (blkPl_7).base + bv% (360))
        wp_steps
        apply SepWP.fold (show (x.slot ↦₆₄ (x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length))) ∗
            ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (x.ptr ↦ₛ x.bs) ⊢
            sliceCursorAfter x.slot x.ptr x.bs rest0 from Entails.refl _) (by sep_focus)
        apply SepWP.done
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
        intro hcl4 hro4
        have hvar' : decodeVarint x.bs = some (BitVec.ofNat 64 (b0 :: v').length, rest0) := by rwa [← hlen_v]
        obtain ⟨h25_0, h26_0, h27_0, h28_0⟩ := hhigh
        refine SepWPp.weaken_pre ?_ (h168_exit b0 v' (sf_al.readReg64 .x0) w0 w1 w2 w3 w4 w5 w6 w80
          hvar' hle' hv_take' h0_64
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hpcf_al, h0_beq])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hrunf_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, hspf_al])
          hsp_align
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, htr_al])
          (by simp (config := { decide := true }) only [bm_HighCalleeSaved, wp_norm, arm64_norm, h25_al, h26_al, h27_al, h28_al, h29_al, h25_sh, h26_sh, h27_sh, h28_sh, h29_sh, h25_0, h26_0, h27_0, h28_0, and_self])
          hcl4 hro4
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h21_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h19_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h24_al])
          (by simp (config := { decide := true }) only [wp_norm, arm64_norm, h29_al]))
        exact Entails.of_eq (by ac_rfl)

namespace BytesMergeFacts

theorem phase2_from_0x0e0_export_placed_gen [LibsignalPlacement] {A : RustAlloc}
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
    (hBytesFromVec : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 250)
      (withLsCl lsmpl (bytesFromVecPlacedSpec A)))
    (hReserve : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
      (lsmpl.base 13)
      (withLsCl lsmpl (doReserveSpecWithStack A (hStack + 48))))
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok ((blkPC_7).rebase (blkPl_7).base H)
        (bytesPlacedDropFnAddr tmpPtr v.length)
        (withLsCl lsmpl (bytesVtableDropSpecBMGen A hStack tmpPtr v v.length)))
    {x : BytesMergeGhost} {s0 s : State} {R : SepProp}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hwt : x.wt = .lengthDelimited)
    (hvar : decodeVarint x.bs = some (len, rest0))
    (hbs_len : bmLenBound reqCap x.bs.length)
    (hcapOk : bmCapCond reqCap x.valCap x.bs.length)
    (hpc : s.pc = (blkPl_7).base + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 224#64)
    (hsp_align : s0.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hhigh : bm_HighCalleeSaved s0 s)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = len)
    (hx2 : s.readReg64 .x2 = x.bufRef)
    (hx19 : s.readReg64 .x19 = x.valPtr)
    (hx29 : s.readReg64 .x29 = s0.sp - 64#64) :
    SepWPp ((blkPC_7).rebase (blkPl_7).base H) (s0.readReg64 .lr) s
      (vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest0 ∗ A.pool ∗
        stackAt (s0.sp - 224#64) (bmSliceStack errStack) ∗
        memRegion (s0.sp - 224#64) 8 ∗
        memRegion (s0.sp - 216#64) 48 ∗
        memRegion (s0.sp - 168#64) 104 ∗
        savedRegsStack s0.sp s0)
      (MergePostGen errStack reqCap A x s0 R) (MergePanicGen errStack reqCap A x s0 R) :=
  phase2_from_0x0e0_placed_gen hbnd hres_le hdef hmc hshim halloc hpanic hBytesFromVec hReserve
    hVtableDrop hwt hvar hbs_len hcapOk hpc hrun hsp hsp_align htrace hhigh hcl hro
    hx0 hx2 hx19 hx29

end BytesMergeFacts

end CryptoVerification.LibsignalTripleRatchet.Prost
