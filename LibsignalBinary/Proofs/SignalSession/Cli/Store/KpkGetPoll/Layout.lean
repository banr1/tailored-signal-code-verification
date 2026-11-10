/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Specifications.AsmConstants

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## Code layout & stack/region splitting helpers -/

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_kpkPoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 432 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 432) =
      stackAt (sp - 432#64) calleeStk ∗ cells (sp - 432#64) 54 :=
  ProofLib.stackAt_split_cells sp calleeStk 54 hhi

/-- Six consecutive 64-bit words (`48` bytes) starting at `a`. -/
def words6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

/-- Eleven consecutive 64-bit words (`88` bytes) starting at `a`. -/
def words11At (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
  ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
  ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10)

theorem memRegion_16_cells (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        (a ↦₆₄ v1) ∗ ((a + 8#64) ↦₆₄ v0)) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + 16 by rfl, memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_eight, memRegion_16_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + 24 by rfl, memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_eight, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 8 + 32 by rfl, memRegion_split a 8 32 (by decide),
    ProofLib.memRegion_eight, memRegion_32_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words6At a w0 w1 w2 w3 w4 w5) := by
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

theorem memRegion_88_words11 (a : BitVec 64) :
    memRegion a 88 =
      (∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words11At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10) := by
  rw [show (88 : Nat) = 48 + 40 by rfl, memRegion_split a 48 40 (by decide),
    memRegion_48_words6, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, words6At, words11At,
    sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem words4_entails_memRegion_32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion_32_cells]
  exact Entails.sepExists_right w3 (Entails.sepExists_right w2
    (Entails.sepExists_right w1 (Entails.sepExists_right w0 (Entails.refl _))))

theorem words5_entails_memRegion_40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [memRegion_40_cells]
  exact Entails.sepExists_right w4 (Entails.sepExists_right w3
    (Entails.sepExists_right w2 (Entails.sepExists_right w1
      (Entails.sepExists_right w0 (Entails.refl _)))))

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem entails_pure_right {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have htrue : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [htrue, ProofLib.pure_true, emp_sepConj]
  exact h

theorem words11At_missing_entails (A : RustAlloc)
    (out w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words11At out 0xFFFFFFFFFFFFFFFF#64 0x800000000000000F#64
      w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢ kpkAnsAt A out .missing := by
  have herr : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = errTag := by decide
  have hspe : (0x800000000000000F#64 : BitVec 64) = speWord 15 := by decide
  unfold words11At kpkAnsAt pkAnsAt
  rw [herr, hspe, show (88 - 16 : Nat) = 40 + 32 by rfl,
    memRegion_split (out + 0x10#64) 40 32 (by decide)]
  have h40 := words5_entails_memRegion_40 (out + 0x10#64) w2 w3 w4 w5 w6
  have h32 := words4_entails_memRegion_32 ((out + 0x10#64) + 40#64) w7 w8 w9 w10
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40 h32 ⊢
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono h40 h32)))
  exact entails_of_eq (by ac_rfl)

/-! ## `vecU8Buf` borrowing, zero-capacity elimination, and deallocation -/

theorem vecU8Buf_zero_entails_emp (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold SpqrV1.Alloc.vecU8Buf
  exact (ProofLib.pure_extract_iff _ _ _).mpr fun _ => Entails.refl emp

private theorem vecU8Buf_cap_lt {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {Q : SepProp} {m : Memory} (h : m ⊨ SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ Q) :
    cap.toNat < 2 ^ 63 := by
  unfold SpqrV1.Alloc.vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.1

def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem vecU8Buf_split_raw (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil]
    refine Entails.trans (entails_pure_right hpure (Entails.refl _)) ?_
    exact entails_of_eq (ProofLib.emp_sepConj _).symm
  · simp only [hcap, ite_false]
    refine Entails.trans ?_ (sepConj_mono_right (entails_pure_right hpure (Entails.refl _)))
    exact entails_of_eq (by ac_rfl)

private theorem vecU8Buf_unsplit_raw (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ⊢ SpqrV1.Alloc.vecU8Buf A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  rw [← sepConj_assoc, sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => entails_pure_right hpure ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil, ProofLib.emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ite_false]
    exact entails_of_eq (by ac_rfl)

private theorem bytesAt_false_eq (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.ChainProofs.bytesAt false ptr bs = (ptr ↦ₛ bs) := rfl

/-- Wrapper contract for `__rust_dealloc(ptr, cap, 1)` freeing a non-empty-capacity `vecU8Buf`
while carrying `FsInv F0 T0` and `stackAt fsp calleeStk`. -/
abbrev DeallocBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

def deallocVecBufCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DeallocBufGhost where
  pre := fun (cap, ptr, bs, fsp) s =>
    ⌜FsInv F0 T0 s ∧ cap ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp⌝ ∗
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (_cap, _ptr, _bs, fsp) s0 sf =>
    ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk ∗ A.pool

theorem deallocVecBuf_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles} {T0 : List TraceEvent}
    {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
          "__rustc::__rust_dealloc")))
      ((deallocVecBufCellsSpec A F0 T0 calleeStk).inImage img) := by
  have hDealloc0 := subroutine_ok_withFsInv hFs
    (dealloc_ok_at_norm_ext_x hC (name := kpkGetPollName)
      (k := num% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      (by rw [kpkGetPoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")]))
    F0 T0
  refine subroutine_ok_outcome_intro fun ⟨cap, ptr, bs, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (deallocVecBufCellsSpec A F0 T0 calleeStk).pre (cap, ptr, bs, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [deallocVecBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hcap, hx0, hx1, hx2, hfsp⟩, hmem⟩
  subst hfsp
  unfold SpqrV1.Alloc.vecU8Buf at hmem
  have hcap0 : ¬(cap = 0) := hcap
  simp only [hcap0, ite_false] at hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hbs_le, hcap_lt, _⟩, hmem⟩
  have hcap_pos : 0 < cap.toNat := by
    by_cases hz : cap.toNat = 0
    · exact (hcap (BitVec.eq_of_toNat_eq hz)).elim
    · omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  have hreg : (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
    have heq : cap.toNat = bs.length + (cap.toNat - bs.length) := by omega
    conv_rhs => rw [heq]
    rw [memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨
      (withFsInv ((rustDeallocExternSpecWithStack A extHookStack).inImage img) F0 T0).pre
        (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by simp [hx1], by simp [hx2], hlay⟩, ?_⟩
    convert hmem_reg using 1; ac_rfl
  refine hDealloc0.mono_outcome (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, deallocVecBufCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨⟨hfsf, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [withFsInv, Spec.inImage, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, Spec.inImage, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, Spec.inImage, rustDeallocExternSpecWithStack] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

/-! ## `decimal` wrapper with `FsInv` and cell decomposition -/

abbrev DecimalCellsGhost :=
  BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def decimalFsCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DecimalCellsGhost where
  pre := fun (n, ret, o0, o1, o2, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = n ∧ s.sp = fsp⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (n, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName n).length) ∗
      SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName n) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decimal_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles} {T0 : List TraceEvent}
    {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
          "libsignal_cli::stores::decimal")))
      ((decimalFsCellsSpec A F0 T0 calleeStk).inImage img) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDecimal F0 T0
  rw [Program.fnAddr_rel (name := kpkGetPollName) kpkGetPoll_fnOff decimal_fnOff
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
      "libsignal_cli::stores::decimal"))
    (by decide)] at hDec0
  refine subroutine_ok_outcome_intro fun ⟨n, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (decimalFsCellsSpec A F0 T0 calleeStk).pre (n, ret, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [decimalFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨n, ret⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (decimalSpec A img decStk) F0 T0).pre callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [decimalSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    dsimp only
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hDec0.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, decimalSpec, decimalFsCellsSpec, callG, keyName] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfsf, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, Spec.inImage, decimalSpec, decimalFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    have hp := hq.2
    rw [← sepConj_assoc] at hp
    exact allowPanic_frame _root_.id hp
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, decimalSpec, Spec.inImage] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

/-! ## `Dir::get` wrapper with `FsInv` (`s0.fs.files = F0`) and 6-word result decomposition -/

/-- Decomposed outcome of `Dir::get` at a 6-word (`48`-byte) stack slot `ret`. -/
def dirGetPostProp (rd : ReadRule) (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (dir : DirGhost) (keyId : BitVec 32) (sf : State)
    (r : Except Unit (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) : Prop :=
  match r with
  | .ok bs =>
    dir.get rd F0 (keyName keyId) = .ok bs ∧
    FsInv F0 T0 sf ∧
    sf.trace = T0 ∧
    w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
    w3 = BitVec.ofNat 64 bs.length ∧
    H = SpqrV1.Alloc.vecU8Buf A w1 w2 bs
  | .error () =>
    w0 = 0x8000000000000001#64 ∧
    (dir.get rd F0 (keyName keyId) = .error () ∧ sf.trace = T0) ∧
    (∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64 0x8000000000000001#64
        w1 w2 w3 w4 w5 t7 t8 t9 t10 ∗ H ⊢ kpkAnsAt A out .readErr)

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 32 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def dirGetFsCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ PkNameOk pathOk dir keyId ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName keyId).length ∧ s.sp = fsp⌝ ∗
    dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, keyId, nCap, nPtr, _o0, _o1, _o2, _o3, _o4, _o5, fsp) _s0 sf =>
    ∃∗ r : Except Unit (List (BitVec 8)),
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ H : SepProp,
      ⌜dirGetPostProp rd A F0 T0 dir keyId sf r w0 w1 w2 w3 w4 w5 H⌝ ∗
      words6At ret w0 w1 w2 w3 w4 w5 ∗ H ∗
      dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirGet_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent} {getStk calleeStk : Nat}
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
          "<libsignal_cli::stores::Dir>::get")))
      ((dirGetFsCellsSpec rd pathOk A F0 T0 calleeStk).inImage img) := by
  have hGet0 := subroutine_ok_withFsInv hFs hGet F0 T0
  rw [Program.fnAddr_rel (name := kpkGetPollName) kpkGetPoll_fnOff dirGet_fnOff
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
      "<libsignal_cli::stores::Dir>::get"))
    (by decide)] at hGet0
  refine subroutine_ok_outcome_intro
    fun ⟨ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp⟩
      R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dirGetFsCellsSpec rd pathOk A F0 T0 calleeStk).pre
      (ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dirGetFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, ⟨hnlen, hdlen, hpOk⟩, hx0, hx1, hx2, hx3, hfsp⟩, hmem⟩
  subst hfsp
  have hfiles : s0.fs.files = F0 :=
    hfs0.files_eq (evs := []) (by simp [htr0]) (by intro _ h; cases h)
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName keyId).length := by
    rw [hx3, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  let nRest := vecU8BufRest A nCap nPtr (keyName keyId)
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hmem_sp : s0.mem ⊨ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
      (dirAt A self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hmem_bor : s0.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
      (dirAt A self dir ∗ words6At ret o0 o1 o2 o3 o4 o5 ∗
        stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) :=
    Satisfies.mono (sepConj_mono_left (vecU8Buf_split_raw A nCap nPtr (keyName keyId))) hmem_sp
  let callG : DirGetGhost := ⟨ret, self, dir, nPtr, keyName keyId, false⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (dirGetSpec rd pathOk A img getStk) F0 T0).pre callG s0 ∗
        (nRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [dirGetSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    dsimp only
    rw [memRegion_48_words6]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk⟩, ?_⟩
    rw [bytesAt_false_eq]
    convert hmem_bor using 1; ac_rfl
  refine hGet0.mono_outcome callG (nRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, dirGetSpec, dirGetFsCellsSpec, callG] at hq ⊢
    rw [hfiles, bytesAt_false_eq] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hr_disj, hq⟩
    have hq_unbor : sf.mem ⊨ ((nPtr ↦ₛ keyName keyId) ∗ nRest) ∗
        (getResultAt A ret r ∗ dirAt A self dir ∗ stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) := by
      convert hq using 1; ac_rfl
    have hq_rest : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
        (getResultAt A ret r ∗ dirAt A self dir ∗ stackAt s0.sp getStk ∗ A.pool ∗ stkRem ∗ R) :=
      Satisfies.mono (sepConj_mono_left (vecU8Buf_unsplit_raw A nCap nPtr (keyName keyId))) hq_unbor
    clear hq hq_unbor
    rcases r with ⟨⟩ | bs
    ·
      dsimp only [getResultAt, speAt, strRefAt, vecU8] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨fPtr, msgBs, sCap, sPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hspe1 : speWord 1 = 0x8000000000000001#64 := by decide
      have herr_tag : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = errTag := by decide
      let H := SpqrV1.Alloc.vecU8Buf A sCap sPtr msgBs ∗ (fPtr ↦ᵣ utf8 "read")
      refine ⟨.error (), 0x8000000000000001#64, sCap, sPtr,
        BitVec.ofNat 64 msgBs.length, fPtr, BitVec.ofNat 64 (utf8 "read").length, H, ?_⟩
      have hprop : dirGetPostProp rd A F0 T0 dir keyId sf (.error ())
          0x8000000000000001#64 sCap sPtr (BitVec.ofNat 64 msgBs.length)
          fPtr (BitVec.ofNat 64 (utf8 "read").length) H := by
        refine ⟨rfl, ⟨hr_disj.1.symm, hr_disj.2.trans htr0⟩, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, errResultAt, speAt, vecU8]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        have h40_eq : out + 8#64 + 32#64 = out + 40#64 := by bv_omega
        rw [herr_tag, ← hspe1, h8_eq, h16_eq, h40_eq]
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h32
        have hv : ((out + 16#64) ↦₆₄ sCap) ∗ ((out + 24#64) ↦₆₄ sPtr) ∗
            ((out + 32#64) ↦₆₄ BitVec.ofNat 64 msgBs.length) ∗
            SpqrV1.Alloc.vecU8Buf A sCap sPtr msgBs ⊢
            ∃∗ bs0 : List (BitVec 8), ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 16#64) c0 p0 bs0 := by
          refine Entails.trans ?_
            (Entails.sepExists_right msgBs
              (Entails.sepExists_right sCap
                (Entails.sepExists_right sPtr (Entails.refl _))))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq (by ac_rfl)
        have hf : ((out + 40#64) ↦₆₄ fPtr) ∗
            ((out + 48#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (fPtr ↦ᵣ utf8 "read") ⊢
            strRefAt (out + 40#64) (utf8 "read") := by
          unfold strRefAt
          refine Entails.sepExists_right fPtr ?_
          have h48_eq : out + 40#64 + asm64% boxSliceLenOff = out + 48#64 := by bv_omega
          rw [h48_eq]
          exact Entails.refl _
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right (sepConj_mono hv hf)) h32))
        exact entails_of_eq (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, H, stkRem] at hq ⊢
      rw [hspe1] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; ac_rfl
    ·
      rcases hr_disj with ⟨hget_eq, htr_eq⟩
      dsimp only [getResultAt, vecResultAt, vecU8] at hq_rest
      rw [memRegion_16_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest
      rcases hq_rest with ⟨g5, g4, bCap, bPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      have hok_tag : okTagVec = 0xFFFFFFFFFFFFFFFE#64 := by decide
      refine ⟨.ok bs, 0xFFFFFFFFFFFFFFFE#64, bCap, bPtr,
        BitVec.ofNat 64 bs.length, g4, g5, SpqrV1.Alloc.vecU8Buf A bCap bPtr bs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hget_eq.symm, hfsf, htr_eq.trans htr0, rfl, rfl, rfl⟩, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words6At, stkRem] at hq ⊢
      rw [hok_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, Spec.inImage, dirGetSpec, dirGetFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    have hp : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (nRest ∗ stkRem)) ∗ R := by
      have h := hq.2
      convert h using 1; ac_rfl
    exact allowPanic_frame _root_.id hp
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, dirGetSpec, Spec.inImage] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

/-! ## `decode_kyber_pre_key` wrapper (`0 < bytes.length` explicit in precondition) -/

private theorem kyberDeserialize_eq (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

/-- Decomposed outcome of `decode_kyber_pre_key` at an 11-word (`88`-byte) stack slot `ret`. -/
def decodePostProp (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (bytes : List (BitVec 8)) (sf : State)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) (H : SepProp) : Prop :=
  FsInv F0 T0 sf ∧ sf.trace = T0 ∧
  match KyberPreKeyRecord.deserialize bytes with
  | .ok r =>
    w0.toNat < 2 ^ 63 ∧
    (∀ out, words11At out w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗ H ⊢ kpkAnsAt A out (.found r))
  | .error e =>
    w0 = 0xFFFFFFFFFFFFFFFF#64 ∧
    (∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64 w1 w2 w3 w4 w5 w6 t7 t8 t9 t10 ∗ H ⊢
        kpkAnsAt A out (.decodeErr e))

abbrev DecodeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def decodeFsCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DecodeCellsGhost where
  pre := fun (ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32 ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧ s.sp = fsp⌝ ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, bCap, bPtr, bytes, _o0, _o1, _o2, _o3, _o4, _o5, _o6, _o7, _o8, _o9, _o10, fsp)
      _s0 sf =>
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ H : SepProp,
      ⌜decodePostProp A F0 T0 bytes sf w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 H⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗ H ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decode_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {F0 : FsFiles} {T0 : List TraceEvent}
    {calleeStk : Nat}
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName +
        BitVec.ofNat 64 (num% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
          "libsignal_cli::stores::decode_kyber_pre_key")))
      ((decodeFsCellsSpec A F0 T0 calleeStk).inImage img) := by
  have hDec0 := subroutine_ok_withFsInv hFs hDec F0 T0
  rw [Program.fnAddr_rel (name := kpkGetPollName) kpkGetPoll_fnOff decodeKyberPreKey_fnOff
    (k := num% (ls_rel%
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}"
      "libsignal_cli::stores::decode_kyber_pre_key"))
    (by decide)] at hDec0
  refine subroutine_ok_outcome_intro
    fun ⟨ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp⟩
      R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (decodeFsCellsSpec A F0 T0 calleeStk).pre
      (ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [decodeFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfs0, htr0, hlen_pos, hlen_lt, hx0, hx1, hx2, hfsp⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let bRest := vecU8BufRest A bCap bPtr bytes
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  have hmem_sp : s0.mem ⊨ SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hmem_bor : s0.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
      (words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
        stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) :=
    Satisfies.mono (sepConj_mono_left (vecU8Buf_split_raw A bCap bPtr bytes)) hmem_sp
  let callG : DecodeGhost := ⟨bPtr, bytes, ret⟩
  have hpre0 : s0.mem ⊨
      (withFsInv (decodeKyberPreKeySpec A img) F0 T0).pre callG s0 ∗
        (bRest ∗ stkRem ∗ R) := by
    refine withFsInv_pre_intro hfs0 ?_
    dsimp only [decodeKyberPreKeySpec, callG]
    refine satisfies_inImage_pre hinv ?_
    dsimp only
    rw [memRegion_88_words11]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt⟩, ?_⟩
    convert hmem_bor using 1; ac_rfl
  refine hDec0.mono_outcome callG (bRest ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfsf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, decodeKyberPreKeySpec, decodeFsCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr_eq, hq⟩
    have hq_unbor : sf.mem ⊨ ((bPtr ↦ₛ bytes) ∗ bRest) ∗
        (kyberPreKeyResultAt A ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) := by
      convert hq using 1; ac_rfl
    have hq_rest : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
        (kyberPreKeyResultAt A ret (KyberPreKeyRecord.deserialize bytes) ∗
          stackAt s0.sp smallRootStack ∗ A.pool ∗ stkRem ∗ R) :=
      Satisfies.mono (sepConj_mono_left (vecU8Buf_unsplit_raw A bCap bPtr bytes)) hq_unbor
    clear hq hq_unbor
    have hdes := kyberDeserialize_eq bytes
    cases hsd : SignedPreKeyRecordStructure.decode bytes with
    | none =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, errResultAt, speAt] at hq_rest
      rw [show (asm% (speSize - spePayloadOff)) = 40 by rfl,
        show (88 - asm% (resultErrSpeOff + speSize)) = 32 by rfl,
        memRegion_40_cells, memRegion_32_cells] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest ⊢
      rcases hq_rest with ⟨w10, w9, w8, w7, w6, w5, w4, w3, w2, hq⟩
      have herr_tag : errTag = 0xFFFFFFFFFFFFFFFF#64 := by decide
      refine ⟨0xFFFFFFFFFFFFFFFF#64, speWord 2, w2, w3, w4, w5, w6, w7, w8, w9, w10, emp, ?_⟩
      have hprop : decodePostProp A F0 T0 bytes sf
          0xFFFFFFFFFFFFFFFF#64 (speWord 2) w2 w3 w4 w5 w6 w7 w8 w9 w10 emp := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, rfl, fun out t7 t8 t9 t10 => ?_⟩
        dsimp only [words11At, kpkAnsAt, pkAnsAt, kyberPreKeyResultAt, errResultAt, speAt]
        have h8_eq : out + asm64% resultErrSpeOff = out + 8#64 := by bv_omega
        have h16_eq : out + 8#64 + asm64% spePayloadOff = out + 16#64 := by bv_omega
        rw [h8_eq, h16_eq, ← herr_tag, sepConj_emp]
        have h40 := words5_entails_memRegion_40 (out + 16#64) w2 w3 w4 w5 w6
        have h32 := words4_entails_memRegion_32 (out + 56#64) t7 t8 t9 t10
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40 h32
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono (sepConj_mono_right h40) h32))
        exact entails_of_eq (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      dsimp only [words11At, stkRem] at hq ⊢
      rw [herr_tag] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq ⊢
      convert hq using 1; ac_rfl
    | some m =>
      rw [hsd] at hdes
      rw [hdes] at hq_rest
      dsimp only [kyberPreKeyResultAt, signedPreKeyStructAt, vecU8] at hq_rest
      rw [memRegion_eq_exists_bytes (ret + 0x54#64) 4 (by decide)] at hq_rest
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq_rest ⊢
      rcases hq_rest with ⟨pad4, sigCap, sigPtr, skCap, skPtr, pkCap, pkPtr, hq⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf,
        SpqrV1.Alloc.vecU8At_eq_header_sep_buf,
        SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
      dsimp only [vecHeader] at hq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
      have hpk_ex : sf.mem ⊨ SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length)) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           (⌜pad4.length = 4⌝ ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      have hpk_lt : pkCap.toNat < 2 ^ 63 := vecU8Buf_cap_lt hpk_ex
      clear hpk_ex
      have hpad_ex : sf.mem ⊨ ⌜pad4.length = 4⌝ ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗ ((ret + 80#64) ↦₃₂ m.id) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      rw [satisfies_pure_sepConj] at hpad_ex
      rcases hpad_ex with ⟨hpad_len, hq_nopad⟩
      have hlen8 : (unpack32 m.id ++ pad4).length = 8 := by simp [hpad_len]
      obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 hlen8
      have htail_word : ∀ a : BitVec 64,
          ((a + 0x50#64) ↦₃₂ m.id) ∗ ((a + 0x54#64) ↦ₛ pad4) =
            ((a + 0x50#64) ↦₆₄ w10) := fun a => by
        rw [pointsTo32_eq_pointsToBytes, pointsTo64_eq_pointsToBytes, ← hw10,
          pointsToBytes_append, unpack32_length]
        have ha : a + 0x50#64 + BitVec.ofNat 64 4 = a + 0x54#64 := by bv_omega
        rw [ha]
      let H := SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ∗
        SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey ∗
        SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature
      refine ⟨pkCap, pkPtr, BitVec.ofNat 64 m.publicKey.length,
        skCap, skPtr, BitVec.ofNat 64 m.privateKey.length,
        sigCap, sigPtr, BitVec.ofNat 64 m.signature.length,
        m.timestamp, w10, H, ?_⟩
      have hprop : decodePostProp A F0 T0 bytes sf
          pkCap pkPtr (BitVec.ofNat 64 m.publicKey.length)
          skCap skPtr (BitVec.ofNat 64 m.privateKey.length)
          sigCap sigPtr (BitVec.ofNat 64 m.signature.length)
          m.timestamp w10 H := by
        unfold decodePostProp
        rw [hdes]
        refine ⟨hfsf, htr_eq.trans htr0, hpk_lt, fun out => ?_⟩
        unfold words11At kpkAnsAt pkAnsAt kyberPreKeyResultAt signedPreKeyStructAt vecU8
        have h80 : out + 80#64 = out + 0x50#64 := rfl
        rw [h80, ← htail_word out]
        have hv1 : (out ↦₆₄ pkCap) ∗ ((out + 8#64) ↦₆₄ pkPtr) ∗
            ((out + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64, vecU8At A out c0 p0 m.publicKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right pkCap (Entails.sepExists_right pkPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          exact entails_of_eq (by ac_rfl)
        have hv2 : ((out + 24#64) ↦₆₄ skCap) ∗ ((out + 32#64) ↦₆₄ skPtr) ∗
            ((out + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 0x18#64) c0 p0 m.privateKey := by
          refine Entails.trans ?_
            (Entails.sepExists_right skCap (Entails.sepExists_right skPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq (by ac_rfl)
        have hv3 : ((out + 48#64) ↦₆₄ sigCap) ∗ ((out + 56#64) ↦₆₄ sigPtr) ∗
            ((out + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature ⊢
            ∃∗ c0 : BitVec 64, ∃∗ p0 : BitVec 64,
              vecU8At A (out + 0x30#64) c0 p0 m.signature := by
          refine Entails.trans ?_
            (Entails.sepExists_right sigCap (Entails.sepExists_right sigPtr (Entails.refl _)))
          rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
          dsimp only [vecHeader]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact entails_of_eq (by ac_rfl)
        have hpad_ent : ((out + 0x54#64) ↦ₛ pad4) ⊢ memRegion (out + 0x54#64) 4 := by
          rw [← hpad_len]
          exact pointsToBytes_entails_memRegion (out + 0x54#64) pad4
        dsimp only [H]
        refine Entails.trans ?_
          (sepConj_mono hv1
            (sepConj_mono hv2
              (sepConj_mono hv3
                (sepConj_mono_right (sepConj_mono_right hpad_ent)))))
        exact entails_of_eq (by ac_rfl)
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hprop, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      have hre_pad : ((ret + 80#64) ↦₃₂ m.id) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           ((ret + 84#64) ↦ₛ pad4) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) =
          (((ret + 80#64) ↦₃₂ m.id) ∗ ((ret + 84#64) ↦ₛ pad4)) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by ac_rfl
      have hq_w10 : sf.mem ⊨ ((ret + 80#64) ↦₆₄ w10) ∗
          (((ret ↦₆₄ pkCap) ∗ ((ret + 8#64) ↦₆₄ pkPtr) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A pkCap pkPtr m.publicKey) ∗
           (((ret + 24#64) ↦₆₄ skCap) ∗ ((ret + 32#64) ↦₆₄ skPtr) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A skCap skPtr m.privateKey) ∗
           (((ret + 48#64) ↦₆₄ sigCap) ∗ ((ret + 56#64) ↦₆₄ sigPtr) ∗
            ((ret + 64#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
            SpqrV1.Alloc.vecU8Buf A sigCap sigPtr m.signature) ∗
           ((ret + 72#64) ↦₆₄ m.timestamp) ∗
           SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗
           (stkRem ∗ R)) := by
        rw [show ret + 80#64 = ret + 0x50#64 from rfl, ← htail_word ret, ← hre_pad]
        convert hq_nopad using 1; ac_rfl
      dsimp only [words11At, H, stkRem] at hq_w10 ⊢
      convert hq_w10 using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, Spec.inImage, decodeKyberPreKeySpec, decodeFsCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    have hp : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (bRest ∗ stkRem)) ∗ R := by
      have h := hq.2
      convert h using 1; ac_rfl
    exact allowPanic_frame _root_.id hp
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · dsimp only [withFsInv, decodeKyberPreKeySpec, Spec.inImage] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

/-! ## Inner poll specification & outer bridge (`kpkGetPoll_of_inner`) -/

def cliKpkGetPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (calleeStk : Nat) : Spec KpkPollGhost where
  pre := fun x s =>
    ⌜FsInv s.fs.files s.trace s ∧
      s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
      PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      memRegion x.out 88 ∗
      A.pool ∗ stackAt (s.sp - 432#64) calleeStk ∗ cells (s.sp - 432#64) 54
  post := fun x s0 sf =>
    (∃∗ ans : PkAns KyberPreKeyRecord,
      ⌜ans = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
          sf.trace = s0.trace⌝ ∗
      kpkAnsAt A x.out ans) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 1#8) ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      A.pool ∗ stackAt (s0.sp - 432#64) calleeStk ∗ cells (s0.sp - 432#64) 54
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem kpkGetPoll_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName)
        ((cliKpkGetPollInnerSpec rd pathOk A calleeStk).inImage img))
    (hstk : 0x1b0 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkGetPollName)
      (kpkGetPollSpec rd pathOk A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
      PkSizeOk rd s0.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s0.fs.files x.kg.lastResort x.id⌝ ∗
      pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.kg.oneTime ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hn1, hn2, hs1, hs2⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        memRegion x.out 88 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 432 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
    stackAt_kpkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 432))
  have hpre_in : s0.mem ⊨
      ((cliKpkGetPollInnerSpec rd pathOk A calleeStk).inImage img).pre x s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [cliKpkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨withFsInv_entry s0, hx0, hx8, hn1, hn2, hs1, hs2⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, cliKpkGetPollInnerSpec, kpkGetPollSpec, pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
      stackAt_kpkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, cliKpkGetPollInnerSpec, kpkGetPollSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
