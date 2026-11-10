/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Fs

/-!
# Frame Layout and Callee Cell Wrappers for `get_pre_key::{closure#0}`

Relative callee address equations, stack-frame and sret decompositions, cell-level wrappers for
`__rust_dealloc`, `decimal`, `Dir::get`, `PreKeyRecord::deserialize`, and `dropSpeWordSpec`, and
the 32-cell inner specification `pkGetPollInnerSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## 1. Symbolic relative-address lemmas -/

theorem decimal_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decimalName =
      (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "libsignal_cli::stores::decimal") := by
  have h1 := pkGetPoll_fnOff
  have h2 := decimal_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPollName, decimalName, h1, h2]
  bv_omega

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dirGetName =
      (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "<libsignal_cli::stores::Dir>::get") := by
  have h1 := pkGetPoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPollName, dirGetName, h1, h2]
  bv_omega

theorem pkDec_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr preKeyDeserializeName =
      (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName -
        bv% (ls_rel%
          "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize"
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") := by
  have h1 := pkGetPoll_fnOff
  have h2 := preKeyDeserialize_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPollName,
    preKeyDeserializeName, h1, h2]
  bv_omega

theorem dropSpe_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr cliDropSpeName =
      (tripleRatchetProgAtExt b ext).fnAddr pkGetPollName -
        bv% (ls_rel%
          "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#3]"
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}") := by
  have h1 := pkGetPoll_fnOff
  have h2 := cliDropSpe_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, pkGetPollName, cliDropSpeName, h1, h2]
  bv_omega

/-! ## 2. Stack and `memRegion` cell decompositions -/

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

theorem stackAt_pkPoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 256 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 256) =
      stackAt (sp - 256#64) calleeStk ∗ cells (sp - 256#64) 32 :=
  ProofLib.stackAt_split_cells sp calleeStk 32 hhi

theorem sp_sub_256_spAligned {s0 s : State} (hal0 : s0.spAligned = true)
    (hsp : s.sp = s0.sp - 256#64) : s.spAligned = true := by
  simp only [State.spAligned, hsp] at hal0 ⊢
  revert hal0
  generalize s0.sp = p
  bv_bits

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

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 16 + 24 by rfl, memRegion_split a 16 24 (by decide),
    memRegion_16_cells, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_cells (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        (a ↦₆₄ v5) ∗ ((a + 8#64) ↦₆₄ v4) ∗ ((a + 16#64) ↦₆₄ v3) ∗
        ((a + 24#64) ↦₆₄ v2) ∗ ((a + 32#64) ↦₆₄ v1) ∗ ((a + 40#64) ↦₆₄ v0)) := by
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_56_cells (a : BitVec 64) :
    memRegion a 56 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64,
        (a ↦₆₄ v6) ∗ ((a + 8#64) ↦₆₄ v5) ∗ ((a + 16#64) ↦₆₄ v4) ∗
        ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v2) ∗
        ((a + 40#64) ↦₆₄ v1) ∗ ((a + 48#64) ↦₆₄ v0)) := by
  rw [show (56 : Nat) = 8 + 48 by rfl, memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_eight, memRegion_48_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem words5_entails_memRegion40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) ⊢ memRegion a 40 := by
  rw [memRegion_40_cells a]
  exact Entails.sepExists_right w4 (Entails.sepExists_right w3
    (Entails.sepExists_right w2 (Entails.sepExists_right w1
      (Entails.sepExists_right w0 (Entails.refl _)))))

private theorem sepProp_eq_of_entails {P Q : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ P) : P = Q :=
  Entails.antisymm h1 h2

private theorem sepExists_congr {α : Type} {f g : α → SepProp} (h : ∀ x, f x = g x) :
    (∃∗ x, f x) = (∃∗ x, g x) :=
  congrArg sepExists (funext h)

private theorem pure_true_eq_emp {P : Prop} (h : P) : (⌜P⌝ : SepProp) = emp := by
  rw [eq_true h]
  exact pure_true

private theorem pointsTo32_memRegion4_eq (a : BitVec 64) (lo : BitVec 32) :
    ((a ↦₃₂ lo) ∗ memRegion (a + 4#64) 4) =
      ∃∗ hi : BitVec 32, (a ↦₆₄ (hi ++ lo)) := by
  rw [ProofLib.memRegion_four (a + 4#64)]
  simp only [sepExists_sepConj_right]
  apply sepExists_congr; intro hi
  have hlo : BitVec.extractLsb' 0 32 (hi ++ lo) = lo := by bv_bits
  have hhi : BitVec.extractLsb' 32 32 (hi ++ lo) = hi := by bv_bits
  rw [ProofLib.pointsTo64_split32 a (hi ++ lo), hlo, hhi]

private theorem pointsTo64_entails_pointsTo32_memRegion4 (a w : BitVec 64) :
    (a ↦₆₄ w) ⊢ (a ↦₃₂ w.extractLsb' 0 32) ∗ memRegion (a + 4#64) 4 := by
  rw [ProofLib.pointsTo64_split32 a w, ProofLib.memRegion_four (a + 4#64)]
  exact sepConj_mono_right (Entails.sepExists_right (w.extractLsb' 32 32) (Entails.refl _))

/-! ## 3. `vecU8Buf` slice borrowing and `__rust_dealloc` cell wrapper -/

def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8Buf_eq_bytes_sep_rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs =
      (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  by_cases hc : cap = 0
  · subst hc
    apply sepProp_eq_of_entails
    · apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hbs
      simp only [pointsToBytes_nil, emp_sepConj, ↓reduceIte]
      rw [pure_true_eq_emp ⟨hlen, hlt, hptr⟩, sepConj_emp]
      exact Entails.refl _
    · simp only [↓reduceIte, sepConj_emp]
      rw [sepConj_comm]
      apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hbs
      simp only [pointsToBytes_nil]
      rw [pure_true_eq_emp ⟨hlen, hlt, hptr⟩]
      exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    ac_rfl

theorem bytes_sep_vecU8BufRest_zero (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((ptr ↦ₛ bs) ∗ vecU8BufRest A 0#64 ptr bs) = ⌜bs = [] ∧ ptr ≠ 0⌝ := by
  rw [← vecU8Buf_eq_bytes_sep_rest]
  unfold SpqrV1.Alloc.vecU8Buf
  have hz : ((0#64 : BitVec 64) = 0) = True := eq_true rfl
  apply sepProp_eq_of_entails
  · apply Entails.pure_left; rintro ⟨hlen, _, hptr⟩
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hbs
    simp only [hz, ↓reduceIte]
    rw [pure_true_eq_emp ⟨trivial, hptr⟩]
    exact Entails.refl _
  · apply Entails.pure_left_only; rintro ⟨rfl, hptr⟩
    simp only [hz, ↓reduceIte]
    rw [pure_true_eq_emp ⟨by decide, by decide, hptr⟩, emp_sepConj]
    exact Entails.refl _

private theorem vecU8_eq_words_sep_bytes_rest (A : RustAlloc) (v : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold vecU8
  apply sepExists_congr; intro cap
  apply sepExists_congr; intro ptr
  rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf, vecU8Buf_eq_bytes_sep_rest]
  dsimp only [vecHeader]
  ac_rfl

private theorem vecU8_intro_of_buf (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A cap ptr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A cap ptr bs =
      vecU8At A v cap ptr bs := by
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

private theorem bytes_sep_memRegion_entails_memRegion (ptr : BitVec 64) (bs : List (BitVec 8))
    {cap : Nat} (hlen : bs.length ≤ cap) (hcap : cap ≤ 2 ^ 64) :
    ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap - bs.length)) ⊢
      memRegion ptr cap := by
  have heq : cap = bs.length + (cap - bs.length) := by omega
  conv_rhs => rw [heq]
  rw [memRegion_split ptr bs.length (cap - bs.length) (by omega),
    memRegion_eq_exists_bytes ptr bs.length (by omega)]
  apply sepConj_mono_left
  exact Entails.sepExists_right bs (Entails.pure_right rfl (Entails.refl _))

private theorem vecU8Buf_cap_add_one_ne_zero {m : Memory} {A : RustAlloc}
    {cap ptr : BitVec 64} {bs : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ R) : cap + 1#64 ≠ 0#64 := by
  unfold SpqrV1.Alloc.vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  have hlt := h.1.2.1
  bv_omega

abbrev DeallocCellsGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

def deallocBufCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DeallocCellsGhost where
  pre := fun (ptr, cap, bs, fsp) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64⌝ ∗
      (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ∗ A.pool ∗ stackAt fsp calleeStk
  post := fun (_ptr, _cap, _bs, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt fsp calleeStk

theorem dealloc_buf_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocBufCellsSpec A calleeStk).inImage img) := by
  have hDealloc := hC.dealloc_ok_at pkGetPollName
    (num% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}"
      "__rustc::__rust_dealloc"))
    (by rw [pkGetPoll_fnOff, ls_stub% "__rustc::__rust_dealloc"])
  refine subroutine_ok_outcome_intro fun ⟨ptr, cap, bs, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (deallocBufCellsSpec A calleeStk).pre (ptr, cap, bs, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [deallocBufCellsSpec, vecU8BufRest, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap0⟩, hmem⟩
  subst hfsp
  have hmem1 : s0.mem ⊨ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((ptr ↦ₛ bs) ∗ (if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        A.pool ∗ stackAt s0.sp calleeStk ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem1
  rcases hmem1 with ⟨⟨hlen, hlt, _hptr⟩, hmem2⟩
  have hcap0' : cap ≠ 0 := hcap0
  simp only [hcap0', ↓reduceIte] at hmem2
  rw [stackAt_sub_split s0.sp hle hhi] at hmem2
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hcap_pos : 0 < cap.toNat := by
    have : cap ≠ 0#64 := hcap0
    bv_omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  have hmem_reg : s0.mem ⊨ ((ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    dsimp only [stkRem]
    convert hmem2 using 1; ac_rfl
  have hmem_reg' : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (bytes_sep_memRegion_entails_memRegion ptr bs hlen (by omega))) hmem_reg
  have hpre0 : s0.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by simp [hx1], by simp [hx2], hlay⟩, ?_⟩
    convert hmem_reg' using 1; ac_rfl
  refine hDealloc.mono_outcome (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, deallocBufCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 4. `decimal` cell wrapper (carrying `FsInv` so `sf.fs.files = s0.fs.files`) -/

abbrev DecimalCellsGhost :=
  BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def decimalCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DecimalCellsGhost where
  pre := fun (n, ret, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = n ∧ s.sp = fsp⌝ ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      stackAt fsp calleeStk ∗ A.pool
  post := fun (n, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.fs.files = s0.fs.files⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName n).length) ∗
      (nPtr ↦ₛ keyName n) ∗ vecU8BufRest A nCap nPtr (keyName n) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decimal_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      ((decimalCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨n, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (decimalCellsSpec A calleeStk).pre (n, ret, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨n, ret⟩
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  have hpre0 : s0.mem ⊨ (withFsInv (decimalSpec A img decStk) s0.fs.files s0.trace).pre
      callG s0 ∗ (stkRem ∗ R) := by
    refine withFsInv_pre_intro (withFsInv_entry s0) ?_
    dsimp only [decimalSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hDecFs.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfs', hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, decimalSpec, decimalCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs' (evs := []) (by simp [htr]) NoFsEv.nil
    change sf.mem ⊨ (vecU8 A ret (keyName n) ∗ stackAt s0.sp decStk ∗ A.pool) ∗ (stkRem ∗ R) at hq
    rw [vecU8_eq_words_sep_bytes_rest] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpec A img decStk).onPanic callG s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨_, hq⟩
    dsimp only [Spec.inImage, decimalSpec, decimalCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpec A img decStk).onExit callG code s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (allowPanic_not_exited hq.2).elim
  · change sf.mem ⊨ (⌜FsInv s0.fs.files s0.trace sf⌝ ∗
      (decimalSpec A img decStk).onOom callG s0 sf) ∗ (stkRem ∗ R) at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    dsimp only [decimalSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

/-! ## 5. `Dir::get` cell wrapper and `.readErr` / `.missing` sret reassemblers -/

def readErrHeap (A : RustAlloc) (w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  ∃∗ ebs : List (BitVec 8),
    ⌜w3 = BitVec.ofNat 64 ebs.length ∧ w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
      SpqrV1.Alloc.vecU8Buf A w1 w2 ebs ∗ (w4 ↦ᵣ utf8 "read")

def dirGetPayload (A : RustAlloc) (r : Except Unit (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  match r with
  | .ok bs =>
    ⌜w0 = okTagVec ∧ w3 = BitVec.ofNat 64 bs.length⌝ ∗
      (w2 ↦ₛ bs) ∗ vecU8BufRest A w1 w2 bs
  | .error () =>
    ⌜w0 = speWord 1⌝ ∗ readErrHeap A w1 w2 w3 w4 w5

theorem readErr_reassemble (A : RustAlloc) (out w1 w2 w3 w4 w5 : BitVec 64) :
    ((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord 1) ∗
      ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗
      ((out + 32#64) ↦₆₄ w3) ∗ ((out + 40#64) ↦₆₄ w4) ∗
      ((out + 48#64) ↦₆₄ w5)) ∗ readErrHeap A w1 w2 w3 w4 w5 ⊢
      pkGetAnsAt A out .readErr := by
  unfold readErrHeap pkGetAnsAt pkAnsAt errResultAt speAt strRefAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, Nat.sub_self, memRegion_zero,
    sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro ebs
  have hpull :
      (((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord 1) ∗
          ((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗
          ((out + 32#64) ↦₆₄ w3) ∗ ((out + 40#64) ↦₆₄ w4) ∗
          ((out + 48#64) ↦₆₄ w5)) ∗
        (⌜w3 = BitVec.ofNat 64 ebs.length ∧ w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          SpqrV1.Alloc.vecU8Buf A w1 w2 ebs ∗ (w4 ↦ᵣ utf8 "read"))) =
      (⌜w3 = BitVec.ofNat 64 ebs.length ∧ w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
        ((((out + 16#64) ↦₆₄ w1) ∗ ((out + 24#64) ↦₆₄ w2) ∗ ((out + 32#64) ↦₆₄ w3)) ∗
          SpqrV1.Alloc.vecU8Buf A w1 w2 ebs) ∗
        ((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord 1) ∗
          ((out + 40#64) ↦₆₄ w4) ∗ ((out + 48#64) ↦₆₄ w5) ∗ (w4 ↦ᵣ utf8 "read"))) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; rintro ⟨rfl, rfl⟩
  refine Entails.sepExists_right w4 (Entails.sepExists_right ebs ?_)
  have hvec := vecU8_intro_of_buf A (out + 16#64) w1 w2 ebs
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hvec
  refine Entails.trans (sepConj_mono_left hvec) ?_
  exact Entails.of_eq (by ac_rfl)

theorem missing_reassemble (A : RustAlloc) (out w2 w3 w4 w5 w6 : BitVec 64) :
    ((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord 13) ∗
      ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗
      ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
      ((out + 48#64) ↦₆₄ w6)) ⊢
      pkGetAnsAt A out .missing := by
  dsimp only [pkGetAnsAt, pkAnsAt]
  have h5 := words5_entails_memRegion40 (out + 16#64) w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h5
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right h5))
  exact Entails.of_eq (by ac_rfl)

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def dirGetCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name)⌝ ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      ((ret + 24#64) ↦₆₄ o3) ∗ ((ret + 32#64) ↦₆₄ o4) ∗ ((ret + 40#64) ↦₆₄ o5) ∗
      stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nameA, name, _o0, _o1, _o2, _o3, _o4, _o5, fsp) s0 sf =>
    ∃∗ r : Except Unit (List (BitVec 8)),
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₆₄ w2) ∗
      ((ret + 24#64) ↦₆₄ w3) ∗ ((ret + 32#64) ↦₆₄ w4) ∗ ((ret + 40#64) ↦₆₄ w5) ∗
      dirGetPayload A r w0 w1 w2 w3 w4 w5 ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirGet_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk calleeStk : Nat}
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      ((dirGetCellsSpec rd pathOk A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro
    fun ⟨ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dirGetCellsSpec rd pathOk A calleeStk).pre
      (ret, self, dir, nameA, name, o0, o1, o2, o3, o4, o5, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnlen, hplen, hpok⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpec rd pathOk A img getStk).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [dirGetSpec, callG, SpqrV1.ChainProofs.bytesAt]
    refine satisfies_inImage_pre hinv ?_
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnlen, hplen, hpok⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hGet.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec, callG,
      SpqrV1.ChainProofs.bytesAt] at hq ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨r, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    rcases r with ⟨⟩ | bs
    · dsimp only [getResultAt, speAt, strRefAt] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w4, ebs, hq⟩
      have hq' : sf.mem ⊨ vecU8 A (ret + 8#64) ebs ∗
          ((ret ↦₆₄ speWord 1) ∗ ((ret + 32#64) ↦₆₄ w4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
            (w4 ↦ᵣ utf8 "read") ∗ dirAt A self dir ∗ (nameA ↦ₛ name) ∗
            stackAt s0.sp getStk ∗ A.pool ∗ (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      dsimp only [vecU8] at hq'
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
      rcases hq' with ⟨w1, w2, hq'⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq'
      dsimp only [vecHeader] at hq'
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq'
      refine ⟨.error (), speWord 1, w1, w2, BitVec.ofNat 64 ebs.length, w4,
        BitVec.ofNat 64 (utf8 "read").length, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload, readErrHeap]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      refine ⟨ebs, ?_⟩
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp trivial, emp_sepConj]
      dsimp only [stkRem] at hq'
      convert hq' using 1; ac_rfl
    · dsimp only [getResultAt, vecResultAt] at hq
      rw [vecU8_eq_words_sep_bytes_rest A (ret + 8#64) bs] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w1, w2, hq⟩
      rw [memRegion_16_cells (ret + 32#64)] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨w5, w4, hq⟩
      refine ⟨.ok bs, okTagVec, w1, w2, BitVec.ofNat 64 bs.length, w4, w5, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hdisj, ?_⟩
      dsimp only [dirGetPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirGetSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 6. `PreKeyRecord::deserialize` cell wrapper and `.decodeErr` / `.found` sret reassemblers -/

def pkDecPayload (A : RustAlloc) (res : Except SignalProtocolError PreKeyRecord)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 64) : SepProp :=
  match res with
  | .ok rec =>
    ⌜d0 + 1#64 ≠ 0#64 ∧
      d2 = BitVec.ofNat 64 rec.preKey.publicKey.length ∧
      d5 = BitVec.ofNat 64 rec.preKey.privateKey.length ∧
      d6.extractLsb' 0 32 = rec.preKey.id⌝ ∗
      SpqrV1.Alloc.vecU8Buf A d0 d1 rec.preKey.publicKey ∗
      SpqrV1.Alloc.vecU8Buf A d3 d4 rec.preKey.privateKey
  | .error e =>
    ⌜e = .invalidProtobufEncoding ∧ d0 = errTag ∧ d1 = speWord 2⌝

theorem decodeErr_reassemble (A : RustAlloc) (out : BitVec 64) (e : SignalProtocolError)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 64) :
    ((out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
      ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗
      ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
      ((out + 48#64) ↦₆₄ d6)) ∗ pkDecPayload A (.error e) d0 d1 d2 d3 d4 d5 d6 ⊢
      pkGetAnsAt A out (.decodeErr e) := by
  dsimp only [pkDecPayload]
  rw [sepConj_comm]
  apply Entails.pure_left; rintro ⟨rfl, rfl, rfl⟩
  dsimp only [pkGetAnsAt, pkAnsAt, preKeyResultAt, errResultAt, speAt]
  simp only [Nat.sub_self, memRegion_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have h5 := words5_entails_memRegion40 (out + 16#64) d2 d3 d4 d5 d6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h5
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right h5))
  exact Entails.of_eq (by ac_rfl)

theorem found_reassemble (A : RustAlloc) (out : BitVec 64) (rec : PreKeyRecord)
    (d0 d1 d2 d3 d4 d5 d6 : BitVec 64) :
    ((out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
      ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗
      ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
      ((out + 48#64) ↦₆₄ d6)) ∗ pkDecPayload A (.ok rec) d0 d1 d2 d3 d4 d5 d6 ⊢
      pkGetAnsAt A out (.found rec) := by
  dsimp only [pkDecPayload, pkGetAnsAt, pkAnsAt, preKeyResultAt, preKeyRecordAt]
  have hpull :
      (((out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗
          ((out + 16#64) ↦₆₄ d2) ∗ ((out + 24#64) ↦₆₄ d3) ∗
          ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5) ∗
          ((out + 48#64) ↦₆₄ d6)) ∗
        (⌜d0 + 1#64 ≠ 0#64 ∧
            d2 = BitVec.ofNat 64 rec.preKey.publicKey.length ∧
            d5 = BitVec.ofNat 64 rec.preKey.privateKey.length ∧
            d6.extractLsb' 0 32 = rec.preKey.id⌝ ∗
          SpqrV1.Alloc.vecU8Buf A d0 d1 rec.preKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A d3 d4 rec.preKey.privateKey)) =
      (⌜d0 + 1#64 ≠ 0#64 ∧
          d2 = BitVec.ofNat 64 rec.preKey.publicKey.length ∧
          d5 = BitVec.ofNat 64 rec.preKey.privateKey.length ∧
          d6.extractLsb' 0 32 = rec.preKey.id⌝ ∗
        (((out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2)) ∗
          SpqrV1.Alloc.vecU8Buf A d0 d1 rec.preKey.publicKey) ∗
        ((((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗ ((out + 40#64) ↦₆₄ d5)) ∗
          SpqrV1.Alloc.vecU8Buf A d3 d4 rec.preKey.privateKey) ∗
        ((out + 48#64) ↦₆₄ d6)) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; rintro ⟨_, rfl, rfl, hid⟩
  have hpub := vecU8_intro_of_buf A out d0 d1 rec.preKey.publicKey
  have hpriv := vecU8_intro_of_buf A (out + 24#64) d3 d4 rec.preKey.privateKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpriv
  have hid64 := pointsTo64_entails_pointsTo32_memRegion4 (out + 48#64) d6
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hid] at hid64
  refine Entails.trans (sepConj_mono_left hpub) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hpriv)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right hid64)) ?_
  exact Entails.of_eq (by ac_rfl)

abbrev PkDecCellsGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def pkDecCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec PkDecCellsGhost where
  pre := fun (bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = ret ∧ s.sp = fsp⌝ ∗
      (bytesA ↦ₛ bytes) ∗
      (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
      ((ret + 24#64) ↦₆₄ o3) ∗ ((ret + 32#64) ↦₆₄ o4) ∗ ((ret + 40#64) ↦₆₄ o5) ∗
      ((ret + 48#64) ↦₆₄ o6) ∗
      stackAt fsp calleeStk ∗ A.pool
  post := fun (bytesA, bytes, ret, _o0, _o1, _o2, _o3, _o4, _o5, _o6, fsp) s0 sf =>
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64,
    ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ d6 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ d0) ∗ ((ret + 8#64) ↦₆₄ d1) ∗ ((ret + 16#64) ↦₆₄ d2) ∗
      ((ret + 24#64) ↦₆₄ d3) ∗ ((ret + 32#64) ↦₆₄ d4) ∗ ((ret + 40#64) ↦₆₄ d5) ∗
      ((ret + 48#64) ↦₆₄ d6) ∗
      pkDecPayload A (PreKeyRecord.deserialize bytes) d0 d1 d2 d3 d4 d5 d6 ∗
      (bytesA ↦ₛ bytes) ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem pkDec_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      ((pkDecCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro
    fun ⟨bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (pkDecCellsSpec A calleeStk).pre
      (bytesA, bytes, ret, o0, o1, o2, o3, o4, o5, o6, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [pkDecCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblen, hx8, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let callG : DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hpre0 : s0.mem ⊨ (preKeyDeserializeSpec A img).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [preKeyDeserializeSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_56_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o6, o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hblen, hx8⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hDec.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, preKeyDeserializeSpec, pkDecCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    rcases hres : PreKeyRecord.deserialize bytes with e | rec
    · have he : e = .invalidProtobufEncoding := by
        have hloop := pkDeserialize_eq_of_decodeLoop bytes
        rw [hres] at hloop
        split at hloop
        · nomatch hloop
        · injection hloop
      subst he
      rw [hres] at hq
      dsimp only [preKeyResultAt, errResultAt, speAt] at hq
      simp only [Nat.sub_self, memRegion_zero, sepConj_emp, BitVec.add_assoc,
        BitVec.reduceAdd] at hq
      rw [memRegion_40_cells] at hq
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
        BitVec.add_assoc, BitVec.reduceAdd] at hq
      rcases hq with ⟨d6, d5, d4, d3, d2, hq⟩
      refine ⟨errTag, speWord 2, d2, d3, d4, d5, d6, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      dsimp only [pkDecPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      simp only [eq_self, and_self, pure_true_eq_emp trivial, emp_sepConj]
      dsimp only [stkRem] at hq
      convert hq using 1; ac_rfl
    · rw [hres] at hq
      dsimp only [preKeyResultAt, preKeyRecordAt] at hq
      have hq1 : sf.mem ⊨
          vecU8 A ret rec.preKey.publicKey ∗
          vecU8 A (ret + 24#64) rec.preKey.privateKey ∗
          (((ret + 48#64) ↦₃₂ rec.preKey.id) ∗ memRegion (ret + 52#64) 4) ∗
          ((bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗ (stkRem ∗ R)) := by
        convert hq using 1; ac_rfl
      have h52 : ret + 48#64 + 4#64 = ret + 52#64 := by bv_omega
      rw [← h52, pointsTo32_memRegion4_eq (ret + 48#64) rec.preKey.id] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨hi32, hq1⟩
      dsimp only [vecU8] at hq1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq1
      rcases hq1 with ⟨d3, d4, d0, d1, hq1⟩
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf, SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq1
      dsimp only [vecHeader] at hq1
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq1
      have hd0_ne : d0 + 1#64 ≠ 0#64 := by
        refine vecU8Buf_cap_add_one_ne_zero (m := sf.mem) (A := A) (cap := d0) (ptr := d1)
          (bs := rec.preKey.publicKey)
          (R := (ret ↦₆₄ d0) ∗ ((ret + 8#64) ↦₆₄ d1) ∗
            ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.publicKey.length) ∗
            ((ret + 24#64) ↦₆₄ d3) ∗ ((ret + 32#64) ↦₆₄ d4) ∗
            ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rec.preKey.privateKey.length) ∗
            SpqrV1.Alloc.vecU8Buf A d3 d4 rec.preKey.privateKey ∗
            ((ret + 48#64) ↦₆₄ (hi32 ++ rec.preKey.id)) ∗
            (bytesA ↦ₛ bytes) ∗ stackAt s0.sp smallRootStack ∗ A.pool ∗ (stkRem ∗ R)) ?_
        convert hq1 using 1; ac_rfl
      refine ⟨d0, d1, BitVec.ofNat 64 rec.preKey.publicKey.length,
        d3, d4, BitVec.ofNat 64 rec.preKey.privateKey.length, hi32 ++ rec.preKey.id, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨htr, ?_⟩
      dsimp only [pkDecPayload]
      rw [stackAt_sub_split s0.sp hle hhi]
      have hid_lo : (hi32 ++ rec.preKey.id).extractLsb' 0 32 = rec.preKey.id := by bv_bits
      rw [pure_true_eq_emp (⟨hd0_ne, rfl, rfl, hid_lo⟩ :
        d0 + 1#64 ≠ 0#64 ∧
          BitVec.ofNat 64 rec.preKey.publicKey.length =
            BitVec.ofNat 64 rec.preKey.publicKey.length ∧
          BitVec.ofNat 64 rec.preKey.privateKey.length =
            BitVec.ofNat 64 rec.preKey.privateKey.length ∧
          (hi32 ++ rec.preKey.id).extractLsb' 0 32 = rec.preKey.id), emp_sepConj]
      dsimp only [stkRem] at hq1
      convert hq1 using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, preKeyDeserializeSpec, pkDecCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [preKeyDeserializeSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 7. `drop_glue::<SignalProtocolError> [local#4]` cell wrapper -/

abbrev DropSpeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def dropSpeWordCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DropSpeCellsGhost where
  pre := fun (a, c1, c2, c3, c4, c5, fsp) s =>
    ⌜s.readReg64 .x0 = a ∧ s.sp = fsp⌝ ∗
      (a ↦₆₄ speWord 13) ∗
      ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗ ((a + 24#64) ↦₆₄ c3) ∗
      ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗
      A.pool ∗ stackAt fsp calleeStk
  post := fun (a, _c1, _c2, _c3, _c4, _c5, fsp) s0 sf =>
    ∃∗ m0 : BitVec 64, ∃∗ m1 : BitVec 64, ∃∗ m2 : BitVec 64,
    ∃∗ m3 : BitVec 64, ∃∗ m4 : BitVec 64, ∃∗ m5 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      (a ↦₆₄ m0) ∗ ((a + 8#64) ↦₆₄ m1) ∗ ((a + 16#64) ↦₆₄ m2) ∗
      ((a + 24#64) ↦₆₄ m3) ∗ ((a + 32#64) ↦₆₄ m4) ∗ ((a + 40#64) ↦₆₄ m5) ∗
      A.pool ∗ stackAt fsp calleeStk

theorem dropSpeWord_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      ((dropSpeWordCellsSpec A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨a, c1, c2, c3, c4, c5, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dropSpeWordCellsSpec A calleeStk).pre (a, c1, c2, c3, c4, c5, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost := ⟨a, 13⟩
  have hpre0 : s0.mem ⊨ (dropSpeWordSpec A img).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [dropSpeWordSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd]
    refine ⟨c5, c4, c3, c2, c1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inl trivial⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hDrop.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, dropSpeWordSpec, dropSpeWordCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    rw [memRegion_48_cells] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨m5, m4, m3, m2, m1, m0, hq⟩
    refine ⟨m0, m1, m2, m3, m4, m5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, dropSpeWordSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, dropSpeWordSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.inImage, dropSpeWordSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 8. Inner specification with 32 explicit frame cells and bridge to `pkGetPollSpec` -/

def pkGetPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec PkPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s.fs.files x.dir x.id⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 56 ∗
      A.pool ∗ stackAt (s.sp - 256#64) calleeStk ∗ cells (s.sp - 256#64) 32
  post := fun x s0 sf =>
    (∃∗ ans : PkAns PreKeyRecord,
      ⌜ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace⌝ ∗
      pkGetAnsAt A x.out ans) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A x.self x.dir ∗ A.pool ∗
      stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem pkGetPoll_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName)
        ((pkGetPollInnerSpec rd pathOk A calleeStk).inImage img))
    (hstk : 256 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetPollName)
      (pkGetPollSpec rd pathOk A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s0.fs.files x.dir x.id⌝ ∗
      pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 56 ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 13#64) 3 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 56 ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 256 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
    stackAt_pkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 13#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 256))
  have hpre_in : s0.mem ⊨ ((pkGetPollInnerSpec rd pathOk A calleeStk).inImage img).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [pkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, pkGetPollInnerSpec, pkGetPollSpec, pkGetPollSpecOf,
      pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 256) (by omega) hstk_hi,
      stackAt_pkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, pkGetPollInnerSpec, pkGetPollSpec, pkGetPollSpecOf] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
