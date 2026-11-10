/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommon
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpoch
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainEpochLoop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ChainStep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `spqr::decode_state`: `ChainPB` `links.push` & Tag 3 (`0x536ec..0x53770`)

**Checked by Lean.** Verifies strict length decrease of `.lengthDelimited` `Proto.mergeMessage`,
the 112-byte Q-register copy (`0x5371c`), `Vec<ChainEpochPB>::push` with `grow_one` (`0x5370c`),
and `ChainPB` tag 3 (`links`, `0x536ec`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem bv_ofNat_mul_112 (ptr : BitVec 64) (n : Nat) :
    ptr + BitVec.ofNat 64 n * 112#64 = ptr + BitVec.ofNat 64 (n * 112) := by
  rw [← BitVec.ofNat_mul]

theorem bv_ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

attribute [local simp, local arm64_norm] bv_ofNat_mul_112 bv_ofNat_add_one

/-! ## Pure & Spatial Helpers for `Vec<ChainEpochPB>::push` -/

theorem proto_mergeMessage_length_lt {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {m m' : M} {bs rest : List (BitVec 8)} {depth' : Nat}
    (h : (Proto.mergeMessage mergeField .lengthDelimited m bs (depth' + 1)).toOption = some (m', rest)) :
    rest.length < bs.length := by
  have hchk : Proto.checkWireType .lengthDelimited .lengthDelimited = .ok () := rfl
  simp only [Proto.mergeMessage, hchk, Bind.bind, Except.bind, takeExact_eq_take_drop] at h
  rcases hdv : Proto.decodeVarint bs with e | ⟨len64, restMid⟩
  · rw [hdv] at h; cases h
  · have hdv_opt : decodeVarint bs = some (len64, restMid) := by
      rw [← proto_decodeVarint_toOption, hdv]; rfl
    have hlt_mid : restMid.length < bs.length := decodeVarint_length hdv_opt
    rw [hdv] at h; dsimp only at h
    by_cases hle : len64.toNat ≤ restMid.length
    · rw [ite_eq_left_iff.mpr fun hnot => absurd hle hnot] at h; dsimp only at h
      rcases hloop : Proto.mergeFieldsLoop mergeField (restMid.take len64.toNat).length m
          (restMid.take len64.toNat) depth' with e | m''
      · rw [hloop] at h; cases h
      · rw [hloop] at h
        simp only [Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        rw [List.length_drop]
        omega
    · rw [ite_eq_right_iff.mpr fun hyes => absurd hyes hle] at h; cases h

theorem arrayAt_append_singleton {α : Type} (elemAt : α → BitVec 64 → SepProp) (stride : Nat)
    (ptr : BitVec 64) (xs : List α) (x : α) :
    arrayAt elemAt stride ptr xs ∗ elemAt x (ptr + BitVec.ofNat 64 (xs.length * stride)) =
      arrayAt elemAt stride ptr (xs ++ [x]) := by
  induction xs generalizing ptr with
  | nil =>
    simp only [arrayAt, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.nil_append, emp_sepConj, sepConj_emp]
  | cons y ys ih =>
    simp only [arrayAt, List.cons_append, List.length_cons]
    have hadd :
        ptr + BitVec.ofNat 64 ((ys.length + 1) * stride) =
          (ptr + BitVec.ofNat 64 stride) + BitVec.ofNat 64 (ys.length * stride) := by
      have hm : (ys.length + 1) * stride = stride + ys.length * stride := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
    rw [hadd, sepConj_assoc, ih (ptr + BitVec.ofNat 64 stride)]

theorem max_double_four_bound {cap : Nat} (hcap : cap ≤ 2 ^ 54) :
    max (2 * cap) 4 * 112 + 8 ≤ 2 ^ 63 ∧ max (2 * cap) 4 * 112 < 2 ^ 63 ∧
      cap < max (2 * cap) 4 ∧ max (2 * cap) 4 < 2 ^ 64 := by
  omega

theorem vecBuf_chainEpochPB_expose_bounds (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs := by
  unfold vecBuf
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.refl _

theorem vecBuf_chainEpochPB_of_lt (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hlt : xs.length < cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      memRegion (ptr + BitVec.ofNat 64 (xs.length * 112)) ((cap.toNat - xs.length) * 112) := by
  unfold vecBuf
  apply Entails.pure_left; intro _
  have hcap0 : cap ≠ 0 := by intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  exact Entails.refl _

theorem vecBuf_chainEpochPB_to_growOne_pre (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (hfull : xs.length = cap.toNat) :
    vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr xs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = cap.toNat * 112 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        (relocArrayAtChainEpochPB A xs).1 bs := by
  unfold vecBuf
  apply Entails.pure_left; rintro ⟨_, _, hptr⟩
  by_cases hcap0 : cap = 0
  · subst hcap0
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero hfull
    subst hxs
    simp only [↓reduceIte, BitVec.toNat_ofNat, Nat.zero_mul, relocArrayAtChainEpochPB]
    refine Entails.sepExists_right [] ?_
    apply Entails.pure_right ⟨rfl, hptr⟩
    simp only [sepConj_emp]
    exact Entails.refl _
  · have hcap0' : cap ≠ 0#64 := hcap0
    simp only [hcap0, hcap0', ↓reduceIte, hfull, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
    have hto := (relocArrayAtChainEpochPB A xs).2.to_bytes ptr
    refine Entails.trans (sepConj_mono_right hto) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    refine Entails.sepExists_right bs ?_
    have hpull :
        A.live ptr (cap.toNat * 112) 8 ∗
          (⌜bs.length = xs.length * 112⌝ ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) =
        ⌜bs.length = xs.length * 112⌝ ∗
          A.live ptr (cap.toNat * 112) 8 ∗ (ptr ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; intro hbs
    have hbs' : bs.length = cap.toNat * 112 := by rw [hbs, hfull]
    apply Entails.pure_right ⟨hbs', hptr⟩
    rw [hbs']
    exact Entails.of_eq (by ac_rfl)

theorem growOne_post_to_arrayAt_chainEpochPB (A : RustAlloc) (cap p' : BitVec 64)
    (xs : List ChainEpochPB) (bs : List (BitVec 8))
    (hfull : xs.length = cap.toNat) (hbs : bs.length = cap.toNat * 112)
    (hnew_toNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4) :
    A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 112) ∗
      (relocArrayAtChainEpochPB A xs).1 bs ⊢
    A.live p' ((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 p' xs ∗
      memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
        (((BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat - xs.length) * 112) := by
  rw [hnew_toNat]
  have hlen_xs : bs.length = xs.length * 112 := by rw [hbs, hfull]
  have hof := (relocArrayAtChainEpochPB A xs).2.of_bytes p' bs hlen_xs
  have hsub : max (2 * cap.toNat) 4 - cap.toNat = max (2 * cap.toNat) 4 - xs.length := by
    rw [hfull]
  rw [hlen_xs, hsub]
  have hgroup :
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) ∗
        (relocArrayAtChainEpochPB A xs).1 bs =
      A.live p' (max (2 * cap.toNat) 4 * 112) 8 ∗
        ((p' ↦ₛ bs) ∗ (relocArrayAtChainEpochPB A xs).1 bs) ∗
        memRegion (p' + BitVec.ofNat 64 (xs.length * 112))
          ((max (2 * cap.toNat) 4 - xs.length) * 112) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right (sepConj_mono_left hof)

/-! ## 112-Byte Q-Register Copy & `arrayAt` Snoc Helpers (`0x5371c..0x53770`) -/

theorem quads14At_sp_688_restore (sp : BitVec 64) (q : Quads14) :
    quads14At (sp - 688#64) q ∗ memRegion (sp - 576#64) 240 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗
      memRegion (sp - 680#64) 40 ∗
      memRegion (sp - 640#64) 304 := by
  unfold quads14At Quads14.head
  have h1 := quads7_entails_head_and_memRegion_48 (sp - 688#64) q.1
  have h2 := quads7At_entails_memRegion_56 (sp - 632#64) q.2
  have ha1 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  have ha2 : sp - 688#64 + 56#64 = sp - 632#64 := by bv_omega
  rw [ha1] at h1; rw [ha2]
  refine Entails.trans (sepConj_mono (sepConj_mono h1 h2) (Entails.refl _)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 8)
      (b' := sp - 640#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 640#64) (n := 8) (k := 296)
      (b' := sp - 632#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 632#64) (n := 56) (k := 240)
      (b' := sp - 576#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_rem_split_112 (ptr : BitVec 64) (len cap : Nat)
    (hlt : len < cap) (hcap63 : cap * 112 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (len * 112)) ((cap - len) * 112) ⊢
      (∃∗ q_dst : Quads14, quads14At (ptr + BitVec.ofNat 64 (len * 112)) q_dst) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len + 1) * 112)) ((cap - (len + 1)) * 112) := by
  have hsplit : (cap - len) * 112 = 112 + (cap - (len + 1)) * 112 := by
    have hsub : cap - len = 1 + (cap - (len + 1)) := by omega
    rw [hsub, Nat.add_mul, Nat.one_mul]
  have haddr : ptr + BitVec.ofNat 64 ((len + 1) * 112) =
      (ptr + BitVec.ofNat 64 (len * 112)) + 112#64 := by
    have hm : (len + 1) * 112 = len * 112 + 112 := by rw [Nat.add_mul, Nat.one_mul]
    rw [hm, BitVec.ofNat_add, BitVec.add_assoc]
  rw [ProofLib.memRegion_split' (b := ptr + BitVec.ofNat 64 (len * 112))
      (n := 112) (k := (cap - (len + 1)) * 112)
      (b' := ptr + BitVec.ofNat 64 ((len + 1) * 112)) hsplit haddr (by omega),
    memRegion_112_eq_quads14At (ptr + BitVec.ofNat 64 (len * 112))]
  exact Entails.refl _

theorem vecOf_chainEpochPB_snoc_fold (A : RustAlloc) (a cap ptr : BitVec 64)
    (xs : List ChainEpochPB) (ep' : ChainEpochPB) (q : Quads14)
    (hlt : xs.length < cap.toNat) (hcap63 : cap.toNat * 112 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
      quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
      chainEpochPBHeap A q ep' ∗
      memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
        ((cap.toNat - (xs.length + 1)) * 112) ⊢
    chainLinksVecAt A a (xs ++ [ep']) := by
  have hcap0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlen_app : (xs ++ [ep']).length = xs.length + 1 := by simp
  have hep_at := quads14_entails_chainEpochPBAt A (ptr + BitVec.ofNat 64 (xs.length * 112)) q ep'
  have harr := arrayAt_append_singleton (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ep'
  unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simp only [hlen_app, hcap0, ↓reduceIte]
  have hgroup :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1)) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
        quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
        chainEpochPBHeap A q ep' ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) =
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        A.live ptr (cap.toNat * 112) 8 ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr xs ∗
          (quads14At (ptr + BitVec.ofNat 64 (xs.length * 112)) q ∗
            chainEpochPBHeap A q ep')) ∗
        memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
          ((cap.toNat - (xs.length + 1)) * 112) := by ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right hep_at)))) ?_
  rw [harr]
  have hpure :
      ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
        ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) =
      ⌜xs.length + 1 ≤ cap.toNat ∧ cap.toNat * 112 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (xs.length + 1))) ∗
          A.live ptr (cap.toNat * 112) 8 ∗
          arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (xs ++ [ep']) ∗
          memRegion (ptr + BitVec.ofNat 64 ((xs.length + 1) * 112))
            ((cap.toNat - (xs.length + 1)) * 112)) := by ac_rfl
  rw [hpure]
  apply Entails.pure_right ⟨by omega, hcap63, hptr⟩
  exact Entails.of_eq (by ac_rfl)

theorem fold_protoPqRatchetStateCapOkAt_snoc (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (ep' : ChainEpochPB) (inner : Option PqRatchetState.Inner)
    (hlinks_next : (ch.links ++ [ep']).length + remLen ≤ 2 ^ 54) :
    optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
      vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
      ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (sp - 928#64) ch.params ∗
      ((sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner ⊢
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen
      ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq H_inner A sp remLen optVn
    { ch with links := ch.links ++ [ep'] } inner]
  dsimp only
  have hpure :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜(ch.links ++ [ep']).length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          chainLinksVecAt A (sp - 992#64) (ch.links ++ [ep']) ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by ac_rfl
  rw [hpure]
  apply Entails.pure_right hlinks_next
  exact Entails.of_eq (by ac_rfl)

/-! ## `decodeState_chain_push_copy_5371c` (`0x5371c..0x53770`, `+640..+724`) -/

/-- 112-byte Q-register copy from `[sp + 0x2c0 .. sp + 0x330)` (`s0.sp - 688#64`) into
    `ptr + ch.links.length * 112`, incrementing `len` at `[sp + 0x1a0]` (`s0.sp - 976#64`)
    and branching to `0x53698` (`+508`). -/
theorem decodeState_chain_push_copy_5371c {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (x : DecodeStateGhost)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (cap ptr : BitVec 64)
    (rest2 : List (BitVec 8)) (limit : Nat)
    (hlt : ch.links.length < cap.toNat)
    (hcap63 : cap.toNat * 112 < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 ch.links.length)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      optVersionNegotiationPBCapOkAt A (s0.sp - 1040#64) rest2.length optVn ∗
      ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
      ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      A.live ptr (cap.toNat * 112) 8 ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr ch.links ∗
      memRegion (ptr + BitVec.ofNat 64 (ch.links.length * 112)) ((cap.toNat - ch.links.length) * 112) ∗
      vecU8CapOkAt A (s0.sp - 968#64) rest2.length ch.nextRoot ∗
      ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
      ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
      ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (s0.sp - 912#64) rest2.length inner ∗
      chainEpochPBAt A (s0.sp - 688#64) ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
  decodeState_fetches b (Rust.withPanics ext) 640 88
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  apply SepWPpI.of_sepWP (mid := entry + 508#64)
  refine SepWP.fold (chainEpochPBAt_entails_quads14 A (s0.sp - 688#64) ep') (by sep_focus) ?_
  refine SepWP.fold (memRegion_rem_split_112 ptr ch.links.length cap.toNat hlt hcap63) (by sep_focus) ?_
  wp_pull_exists
  rename_i q_src q_dst
  rcases q_src with ⟨⟨s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6⟩, ⟨s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6⟩⟩
  rcases q_dst with ⟨⟨d0_0, d0_1, d0_2, d0_3, d0_4, d0_5, d0_6⟩, ⟨d1_0, d1_1, d1_2, d1_3, d1_4, d1_5, d1_6⟩⟩
  dsimp only [quads14At, quads7At]
  wp_steps 22
  have hfold_snoc := vecOf_chainEpochPB_snoc_fold A (s0.sp - 992#64) cap ptr ch.links ep'
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
    hlt hcap63 hptr
  have ha984 : s0.sp - 992#64 + 8#64 = s0.sp - 984#64 := by bv_omega
  have ha976 : s0.sp - 992#64 + 16#64 = s0.sp - 976#64 := by bv_omega
  rw [ha984, ha976] at hfold_snoc
  dsimp only [quads14At, quads7At] at hfold_snoc
  refine SepWP.fold hfold_snoc (by sep_focus) ?_
  have hrestore := quads14At_sp_688_restore s0.sp
    ((s0_0, s0_1, s0_2, s0_3, s0_4, s0_5, s0_6), (s1_0, s1_1, s1_2, s1_3, s1_4, s1_5, s1_6))
  dsimp only [quads14At, quads7At, Quads14.head] at hrestore
  refine SepWP.fold hrestore (by sep_focus) ?_
  refine SepWP.fold (fold_protoPqRatchetStateCapOkAt_snoc H_inner A s0.sp rest2.length
    optVn ch ep' inner hlinks_next) (by sep_focus) ?_
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  exact hloop s0_0 _ _
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
    (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
    (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
    (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hx28])
    (by simp only [arm64_norm, hx29])
    (by ac_rfl)

/-! ## `decodeState_chain_push_5370c` (`0x5370c..0x53770`, `0x5394c..0x53954`) -/

theorem SepWPpI.pure_elim {φ : Prop} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Q_err : State → SepProp → Prop}
    (h : φ → SepWPpI img prog ret s P Q Q_err) :
    SepWPpI img prog ret s (⌜φ⌝ ∗ P) Q Q_err := by
  intro hinv R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 hinv R hm.2 hL

theorem bv_len_beq_cap_false {len : Nat} {cap : BitVec 64}
    (hlt : len < cap.toNat) :
    (BitVec.ofNat 64 len == cap) = false ∧ (BitVec.ofNat 64 len != cap) = true := by
  have hlt64 : len < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  have hne : BitVec.ofNat 64 len ≠ cap := by
    intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at hto
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

theorem bv_len_beq_cap_true {len : Nat} {cap : BitVec 64}
    (heq : len = cap.toNat) :
    (BitVec.ofNat 64 len == cap) = true ∧ (BitVec.ofNat 64 len != cap) = false := by
  have hbv : BitVec.ofNat 64 len = cap := by
    rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨beq_iff_eq.mpr hbv, bne_eq_false_iff_eq.mpr hbv⟩

/-- `Vec<ChainEpochPB>::push` at `0x5370c` (`+624`), handling both `len < cap` (direct copy at
    `0x5371c`) and `len == cap` (`RawVecInner::grow_one` at `0x5394c..0x53954` followed by copy
    at `0x5371c`), branching to `0x53698` (`+508`). -/
theorem decodeState_chain_push_5370c {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext)
    (x : DecodeStateGhost)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (ep' : ChainEpochPB) (rest2 : List (BitVec 8)) (limit : Nat)
    (hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 624#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨optVn, some ch, inner⟩ ∗
      chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
      memRegion (s0.sp - 576#64) 240 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (w0' : BitVec 64) (sf : State) (P' : SepProp),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length
          ⟨optVn, some { ch with links := ch.links ++ [ep'] }, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hgrow_call := hc.growOneChainEpoch_at
  subst hP
  rw [protoPqRatchetStateCapOkAt_some_ch_eq H_inner A s0.sp rest2.length optVn ch inner]
  have hep_drop := chainEpochPBCapOkAt_entails_chainEpochPBAt A (s0.sp - 688#64) rest2.length ep'
  have ha984 : s0.sp - 992#64 + 8#64 = s0.sp - 984#64 := by bv_omega
  have ha976 : s0.sp - 992#64 + 16#64 = s0.sp - 976#64 := by bv_omega
  have hvec_unfold :
      chainLinksVecAt A (s0.sp - 992#64) ch.links =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
        ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr ch.links := by
    unfold chainLinksVecAt chainEpochPBSize vecOf vecAt vecHeader
    simp only [ha984, ha976, sepConj_assoc]
  rw [hvec_unfold]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPpI.exists_elim; intro cap
  apply SepWPpI.exists_elim; intro ptr
  have hreord :
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        (optVersionNegotiationPBCapOkAt A (s0.sp - 1040#64) rest2.length optVn ∗
          (⌜ch.links.length + rest2.length ≤ 2 ^ 54⌝ ∗
            (((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
              ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr ch.links) ∗
            vecU8CapOkAt A (s0.sp - 968#64) rest2.length ch.nextRoot ∗
            ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
            ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
            optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
            ((s0.sp - 916#64) ↦₃₂ ch.direction)) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (s0.sp - 912#64) rest2.length inner) ∗
        chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
        memRegion (s0.sp - 576#64) 240 ∗
        decodeStateLoopCommon b A x s0 =
      ⌜ch.links.length + rest2.length ≤ 2 ^ 54⌝ ∗
        (vecBuf A 112 8 (fun ep addr => chainEpochPBAt A addr ep) cap ptr ch.links ∗
          (chainEpochPBCapOkAt A (s0.sp - 688#64) rest2.length ep' ∗
            (sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
              optVersionNegotiationPBCapOkAt A (s0.sp - 1040#64) rest2.length optVn ∗
              ((s0.sp - 992#64) ↦₆₄ cap) ∗ ((s0.sp - 984#64) ↦₆₄ ptr) ∗
              ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              vecU8CapOkAt A (s0.sp - 968#64) rest2.length ch.nextRoot ∗
              ((s0.sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
              ((s0.sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
              optChainParamsPBAt (s0.sp - 928#64) ch.params ∗
              ((s0.sp - 916#64) ↦₃₂ ch.direction) ∗
              optProtoPqRatchetInnerCapOkAt H_inner A (s0.sp - 912#64) rest2.length inner ∗
              memRegion (s0.sp - 576#64) 240 ∗
              decodeStateLoopCommon b A x s0))) := by ac_rfl
  rw [hreord]
  apply SepWPpI.pure_elim; intro _hlinks_cur
  have hexp := vecBuf_chainEpochPB_expose_bounds A cap ptr ch.links
  refine SepWPpI.mono_pre (sepConj_mono hexp (sepConj_mono_left hep_drop)) ?_
  rw [sepConj_assoc]
  apply SepWPpI.pure_elim; rintro ⟨hlen_le, hcap63, hptr⟩
  by_cases hlt : ch.links.length < cap.toNat
  · -- len < cap: direct copy at 0x5371c (+640)
    have ⟨hbeq, hbne⟩ := bv_len_beq_cap_false hlt
    refine SepWPpI.mono_pre
      (sepConj_mono_left (vecBuf_chainEpochPB_of_lt A cap ptr ch.links hlt)) ?_
    dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 624 16
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 640#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    exact decodeState_chain_push_copy_5371c x optVn ch inner ep' cap ptr rest2 limit
      hlt hcap63 hptr hlinks_next s0 _ _ R post hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, hbeq, hbne])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hx28])
      (by simp only [arm64_norm, hx29])
      (by ac_rfl)
      (fun w0' sf P' hpc' => hloop w0' sf P' (by rw [← hentry]; exact hpc'))
  · -- len == cap: grow_one at 0x5394c (+1200) -> 0x5371c (+640)
    have heq_len : ch.links.length = cap.toNat := by omega
    have hbv : BitVec.ofNat 64 ch.links.length = cap := by
      rw [heq_len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hbeq : (cap - cap == 0#64) = true := by simp
    have hbne : (!decide ((cap - cap == 0#64) = true)) = false := by simp
    have hcap_54 : cap.toNat ≤ 2 ^ 54 := by
      have : (ch.links ++ [ep']).length = ch.links.length + 1 := by simp
      omega
    have ⟨hgrow_bound, hnew_cap63_nat, hnew_lt_nat, hnew_lt64⟩ := max_double_four_bound hcap_54
    have hnew_toNat : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = max (2 * cap.toNat) 4 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
    have hnew_lt : ch.links.length < (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat := by omega
    have hnew_cap63 : (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat * 112 < 2 ^ 63 := by omega
    refine SepWPpI.mono_pre
      (sepConj_mono_left (vecBuf_chainEpochPB_to_growOne_pre A cap ptr ch.links heq_len)) ?_
    rw [sepExists_sepConj_left]
    apply SepWPpI.exists_elim; intro bs
    rw [sepConj_assoc]
    apply SepWPpI.pure_elim; rintro ⟨hbs_len, _⟩
    rw [hbv]
    dsimp only [tripleRatchetProgAtExt, decodeStateName, decodeStateLoopCommon] at hpc hgrow_call ⊢
    have hentry : decodeStateEntry b ext =
        (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
    decodeState_fetches b (Rust.withPanics ext) 624 16
    decodeState_fetches b (Rust.withPanics ext) 1200 12
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "spqr::decode_state" = entry
    examples_hide_fetches
    apply SepWPpI.of_sepWP (mid := entry + 1200#64)
    wp_steps 4
    apply SepWP.done (by simp only [arm64_norm, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    apply SepWPpI.of_sepWP (mid := entry + (370400#64 - 319652#64))
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    have hx22_30 : s0.sp - 1040#64 + 48#64 = s0.sp - 992#64 := by bv_omega
    refine SepWPpI.call_growOneChainEpoch hgrow_call
      (s0.sp - 992#64) cap ptr bs
      (ret_pc := entry + 1208#64)
      (hpc := by simp only [arm64_norm])
      (hrun := by simp only [arm64_norm, hrun])
      (hsp := by simp only [arm64_norm, hsp]) (hs0A := hs0A)
      (hlr := by simp only [arm64_norm]) (htr := by simp only [arm64_norm, htr])
      (hx0 := by simp only [arm64_norm, hx22, hx22_30])
      (hlen := hbs_len) (hptr := hptr) (hbound := hgrow_bound)
      (hP := by rw [ha984]; sep_focus) ?_
    intro s1 p' hptr' _ hpc1 hrun1 hsp1 htr1 hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [arm64_norm, wp_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    rw [← hbv] at hx27_1
    have hsp1A : s1.spAligned = true := by rw [State.spAligned, hsp1]; exact sp_sub_1392_aligned s0 hs0A
    have hpost_grow := growOne_post_to_arrayAt_chainEpochPB A cap p' ch.links bs heq_len hbs_len hnew_toNat
    have hrestore_len : ((s0.sp - 976#64) ↦₆₄ cap) ⊢ ((s0.sp - 976#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) :=
      Entails.of_eq (by rw [hbv])
    rw [ha984]
    apply SepWPpI.of_sepWP (mid := entry + 640#64)
    refine SepWP.fold hpost_grow (by sep_focus) ?_
    refine SepWP.fold hrestore_len (by sep_focus) ?_
    wp_steps 1
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
    exact decodeState_chain_push_copy_5371c x optVn ch inner ep'
      (BitVec.ofNat 64 (max (2 * cap.toNat) 4)) p' rest2 limit
      hnew_lt hnew_cap63 hptr' hlinks_next s0 _ _ R post hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm])
      (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1])
      (by simp only [arm64_norm, htr1])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by dsimp only [decodeStateLoopCommon]; ac_rfl)
      (fun w0' sf P' hpc' => hloop w0' sf P' (by rw [← hentry]; exact hpc'))

/-! ## Tag 3 (`ChainPB::epoch` `Vec<ChainEpochPB>::push`, `0x536ec..0x53770`, `+592..+724`) -/

theorem protoPqRatchetStateCapOkAt_expose_ch_links (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (ch : ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ ⊢
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
      protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, some ch, inner⟩ := by
  rw [protoPqRatchetStateCapOkAt_some_ch_eq]
  have h1 :
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
        (⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
          chainLinksVecAt A (sp - 992#64) ch.links ∗
          vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
          ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
          ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
          optChainParamsPBAt (sp - 928#64) ch.params ∗
          ((sp - 916#64) ↦₃₂ ch.direction)) ∗
        optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner =
      ⌜ch.links.length + remLen ≤ 2 ^ 54⌝ ∗
        (optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
          (chainLinksVecAt A (sp - 992#64) ch.links ∗
            vecU8CapOkAt A (sp - 968#64) remLen ch.nextRoot ∗
            ((sp - 944#64) ↦₆₄ ch.currentEpoch) ∗
            ((sp - 936#64) ↦₆₄ ch.sendEpoch) ∗
            optChainParamsPBAt (sp - 928#64) ch.params ∗
            ((sp - 916#64) ↦₃₂ ch.direction)) ∗
          optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; intro h
  apply Entails.pure_right h
  apply Entails.pure_right h
  exact Entails.of_eq (by ac_rfl)

theorem wt_ne_two_of_ne_lengthDelimited {iwt : WireType} (hwt : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> first | exact (hwt rfl).elim | decide

attribute [local irreducible] Proto.mergeMessage mergeLoopBin Proto.spqrDecodeState

/-- `ChainPB` tag 3 (`epoch`, `0x536ec..0x53770`, `+592..+724`): checks `x0 == 2`
    (`.lengthDelimited`), merges a `ChainEpochPB` (`decodeState_epoch_merge_536f4`),
    and pushes it onto `ch.links` (`decodeState_chain_push_5370c`), continuing to
    `0x53698` (`+508`). -/
theorem decodeState_chain_tag3_536ec {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hc : DecodeStateCalleeContractsX4K H_inner img b A ext)
    (x : DecodeStateGhost) (w0 : BitVec 64)
    (optVn : Option VersionNegotiationPB) (ch : ChainPB) (inner : Option PqRatchetState.Inner)
    (iwt : WireType) (rest1 : List (BitVec 8)) (limit : Nat)
    (hrest1_le : rest1.length ≤ x.st.bytes.length)
    (hrest1_suf : IsDropSuffix x.st.bytes rest1)
    (hlen_bound : x.st.bytes.length < 2 ^ 32)
    (herr_of_none :
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption = none →
      spqrDecodeState x.st.bytes = .error .stateDecode)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = decodeStatePost H_inner b A x s0 R)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 592#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 .x19 = x.outPtr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 limit)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = ((s0.sp - 688#64) ↦₆₄ w0) ∗
      sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
      memRegion (s0.sp - 680#64) 40 ∗
      memRegion (s0.sp - 640#64) 304 ∗
      decodeStateLoopCommon b A x s0)
    (hloop : ∀ (w0' : BitVec 64) (ch' : ChainPB) (rest2 : List (BitVec 8)) (sf : State) (P' : SepProp),
      (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption = some (ch', rest2) →
      rest2.length ≤ rest1.length →
      IsDropSuffix rest1 rest2 →
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr decodeStateName + 508#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = x.outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 limit →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = 8#64 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = ((s0.sp - 688#64) ↦₆₄ w0') ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest2 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest2.length ⟨optVn, some ch', inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 →
      SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf P' post
        (decodeStatePanicPost H_inner b A x s0 R)) :
    SepWPpI img (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post
      (decodeStatePanicPost H_inner b A x s0 R) := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  have hreord_tag3 :
      ((s0.sp - 688#64) ↦₆₄ w0) ∗
        sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
        protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
        memRegion (s0.sp - 680#64) 40 ∗
        memRegion (s0.sp - 640#64) 304 ∗
        decodeStateLoopCommon b A x s0 =
      protoPqRatchetStateCapOkAt H_inner A (s0.sp - 1040#64) rest1.length ⟨optVn, some ch, inner⟩ ∗
        (((s0.sp - 688#64) ↦₆₄ w0) ∗
          sliceCursorAfter (s0.sp - 1056#64) x.st.ptr x.st.bytes rest1 ∗
          memRegion (s0.sp - 680#64) 40 ∗
          memRegion (s0.sp - 640#64) 304 ∗
          decodeStateLoopCommon b A x s0) := by ac_rfl
  rw [hreord_tag3]
  refine SepWPpI.mono_pre
    (sepConj_mono_left
      (protoPqRatchetStateCapOkAt_expose_ch_links H_inner A s0.sp rest1.length optVn ch inner)) ?_
  rw [sepConj_assoc]
  apply SepWPpI.pure_elim; intro hlinks1
  dsimp only [tripleRatchetProgAtExt, decodeStateName] at hpc ⊢
  have hentry : decodeStateEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::decode_state" := rfl
  decodeState_fetches b (Rust.withPanics ext) 592 8
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::decode_state" = entry
  examples_hide_fetches
  by_cases hwt : iwt = .lengthDelimited
  · -- iwt == .lengthDelimited (x0 == 2) -> 0x536f4 (+600)
    have hx0_2 : s.readReg64 .x0 = 2#64 := by rw [hx0, hwt]; rfl
    apply SepWPpI.of_sepWP (mid := entry + 600#64)
    wp_steps 2
    apply SepWP.done (by simp only [arm64_norm, hx0_2]) (by simp only [arm64_norm, hrun])
    refine decodeState_epoch_merge_536f4 (v20 := BitVec.ofNat 64 limit) hc x w0
      ⟨optVn, some ch, inner⟩ rest1 hrest1_le hrest1_suf hlen_bound
      (fun hnone => herr_of_none (by rw [chainPB_mergeField_tag3, hwt, codecWireTypeToProto, hnone]; rfl))
      s0 _ _ R post hpost hs0A
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, hx0_2])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      (by simp only [arm64_norm, hx25]) (by simp only [arm64_norm, hx26])
      (by simp only [arm64_norm, hx28]) (by simp only [arm64_norm, hx29])
      (by ac_rfl) ?_
    intro ep' rest2 sf1 P1 hok_mm hle2 hsuf2 hpc1 hrun1 hsp1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hP1
    have hlt2 : rest2.length < rest1.length := proto_mergeMessage_length_lt hok_mm
    have hlinks_next : (ch.links ++ [ep']).length + rest2.length ≤ 2 ^ 54 := by
      have : (ch.links ++ [ep']).length = ch.links.length + 1 := by simp
      omega
    have hok_tag3 :
        (ChainPB.mergeField ch 3#32 (codecWireTypeToProto iwt) rest1 99).toOption =
          some ({ ch with links := ch.links ++ [ep'] }, rest2) := by
      rw [chainPB_mergeField_tag3, hwt, codecWireTypeToProto, hok_mm]; rfl
    exact decodeState_chain_push_5370c hc x optVn ch inner ep' rest2 limit
      hlinks_next s0 sf1 P1 R post hs0A
      hpc1 hrun1 hsp1 htr1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 hP1
      (fun w0' sf2 P2 hpc2 =>
        hloop w0' { ch with links := ch.links ++ [ep'] } rest2 sf2 P2 hok_tag3 hle2 hsuf2
          (by rw [← hentry]; exact hpc2))
  · -- iwt != .lengthDelimited -> 0x53f30 (+2708)
    have ⟨hbeq, hbne⟩ := wt_ne_two_of_ne_lengthDelimited hwt
    have herr : spqrDecodeState x.st.bytes = .error .stateDecode := by
      apply herr_of_none
      rw [chainPB_mergeField_tag3, mergeMessage_toOption_of_ne_lengthDelimited ChainEpochPB.mergeField hwt]
      rfl
    apply SepWPpI.of_sepWP (mid := entry + 2708#64)
    wp_steps 2
    refine SepWP.fold (loopCommon_cursor_to_errFrame H_inner b A x rest1 rest1.length
      ⟨optVn, some ch, inner⟩ s0) (by sep_focus) ?_
    apply SepWP.done (by simp only [arm64_norm, hx0, hbeq, hbne]) (by simp only [arm64_norm, hrun])
    exact SepWPpI.of_sepWPp (decodeState_err_chain_epoch_wt_53f30 hc.toDecodeStateCalleeContracts4K
      x ⟨optVn, some ch, inner⟩ w0 s0 _ _ R post hpost herr
      (by rw [decodeStateEntry_eq, hentry]; simp only [arm64_norm, hx0, hbeq, hbne])
      (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) hs0A
      (by simp only [arm64_norm, htr]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx29])
      (by ac_rfl))

end CryptoVerification.SpqrV1.Top.DecodeState
