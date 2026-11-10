/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prog
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym -- shake: keep

/-!
# `<spqr::encoding::polynomial::PolyEncoder>::from_pb`: Definitions and Specifications

**Checked by Lean.**

Total pure model (`fromPbResult`) and AArch64 separation-logic specifications (`encoderFromPbSpec`,
`encoderFromPbSpecX`) for `<PolyEncoder>::from_pb` (`0x62188`, Block `374`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L22
open Lean Meta Elab Tactic ProofLib in
elab "ls_code_fetches_range " prog:ident binPfx:ident base:term:max hooks:term:max sym:str k0:num len:num : tactic => do
  let progName ← realizeGlobalConstNoOverloadWithInfo prog
  let fnEntry ← CodeLookup.lookup progName .fnOff sym.getString
  evalTactic (← `(tactic| code_fetches_range $prog $binPfx $base $hooks $(mkCIdentFrom sym fnEntry.decl) $(Syntax.mkNumLit (toString fnEntry.val)) $k0 $len))
end CryptoVerification.SpqrV1.Layout.L22

namespace CryptoVerification.SpqrV1.Poly.EncoderFromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
export CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym spqrMemcpySym spqrMemmoveSym)
abbrev spqrRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L1
open CryptoVerification.SpqrV1.Layout.L22

/-! ## Symbol Names, Instruction Decodes, and Stack Budgets -/

abbrev encoderFromPbName : String :=
  "<spqr::encoding::polynomial::PolyEncoder>::from_pb"

abbrev dropGluePoly16Name : String :=
  "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>"

abbrev dropGlueProtoPolyEncoderName : String :=
  "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>"

gen_fn_decodes libsignalSessionCode_tree libsignalSessionBin
  ["<spqr::encoding::polynomial::PolyEncoder>::from_pb"]

ls_attribute [ simp, arm64_norm ↓, wp_norm ↓]
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder>::from_pb")
  (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>")
  (ls_lemma% fnOff "<alloc::raw_vec::RawVec<spqr::encoding::gf::GF16>>::grow_one")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_bounds_check")

macro "encoder_from_pb_fetches_range " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic|
    ls_code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b $H
      "<spqr::encoding::polynomial::PolyEncoder>::from_pb" $k0 $len)

/-- Own stack frame of `<PolyEncoder>::from_pb` (`0x60 + 0x3a0 = 0x400 = 1024` bytes). -/
abbrev encoderFromPbFrame : Nat := 1024

/-- Stack budget of `<PolyEncoder>::from_pb` (`1024` B own frame + `dropGluePoly16Stack` = `1056 + allocHookStack`). -/
abbrev encoderFromPbStack : Nat := encoderFromPbFrame + dropGluePoly16Stack

/-- Extended-stack budget of `<PolyEncoder>::from_pb` (`1024 + extHookStack`). -/
abbrev encoderFromPbStackX : Nat := encoderFromPbFrame + extHookStack

/-! ## Total Pure Model of `PolyEncoder.fromPb` -/

/-- Total version of `Poly.bytesToGF16List` on even-length byte lists. -/
def bytesToGF16ListTotal : List (BitVec 8) → List GF16
  | [] => []
  | [ _ ] => []
  | b0 :: b1 :: rest => GF16.new (u16FromBeBytes b0 b1) :: bytesToGF16ListTotal rest

theorem bytesToGF16List_eq_ok (bs : List (BitVec 8)) (heven : bs.length % 2 = 0) :
    LibsignalSpqrV1.Poly.bytesToGF16List bs = .ok (bytesToGF16ListTotal bs) ∧
    (bytesToGF16ListTotal bs).length = bs.length / 2 := by
  induction bs using bytesToGF16ListTotal.induct with
  | case1 => simp [LibsignalSpqrV1.Poly.bytesToGF16List, bytesToGF16ListTotal]
  | case2 b0 => simp at heven
  | case3 b0 b1 rest ih =>
    have heven' : rest.length % 2 = 0 := by
      simp only [List.length_cons] at heven
      omega
    obtain ⟨h1, h2⟩ := ih heven'
    refine ⟨?_, ?_⟩
    · simp [LibsignalSpqrV1.Poly.bytesToGF16List, bytesToGF16ListTotal, h1, bind, Except.bind, pure, Except.pure]
    · simp only [bytesToGF16ListTotal, List.length_cons, h2]
      omega

/-- Total version of `Poly.deserialize`. -/
def polyDeserializeTotal (serialized : List (BitVec 8)) : Except PolynomialError LibsignalSpqrV1.Poly :=
  if serialized.isEmpty || serialized.length % 2 == 1 then
    .error .serializationInvalid
  else
    .ok { coefficients := bytesToGF16ListTotal serialized }

theorem polyDeserialize_eq_ok (serialized : List (BitVec 8)) :
    LibsignalSpqrV1.Poly.deserialize serialized = .ok (polyDeserializeTotal serialized) := by
  unfold LibsignalSpqrV1.Poly.deserialize polyDeserializeTotal
  by_cases hbad : (serialized.isEmpty || serialized.length % 2 == 1) = true
  · simp [hbad, pure, Except.pure]
  · have heven : serialized.length % 2 = 0 := by
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hbad
      omega
    have hok := (bytesToGF16List_eq_ok serialized heven).1
    simp [hbad, hok, bind, Except.bind, pure, Except.pure]

/-- Total version of `PolyEncoder.decodePbPoints`. -/
def decodePbPointsTotal : List (List (BitVec 8)) → Except PolynomialError (List Point)
  | [] => .ok []
  | pts :: rest =>
    if pts.length % 2 != 0 then
      .error .serializationInvalid
    else
      match decodePbPointsTotal rest with
      | .error e => .error e
      | .ok tail => .ok ({ value := bytesToGF16ListTotal pts } :: tail)

theorem decodePbPoints_eq_ok (bss : List (List (BitVec 8))) :
    PolyEncoder.decodePbPoints bss = .ok (decodePbPointsTotal bss) := by
  induction bss with
  | nil => rfl
  | cons pts rest ih =>
    unfold PolyEncoder.decodePbPoints decodePbPointsTotal
    by_cases hodd : (pts.length % 2 != 0) = true
    · simp [hodd, pure, Except.pure]
    · have heven : pts.length % 2 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd
        exact hodd
      have hok := (bytesToGF16List_eq_ok pts heven).1
      simp only [hodd, Bool.false_eq_true, ↓reduceIte, hok, ih, bind, Except.bind, pure, Except.pure]
      cases decodePbPointsTotal rest <;> rfl

/-- Total version of `PolyEncoder.decodePbPolys`. -/
def decodePbPolysTotal : List (List (BitVec 8)) → Except PolynomialError (List LibsignalSpqrV1.Poly)
  | [] => .ok []
  | polyBytes :: rest =>
    match polyDeserializeTotal polyBytes with
    | .error e => .error e
    | .ok p =>
      match decodePbPolysTotal rest with
      | .error e => .error e
      | .ok tail => .ok (p :: tail)

theorem decodePbPolys_eq_ok (bss : List (List (BitVec 8))) :
    PolyEncoder.decodePbPolys bss = .ok (decodePbPolysTotal bss) := by
  induction bss with
  | nil => rfl
  | cons polyBytes rest ih =>
    unfold PolyEncoder.decodePbPolys decodePbPolysTotal
    rw [polyDeserialize_eq_ok polyBytes]
    simp only [bind, Except.bind, pure, Except.pure]
    cases polyDeserializeTotal polyBytes with
    | error e => rfl
    | ok p =>
      rw [ih]
      cases decodePbPolysTotal rest <;> rfl

/-- Total result of `PolyEncoder.fromPb pb` (`PolyEncoder.fromPb pb = .ok (fromPbResult pb)`). -/
def fromPbResult (pb : ProtoPolynomialEncoder) : Except PolynomialError PolyEncoder :=
  if !pb.pts.isEmpty then
    if !pb.polys.isEmpty then
      .error .serializationInvalid
    else if pb.pts.length != NUM_POLYS then
      .error .serializationInvalid
    else
      match decodePbPointsTotal pb.pts with
      | .error e => .error e
      | .ok out => .ok { idx := pb.idx, s := .points out }
  else if pb.polys.length == NUM_POLYS then
    match decodePbPolysTotal pb.polys with
    | .error e => .error e
    | .ok out => .ok { idx := pb.idx, s := .polys out }
  else
    .error .serializationInvalid

theorem fromPb_eq_ok (pb : ProtoPolynomialEncoder) :
    PolyEncoder.fromPb pb = .ok (fromPbResult pb) := by
  unfold PolyEncoder.fromPb fromPbResult
  by_cases hpts : (!pb.pts.isEmpty) = true
  · simp only [hpts, ↓reduceIte]
    by_cases hpolys : (!pb.polys.isEmpty) = true
    · simp [hpolys, pure, Except.pure]
    · simp only [hpolys, Bool.false_eq_true, ↓reduceIte]
      by_cases hlen : (pb.pts.length != NUM_POLYS) = true
      · simp [hlen, pure, Except.pure]
      · simp only [hlen, Bool.false_eq_true, ↓reduceIte, decodePbPoints_eq_ok pb.pts, bind, Except.bind, pure, Except.pure]
        cases decodePbPointsTotal pb.pts <;> rfl
  · simp only [hpts, Bool.false_eq_true, ↓reduceIte]
    by_cases hlen : (pb.polys.length == NUM_POLYS) = true
    · simp only [hlen, ↓reduceIte, decodePbPolys_eq_ok pb.polys, bind, Except.bind, pure, Except.pure]
      cases decodePbPolysTotal pb.polys <;> rfl
    · simp [hlen, pure, Except.pure]

theorem pointsTo16_pair_eq (a : BitVec 64) (b0 b1 : BitVec 8) :
    (a ↦₁₆ (b1 ++ b0)) = (a ↦ₛ [b0, b1]) := by
  rw [pointsTo16_eq_pointsToBytes]
  congr 1
  simp only [unpack16, List.cons.injEq, and_true]
  exact ⟨by bv_slice, by bv_slice⟩

theorem pointsToBytes_pair_cons (a : BitVec 64) (b0 b1 : BitVec 8) (rest : List (BitVec 8)) :
    (a ↦ₛ (b0 :: b1 :: rest)) =
      (a ↦₁₆ (b1 ++ b0)) ∗ ((a + 2#64) ↦ₛ rest) := by
  have hsplit : (b0 :: b1 :: rest) = [b0, b1] ++ rest := rfl
  rw [hsplit, ProofLib.pointsToBytes_append a [b0, b1] rest, ← pointsTo16_pair_eq]
  rfl

theorem rev16_pair_eq_u16FromBeBytes (b0 b1 : BitVec 8) :
    ((rev16_64 ((b1 ++ b0).zeroExtend 64)).setWidth 32).setWidth 16 =
      (GF16.new (u16FromBeBytes b0 b1)).value := by
  simp only [GF16.new, u16FromBeBytes, rev16_64]
  bv_slice

theorem pointsTo64_pair_eq_pointsTo128 (a : BitVec 64) (w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦₁₂₈ (w1 ++ w0)) := by
  unfold pointsTo128
  have h0 : (w1 ++ w0).extractLsb' 0 64 = w0 := by bv_kernel
  have h1 : (w1 ++ w0).extractLsb' 64 64 = w1 := by bv_kernel
  rw [h0, h1]

/-- Low byte (`bits 0..7`) of `u : BitVec 64`. -/
def loByte (u : BitVec 64) : BitVec 8 :=
  u.extractLsb' 0 8

/-- High byte (`bits 56..63`) of `u : BitVec 64`. -/
def hiByte (u : BitVec 64) : BitVec 8 :=
  u.extractLsb' 56 8

/-- Pack the high 7 bytes of `u : BitVec 64` followed by `b : BitVec 8` into a 64-bit word. -/
def unshiftWord (u : BitVec 64) (b : BitVec 8) : BitVec 64 :=
  (u >>> 8) ||| (b.zeroExtend 64 <<< 56)

/-- Low 7 bytes of `u : BitVec 64`. -/
def loBytes7 (u : BitVec 64) : List (BitVec 8) :=
  (unpack64 u).take 7

/-- High 7 bytes of `u : BitVec 64`. -/
def hiBytes7 (u : BitVec 64) : List (BitVec 8) :=
  (unpack64 u).drop 1

@[simp] theorem length_loBytes7 (u : BitVec 64) : (loBytes7 u).length = 7 := rfl
@[simp] theorem length_hiBytes7 (u : BitVec 64) : (hiBytes7 u).length = 7 := rfl

theorem unpack64_eq_loByte_cons_hiBytes7 (u : BitVec 64) :
    unpack64 u = loByte u :: hiBytes7 u := rfl

theorem loByte_cons_unpack64_unshiftWord (u : BitVec 64) (b : BitVec 8) :
    loByte u :: unpack64 (unshiftWord u b) = unpack64 u ++ [b] := by
  simp only [unpack64, loByte, unshiftWord, List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨trivial, by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
    by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel, trivial⟩

theorem loBytes7_unshiftWord_append_unpack64 (ptr len : BitVec 64) :
    loBytes7 (unshiftWord ptr (loByte len)) ++ unpack64 len =
      unpack64 (unshiftWord ptr (loByte len)) ++ hiBytes7 len := by
  simp only [loBytes7, hiBytes7, unpack64, unshiftWord, loByte, List.take, List.drop,
    List.cons_append, List.nil_append, List.cons.injEq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, by bv_kernel, trivial⟩

theorem pair64_to_byte_word_tail7 (q ptr len : BitVec 64) :
    ((q ↦₆₄ ptr) ∗ ((q + 8#64) ↦₆₄ len)) =
      ((q ↦₈ loByte ptr) ∗ ((q + 1#64) ↦₆₄ unshiftWord ptr (loByte len)) ∗
        ((q + 9#64) ↦ₛ hiBytes7 len)) := by
  have hleft :
      ((q ↦₆₄ ptr) ∗ ((q + 8#64) ↦₈ loByte len)) =
        ((q ↦₈ loByte ptr) ∗ ((q + 1#64) ↦₆₄ unshiftWord ptr (loByte len))) := by
    rw [pointsTo64_eq_pointsToBytes q ptr, pointsTo64_eq_pointsToBytes (q + 1#64),
        ← ProofLib.pointsToBytes_cons, loByte_cons_unpack64_unshiftWord ptr (loByte len),
        ProofLib.pointsToBytes_append q (unpack64 ptr) [loByte len], unpack64_length]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [pointsTo64_eq_pointsToBytes (q + 8#64) len,
      unpack64_eq_loByte_cons_hiBytes7 len,
      ← List.singleton_append (x := loByte len),
      ProofLib.pointsToBytes_append (q + 8#64) [loByte len] (hiBytes7 len)]
  have h1 : (q + 8#64) + BitVec.ofNat 64 ([loByte len].length) = q + 9#64 := by
    simp only [List.length_singleton]; bv_omega
  rw [h1, ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp,
      ← sepConj_assoc, hleft, sepConj_assoc]

theorem byte_unshift_tail7_to_pair64 (q ptr len : BitVec 64) (bs7 : List (BitVec 8))
    (hbs7 : bs7.length = 7) :
    ((q ↦₈ loByte ptr) ∗ ((q + 1#64) ↦₆₄ unshiftWord ptr (loByte len)) ∗
      ((q + 9#64) ↦ₛ bs7)) ⊢
      (q ↦₆₄ ptr) ∗ (∃∗ v : BitVec 64, (q + 8#64) ↦₆₄ v) := by
  have hleft :
      ((q ↦₈ loByte ptr) ∗ ((q + 1#64) ↦₆₄ unshiftWord ptr (loByte len))) =
        ((q ↦₆₄ ptr) ∗ ((q + 8#64) ↦₈ loByte len)) := by
    rw [pointsTo64_eq_pointsToBytes (q + 1#64), ← ProofLib.pointsToBytes_cons,
        loByte_cons_unpack64_unshiftWord ptr (loByte len),
        ProofLib.pointsToBytes_append q (unpack64 ptr) [loByte len],
        unpack64_length, ← pointsTo64_eq_pointsToBytes q ptr]
    simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]
  rw [← sepConj_assoc, hleft, sepConj_assoc]
  refine sepConj_mono_right ?_
  have hjoin : ((q + 8#64) ↦₈ loByte len) ∗ ((q + 9#64) ↦ₛ bs7) ⊢ memRegion (q + 8#64) 8 := by
    rw [ProofLib.memRegion_split' (b := q + 8#64) (n := 1) (k := 7) (b' := q + 9#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo8_entails_memRegion _ _)
      (hbs7 ▸ pointsToBytes_entails_memRegion (q + 9#64) bs7)
  rw [← ProofLib.memRegion_eight (q + 8#64)]
  exact hjoin

theorem memRegion_15_to_left64 (p : BitVec 64) :
    memRegion p 15 ⊢ (∃∗ v : BitVec 64, p ↦₆₄ v) ∗ memRegion (p + 8#64) 7 := by
  rw [ProofLib.memRegion_split p 8 7 (by decide), ProofLib.memRegion_eight p]
  exact Entails.refl _

theorem unshift_left64_to_right64 (p ptr len : BitVec 64) :
    (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ memRegion (p + 8#64) 7 ⊢
      (p ↦ₛ loBytes7 (unshiftWord ptr (loByte len))) ∗ (∃∗ v : BitVec 64, (p + 7#64) ↦₆₄ v) := by
  have hsplit : unpack64 (unshiftWord ptr (loByte len)) =
      loBytes7 (unshiftWord ptr (loByte len)) ++ [hiByte (unshiftWord ptr (loByte len))] := by
    simp only [loBytes7, hiByte, unpack64]
    rfl
  rw [pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len)), hsplit,
      ProofLib.pointsToBytes_append p (loBytes7 (unshiftWord ptr (loByte len)))
        [hiByte (unshiftWord ptr (loByte len))],
      length_loBytes7]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil,
    sepConj_emp, sepConj_assoc]
  refine sepConj_mono_right ?_
  rw [← ProofLib.memRegion_eight (p + 7#64),
      ProofLib.memRegion_split' (b := p + 7#64) (n := 1) (k := 7) (b' := p + 8#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem right64_to_unshift_left64 (p ptr len : BitVec 64) :
    (p ↦ₛ loBytes7 (unshiftWord ptr (loByte len))) ∗ ((p + 7#64) ↦₆₄ len) ⊢
      (p ↦₆₄ unshiftWord ptr (loByte len)) ∗ memRegion (p + 8#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes (p + 7#64) len]
  have h7 : p + BitVec.ofNat 64 (loBytes7 (unshiftWord ptr (loByte len))).length = p + 7#64 := by
    rw [length_loBytes7]
  rw [← h7, ← ProofLib.pointsToBytes_append p (loBytes7 (unshiftWord ptr (loByte len))) (unpack64 len),
      loBytes7_unshiftWord_append_unpack64 ptr len,
      ProofLib.pointsToBytes_append p (unpack64 (unshiftWord ptr (loByte len))) (hiBytes7 len),
      unpack64_length, ← pointsTo64_eq_pointsToBytes p (unshiftWord ptr (loByte len))]
  exact sepConj_mono_right (length_hiBytes7 len ▸ pointsToBytes_entails_memRegion (p + 8#64) (hiBytes7 len))

theorem left64_to_memRegion_15 (p w : BitVec 64) :
    (p ↦₆₄ w) ∗ memRegion (p + 8#64) 7 ⊢ memRegion p 15 := by
  rw [ProofLib.memRegion_split p 8 7 (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion p w)

/-- 24-byte serialized `Vec` header `(cap, ptr, len)`. -/
def vecHeaderBytesOf (pin : VecPin) (len : Nat) : List (BitVec 8) :=
  unpack64 pin.cap ++ unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)

@[simp] theorem length_vecHeaderBytesOf (pin : VecPin) (len : Nat) :
    (vecHeaderBytesOf pin len).length = 24 := rfl

/-- Concatenated 24-byte `Vec` headers for `pins` and `vecs`. -/
def vecHeadersBytesOf : List VecPin → List (List GF16) → List (BitVec 8)
  | [], _ => []
  | _, [] => []
  | pin :: pins, cs :: vecs => vecHeaderBytesOf pin cs.length ++ vecHeadersBytesOf pins vecs

theorem length_vecHeadersBytesOf :
    ∀ (pins : List VecPin) (vecs : List (List GF16)),
      pins.length = vecs.length →
      (vecHeadersBytesOf pins vecs).length = vecs.length * 24
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | pin :: pins, cs :: vecs, h => by
    simp only [List.length_cons] at h
    have ih := length_vecHeadersBytesOf pins vecs (Nat.succ.inj h)
    simp only [vecHeadersBytesOf, List.length_append, length_vecHeaderBytesOf, ih, List.length_cons]
    omega

/-- Separating conjunction of `vecBuf A gf16Stride gf16Align gf16At` across `pins` and `vecs`. -/
def vecGF16HeapList (A : RustAlloc) : List VecPin → List (List GF16) → SepProp
  | [], _ => emp
  | _, [] => emp
  | pin :: pins, cs :: vecs =>
    vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs

theorem vecHeader_eq_pointsToBytes (a : BitVec 64) (pin : VecPin) (len : Nat) :
    vecHeader a pin.cap pin.ptr (BitVec.ofNat 64 len) =
      (a ↦ₛ vecHeaderBytesOf pin len) := by
  unfold vecHeader vecHeaderBytesOf
  rw [List.append_assoc,
      ProofLib.pointsToBytes_append a (unpack64 pin.cap)
        (unpack64 pin.ptr ++ unpack64 (BitVec.ofNat 64 len)),
      unpack64_length,
      ProofLib.pointsToBytes_append (a + 8#64) (unpack64 pin.ptr) (unpack64 (BitVec.ofNat 64 len)),
      unpack64_length]
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by bv_omega
  rw [h16, ← pointsTo64_eq_pointsToBytes a pin.cap,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) pin.ptr,
      ← pointsTo64_eq_pointsToBytes (a + 16#64) (BitVec.ofNat 64 len)]

theorem vecGF16Of_entails_pin (A : RustAlloc) (a : BitVec 64) (cs : List GF16) :
    vecGF16Of A a cs ⊢
      ∃∗ pin : VecPin,
        (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
          vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs := by
  unfold vecGF16Of vecOf vecAt
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
  rw [← vecHeader_eq_pointsToBytes a ⟨cap, ptr⟩ cs.length]
  exact Entails.refl _

theorem pin_entails_vecGF16Of (A : RustAlloc) (a : BitVec 64) (pin : VecPin) (cs : List GF16) :
    (a ↦ₛ vecHeaderBytesOf pin cs.length) ∗
      vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ⊢
      vecGF16Of A a cs := by
  rw [← vecHeader_eq_pointsToBytes a pin cs.length]
  unfold vecGF16Of vecOf vecAt
  exact Entails.sepExists_right pin.cap (Entails.sepExists_right pin.ptr (Entails.refl _))

theorem vecGF16ListOf_entails_headers_heaps (A : RustAlloc) :
    ∀ (vecs : List (List GF16)) (a : BitVec 64),
      vecGF16ListOf A a vecs ⊢
        ∃∗ pins : List VecPin,
          ⌜pins.length = vecs.length⌝ ∗
            (a ↦ₛ vecHeadersBytesOf pins vecs) ∗
            vecGF16HeapList A pins vecs
  | [], a => by
    simp only [vecGF16ListOf, arrayAt]
    refine Entails.sepExists_right [] ?_
    simp [vecHeadersBytesOf, vecGF16HeapList, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | cs :: vecs, a => by
    simp only [vecGF16ListOf, arrayAt, vecHeaderBytes]
    refine Entails.trans (sepConj_mono (vecGF16Of_entails_pin A a cs)
      (vecGF16ListOf_entails_headers_heaps A vecs (a + 24#64))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pins
    apply Entails.sepExists_elim; intro pin
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs) ∗
        (⌜pins.length = vecs.length⌝ ∗
          ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) =
      ⌜pins.length = vecs.length⌝ ∗
        (((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
          (vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs)) by ac_rfl)) ?_
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right (pin :: pins) ?_
    have hlen' : (pin :: pins).length = (cs :: vecs).length := by simp [hlen]
    refine Entails.pure_right hlen' ?_
    simp only [vecHeadersBytesOf, vecGF16HeapList]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    exact Entails.refl _

theorem headers_heaps_entails_vecGF16ListOf (A : RustAlloc) :
    ∀ (pins : List VecPin) (vecs : List (List GF16)) (a : BitVec 64),
      pins.length = vecs.length →
      (a ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs ⊢
        vecGF16ListOf A a vecs
  | [], [], a, _ => by
    simp [vecHeadersBytesOf, vecGF16HeapList, vecGF16ListOf, arrayAt, ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | pin :: pins, cs :: vecs, a, h => by
    simp only [List.length_cons] at h
    simp only [vecHeadersBytesOf, vecGF16HeapList, vecGF16ListOf, arrayAt, vecHeaderBytes]
    rw [ProofLib.pointsToBytes_append a (vecHeaderBytesOf pin cs.length) (vecHeadersBytesOf pins vecs),
        length_vecHeaderBytesOf]
    refine Entails.trans (Entails.of_eq (show
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ ((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs)) ∗
        (vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs ∗ vecGF16HeapList A pins vecs) =
      ((a ↦ₛ vecHeaderBytesOf pin cs.length) ∗ vecBuf A gf16Stride gf16Align gf16At pin.cap pin.ptr cs) ∗
        (((a + 24#64) ↦ₛ vecHeadersBytesOf pins vecs) ∗ vecGF16HeapList A pins vecs) by ac_rfl)) ?_
    exact sepConj_mono (pin_entails_vecGF16Of A a pin cs)
      (headers_heaps_entails_vecGF16ListOf A pins vecs (a + 24#64) (Nat.succ.inj h))

theorem pointListOf_eq_vecGF16ListOf (A : RustAlloc) :
    ∀ (pts : List Point) (a : BitVec 64),
      pointListOf A a pts = vecGF16ListOf A a (pts.map Point.value)
  | [], _ => rfl
  | pt :: pts, a => by
    have ih := pointListOf_eq_vecGF16ListOf A pts (a + 24#64)
    dsimp only [pointListOf, vecGF16ListOf, vecHeaderBytes] at ih ⊢
    simp only [arrayAt, List.map_cons]
    rw [ih]
    rfl

theorem polyListOf_eq_vecGF16ListOf (A : RustAlloc) :
    ∀ (polys : List LibsignalSpqrV1.Poly) (a : BitVec 64),
      polyListOf A a polys = vecGF16ListOf A a (polys.map LibsignalSpqrV1.Poly.coefficients)
  | [], _ => rfl
  | p :: polys, a => by
    have ih := polyListOf_eq_vecGF16ListOf A polys (a + 24#64)
    dsimp only [polyListOf, vecGF16ListOf, vecHeaderBytes] at ih ⊢
    simp only [arrayAt, List.map_cons]
    rw [ih]
    rfl

/-! ## Specification of `<spqr::encoding::polynomial::PolyEncoder>::from_pb` (`0x62188`) -/

/-- Ghost arguments of `<PolyEncoder>::from_pb` (`0x62188`). -/
structure EncoderFromPbGhost where
  /-- Sret pointer (`x0`, 400-byte `Result<PolyEncoder, PolynomialError>` output). -/
  out : BitVec 64
  /-- Pointer to the 56-byte `ProtoPolynomialEncoder` moved by value (`x1`). -/
  pbA : BitVec 64
  /-- Logical `ProtoPolynomialEncoder` value at `pbA`. -/
  pb : ProtoPolynomialEncoder

def encoderFromPbOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decodePbPointsTotal_value_length_le :
    ∀ (bss : List (List (BitVec 8))) (out : List Point),
      decodePbPointsTotal bss = .ok out →
      (∀ bs ∈ bss, bs.length ≤ 2 * 0x0555555555555555) →
      ∀ pt ∈ out, pt.value.length ≤ 0x0555555555555555
  | [], out, hdec, _ => by
    simp [decodePbPointsTotal] at hdec
    subst hdec
    intro pt hpt; cases hpt
  | bs :: rest, out, hdec, hbound => by
    dsimp only [decodePbPointsTotal] at hdec
    split_ifs at hdec with hodd
    cases hrest : decodePbPointsTotal rest with
    | error e => simp [hrest] at hdec
    | ok tail =>
      simp only [hrest, Except.ok.injEq] at hdec
      subst hdec
      have heven : bs.length % 2 = 0 := by
        simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd
        exact hodd
      intro pt hpt
      simp only [List.mem_cons] at hpt
      rcases hpt with rfl | hmem
      · have hlen := (bytesToGF16List_eq_ok bs heven).2
        have hbs_le := hbound bs (List.mem_cons_self ..)
        change (bytesToGF16ListTotal bs).length ≤ 0x0555555555555555
        omega
      · exact decodePbPointsTotal_value_length_le rest tail hrest
          (fun b hb => hbound b (List.mem_cons_of_mem bs hb)) pt hmem

/-- Specification of `<PolyEncoder>::from_pb` (`0x62188`): consumes `protoPolynomialEncoderAt A pbA pb` at `x1` into `memRegion pbA 56` and writes `resultPolyEncoderFromPbAt A out (fromPbResult pb)` to `x0 = out` (or panics on OOM). -/
def encoderFromPbSpec (A : RustAlloc) : Spec EncoderFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp encoderFromPbStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderFromPbAt A x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool ∗ stackAt s0.sp encoderFromPbStack
  onPanic := fun _ s0 sf => encoderFromPbOnPanic s0 sf

/-- Extended-stack variant of `encoderFromPbSpec` (`encoderFromPbStackX = 1024 + extHookStack`). -/
def encoderFromPbSpecX (A : RustAlloc) : Spec EncoderFromPbGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      (∀ bs ∈ x.pb.pts, bs.length ≤ 2 * 0x0555555555555555)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      protoPolynomialEncoderAt A x.pbA x.pb ∗
      A.pool ∗ stackAt s.sp encoderFromPbStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderFromPbAt A x.out (fromPbResult x.pb) ∗
      memRegion x.pbA protoPolynomialEncoderSize ∗
      A.pool ∗ stackAt s0.sp encoderFromPbStackX
  onPanic := fun _ s0 sf => encoderFromPbOnPanic s0 sf

def EncoderFromPbOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg b ext)
    ((contractProg b ext).fnAddr encoderFromPbName)
    (encoderFromPbSpec A)

def EncoderFromPbOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr encoderFromPbName)
    ((encoderFromPbSpecX A).inImage img)

def EncoderFromPbPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
    (blkPl_374).base
    (encoderFromPbSpec A)

def EncoderFromPbPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
    (blkPl_374).base
    (encoderFromPbSpecX A)

/-! ## Shared `vecU8` Read/Restore and Bitwise Helpers -/

/-- Remaining parts of `vecU8At A a cap ptr bs` after exposing `(a + 8) ↦₆₄ ptr`,
    `(a + 16) ↦₆₄ bs.length`, and `ptr ↦ₛ bs`. -/
def vecU8Rest (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (a ↦₆₄ cap) ∗
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr cap.toNat 1 ∗
     memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_open (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap, ∃∗ ptr,
        ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗
        vecU8Rest A a cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Rest
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbs
    have hnil : (ptr ↦ₛ ([] : List (BitVec 8))) = emp := ProofLib.pointsToBytes_nil ptr
    simp only [hnil, ↓reduceIte]
    refine Entails.trans ?_
      (Entails.of_eq (show
        ⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
          (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
         emp ∗ ((a ↦₆₄ 0#64) ∗ emp)) =
        ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
        emp ∗ ((a ↦₆₄ 0#64) ∗
          ⌜([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
            (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ emp) by ac_rfl))
    refine Entails.pure_right ⟨hle, hcap_lt, hptr⟩ ?_
    exact Entails.of_eq (by ac_rfl)
  · simp only [hcap, ↓reduceIte]
    refine Entails.trans ?_
      (Entails.of_eq (show
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         (ptr ↦ₛ bs) ∗ ((a ↦₆₄ cap) ∗ A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ ((a ↦₆₄ cap) ∗
          ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (A.live ptr cap.toNat 1 ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl))
    refine Entails.pure_right ⟨hle, hcap_lt, hptr⟩ ?_
    exact Entails.of_eq (by ac_rfl)

theorem vecU8_close (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((a + 8#64) ↦₆₄ ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (ptr ↦ₛ bs) ∗
    vecU8Rest A a cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8 vecU8At vecHeader vecU8Rest
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  refine Entails.trans
    (Entails.of_eq (show _ =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
       (ptr ↦ₛ bs) ∗
       (if cap = 0 then emp
        else A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr⟩
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right ⟨hle, hcap_lt, hptr⟩ ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs : bs = [] := by
      cases bs with
      | nil => rfl
      | cons _ _ => simp [BitVec.toNat_ofNat] at hle
    subst hbs
    have hnil : (ptr ↦ₛ ([] : List (BitVec 8))) = emp := ProofLib.pointsToBytes_nil ptr
    simp only [hnil, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem madd_24_eq (j : Nat) (base : BitVec 64) :
    BitVec.ofNat 64 j * 24#64 + base = base + BitVec.ofNat 64 (24 * j) := by
  have hmul : BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_comm]
  rw [hmul, BitVec.add_comm]

theorem lsr_62_nat_eq_zero {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n >>> 62 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64,
    Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt hn

theorem lsr_62_eq_zero {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n >>> 62#64 = 0#64 :=
  lsr_62_nat_eq_zero hn

theorem bit0_and_32_eq_zero_of_even {n : Nat} (heven : n % 2 = 0) (hn : n < 2 ^ 62) :
    (((BitVec.ofNat 64 n).setWidth 32).zeroExtend 64 &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hmod64 : n % 2 ^ 32 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hmod64]
  change (n % 2 ^ 32) &&& (2 ^ 1 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_32_eq_one_of_odd {n : Nat} (hodd : n % 2 ≠ 0) (hn : n < 2 ^ 62) :
    (((BitVec.ofNat 64 n).setWidth 32).zeroExtend 64 &&& 1#64) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hmod64 : n % 2 ^ 32 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.mod_eq_of_lt hmod64]
  change (n % 2 ^ 32) &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_64_eq_zero_of_even {n : Nat} (heven : n % 2 = 0) (hn : n < 2 ^ 62) :
    (BitVec.ofNat 64 n &&& 1#64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  change n &&& (2 ^ 1 - 1) = 0
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem bit0_and_64_eq_one_of_odd {n : Nat} (hodd : n % 2 ≠ 0) (hn : n < 2 ^ 62) :
    (BitVec.ofNat 64 n &&& 1#64) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  change n &&& (2 ^ 1 - 1) = 1
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shiftLeft_1_nat_eq_mul_2 {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have h2n64 : 2 * n < 2 ^ 64 := by omega
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64,
    Nat.mod_eq_of_lt h2n64, Nat.shiftLeft_eq]
  omega

theorem shiftLeft_1_eq_mul_2 {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) :=
  shiftLeft_1_nat_eq_mul_2 hn

theorem shiftRight_1_nat_eq_div_2 {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hdiv64 : n / 2 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64,
    Nat.mod_eq_of_lt hdiv64, Nat.shiftRight_eq_div_pow]

theorem shiftRight_1_eq_div_2 {n : Nat} (hn : n < 2 ^ 62) :
    BitVec.ofNat 64 n >>> 1#64 = BitVec.ofNat 64 (n / 2) :=
  shiftRight_1_nat_eq_div_2 hn

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have h := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  omega

theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false :=
  beq_eq_false_iff_ne.mpr (ofNat_ne_zero_of_pos hpos hn)

theorem bytesToGF16ListTotal_length :
    ∀ (n : Nat) (bs : List (BitVec 8)), bs.length = 2 * n →
      (bytesToGF16ListTotal bs).length = n
  | 0, bs, hlen => by
    cases bs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | n + 1, bs, hlen => by
    rcases bs with _ | ⟨b0, _ | ⟨b1, bs'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · dsimp only [bytesToGF16ListTotal]
      rw [List.length_cons, bytesToGF16ListTotal_length n bs' (by simp at hlen; omega)]

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem seq_clean {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target_pc sm P_mid post) :
    SepWP prog target_pc s P post :=
  SepWP.seq h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hQ)

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

theorem sepWPp_seq_clean {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_mid : State → Prop} {Q Q_panic : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → Q_mid sm →
      SepWPp prog target_pc sm P_mid Q Q_panic) :
    SepWPp prog target_pc s P Q Q_panic :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm Pm hpcm hrunm ⟨hPm, hQm⟩ =>
    SepWPp.weaken_pre hPm (h2 sm hpcm hrunm hQm))

theorem sepWPp_pure_mid {prog : Program} {target_pc : BitVec 64}
    {s : State} {L1 L2 R : SepProp} {φ : Prop}
    {Q Q_panic : State → SepProp → Prop}
    (h : φ → SepWPp prog target_pc s (L1 ∗ L2 ∗ R) Q Q_panic) :
    SepWPp prog target_pc s (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) Q Q_panic := by
  have heq : (L1 ∗ L2 ∗ ⌜φ⌝ ∗ R) = (⌜φ⌝ ∗ (L1 ∗ L2 ∗ R)) := by ac_rfl
  rw [heq]
  exact SepWPp.pure_left h

/-- An unallocated `Vec<GF16>` slot `(cap = 0, ptr = 2, len = 0)` at `addr` (24 bytes). -/
def emptySlotAt (addr : BitVec 64) : SepProp :=
  (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 2#64) ∗ ((addr + 16#64) ↦₆₄ 0#64)

/-- `n` contiguous `emptySlotAt` headers starting at `base` with stride 24. -/
def emptySlotsAt (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => emptySlotAt base ∗ emptySlotsAt (base + 24#64) n

theorem emptySlotAt_entails_vecGF16Of (A : RustAlloc) (addr : BitVec 64) :
    emptySlotAt addr ⊢ vecGF16Of A addr [] := by
  unfold emptySlotAt vecGF16Of vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 2#64 ?_)
  have hp : ([] : List GF16).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * gf16Stride < 2 ^ 63 ∧ (2#64 : BitVec 64) ≠ 0 := by decide
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live 2#64 ((0#64 : BitVec 64).toNat * gf16Stride) gf16Align ∗
        arrayAt gf16At gf16Stride 2#64 [] ∗
        memRegion (2#64 + BitVec.ofNat 64 (([] : List GF16).length * gf16Stride))
          (((0#64 : BitVec 64).toNat - ([] : List GF16).length) * gf16Stride)) = emp := rfl
  rw [hite, sepConj_emp]
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (sepConj_comm _ _)

theorem emptySlotsAt_entails_vecGF16ListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      emptySlotsAt base n ⊢ vecGF16ListOf A base (List.replicate n [])
  | 0, base => by
    simp [emptySlotsAt, vecGF16ListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    simp only [emptySlotsAt, List.replicate_succ, vecGF16ListOf, arrayAt, vecHeaderBytes,
      BitVec.ofNat_eq_ofNat]
    exact sepConj_mono (emptySlotAt_entails_vecGF16Of A base)
      (emptySlotsAt_entails_vecGF16ListOf A n (base + 24#64))

theorem vecGF16ListOf_append (A : RustAlloc) :
    ∀ (xs ys : List (List GF16)) (base : BitVec 64),
      vecGF16ListOf A base (xs ++ ys) =
        vecGF16ListOf A base xs ∗ vecGF16ListOf A (base + BitVec.ofNat 64 (24 * xs.length)) ys
  | [], ys, base => by
    simp [vecGF16ListOf, arrayAt]
  | x :: xs, ys, base => by
    have ih := vecGF16ListOf_append A xs ys (base + 24#64)
    dsimp only [vecGF16ListOf, vecHeaderBytes] at ih ⊢
    simp only [List.cons_append, arrayAt, BitVec.ofNat_eq_ofNat, ih, sepConj_assoc]
    congr 2
    have hadd : (base + 24#64) + BitVec.ofNat 64 (24 * xs.length) =
        base + BitVec.ofNat 64 (24 * (x :: xs).length) := by
      simp only [List.length_cons, Nat.mul_add, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega
    rw [hadd]

theorem sepWP_cells_succ {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target_pc s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) post) :
    SepWP prog target_pc s (cells a (k + 1) ∗ Rest) post := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact ProofLib.SepWP.exists_left h

theorem sepWP_cells_zero {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s Rest post) :
    SepWP prog target_pc s (cells a 0 ∗ Rest) post := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

theorem ult_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_true_eq]
  exact hlt

theorem not_ult_of_ge {a b : Nat} (hge : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
  have hb : b < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

theorem ule_false_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

theorem ule_true_of_le {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 a) = true := by
  have hb : b < 2 ^ 64 := by omega
  simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_true_eq]
  exact hle

theorem bne_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true := by
  have ha : a < 2 ^ 64 := by omega
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  omega

theorem bne_of_gt {a b : Nat} (hlt : b < a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true := by
  have hb : b < 2 ^ 64 := by omega
  rw [bne_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  omega

theorem beq_false_of_lt {a b : Nat} (hlt : a < b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  have ha : a < 2 ^ 64 := by omega
  apply beq_false_of_ne
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  omega

theorem beq_false_of_gt {a b : Nat} (hlt : b < a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  have hb : b < 2 ^ 64 := by omega
  apply beq_false_of_ne
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ht
  omega

theorem ofNat_add_one (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  rw [← BitVec.ofNat_add]

theorem ofNat_add_two (k : Nat) :
    BitVec.ofNat 64 (2 * k) + 2#64 = BitVec.ofNat 64 (2 * (k + 1)) := by
  simp [Nat.mul_add, BitVec.ofNat_add]

theorem memRegion_two_cons (dstPtr : BitVec 64) (done n : Nat)
    (hbound : 2 * (n + 1) < 2 ^ 63) :
    memRegion (dstPtr + BitVec.ofNat 64 (2 * done)) (2 * (n + 1)) =
      (∃∗ v : BitVec 16, (dstPtr + BitVec.ofNat 64 (2 * done)) ↦₁₆ v) ∗
        memRegion (dstPtr + BitVec.ofNat 64 (2 * (done + 1))) (2 * n) := by
  have hmul : 2 * (n + 1) = 2 + 2 * n := by omega
  have hadd : dstPtr + BitVec.ofNat 64 (2 * done) + 2#64 =
      dstPtr + BitVec.ofNat 64 (2 * (done + 1)) := by
    rw [BitVec.add_assoc, ofNat_add_two]
  rw [hmul, ProofLib.memRegion_split (dstPtr + BitVec.ofNat 64 (2 * done)) 2 (2 * n) (by omega),
      ProofLib.memRegion_two, hadd]

end CryptoVerification.SpqrV1.Poly.EncoderFromPb
