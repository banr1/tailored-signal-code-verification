/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoder -- shake: keep

/-!
# Exact-Capacity Specifications and Proofs for `PolynomialEncoder::encode` and `PolynomialDecoder::encode`

In `Poly.protoPolynomialEncoderPinnedAt` and `Poly.protoPolynomialDecoderPinnedAt`, the `Vec<Vec<u8>>`
headers carry the Rust `Vec` invariant `cap.toNat * 24 < 2 ^ 63`, which yields `pts.length * 24 < 2 ^ 63`
and `polys.length * 24 < 2 ^ 63` (hence `< 2 ^ 59`).

This module lifts `encode_repeated [local#2]` from `< 2 ^ 58` to `< 2 ^ 59` (reusing
`EncodeRepeated2.step_iter` and `EncodeRepeated2.step_latch_zero` directly) and proves exact-capacity
specifications for `PolynomialEncoder::encode [local#2]` and
`PolynomialDecoder::encode [local#2]` with no external `pts.length` / `polys.length`
preconditions.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. `encode_repeated [local#2]` with `elems.length < 2 ^ 59` -/

open Lean Meta Elab Tactic in
local elab "encRepeated2_fetches_range " b:term:max H:term:max sym:str
    kStart:num kEnd:num : tactic => do
  let offExpr ← elabTerm (← `((ls_off% $sym : Nat))) (some (mkConst ``Nat))
  let off ← whnfD offExpr
  let some off := off.rawNatLit? <|> off.nat?
    | throwError "encRepeated2_fetches_range: could not reduce ls_off%"
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Varint |>.str
      ("libsignalSessionBin_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k))))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) (ls_lemma% fnOff $sym) (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) (ls_lemma% fnOff $sym) (by decide) $dec))

theorem setup_x24_eq_59 {n : Nat} (hlt : n < 2 ^ 59) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 =
      BitVec.ofNat 64 (24 * n) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2n : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3n : (BitVec.ofNat 64 (3 * n)).toNat = 3 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h24n : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, hn, h2n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 (3 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hn, h2n, h3n, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, h3n, h24n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

theorem latch_sub24_eq_59 (k : Nat) (hk : k + 1 < 2 ^ 59) :
    BitVec.ofNat 64 (24 * (k + 1)) - 24#64 = BitVec.ofNat 64 (24 * k) := by
  have hk_toNat : (BitVec.ofNat 64 (24 * (k + 1))).toNat = 24 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk0_toNat : (BitVec.ofNat 64 (24 * k)).toNat = 24 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hle : (24#64 : BitVec 64) ≤ BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [BitVec.le_def, hk_toNat]
    change 24 ≤ 24 * (k + 1)
    omega
  rw [BitVec.toNat_sub_of_le hle, hk_toNat, hk0_toNat]
  change 24 * (k + 1) - 24 = 24 * k
  omega

def encodeRepeated59SpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeRepeatedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeRepeatedStackOf resStack)
  post := (encodeRepeatedSpecOf resStack A).post
  onPanic := (encodeRepeatedSpec A).onPanic

theorem step_latch_succ_59 (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name + 84#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name + 96#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  encRepeated2_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" 84 96
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name = entry
  examples_hide_fetches
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply SepWPp.of_sepWP_cs (mid := entry + 96#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSaved, arm64_norm, *, and_self]))

theorem step_loop_59 {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy"))
      sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name + 228#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      EncRepeatedCalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  induction elems generalizing curBase curCap curPtr curBs s P F with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    rcases head with ⟨elemPtr, elemBs⟩
    subst hP
    simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit
    have hfit_head : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
        curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine EncodeRepeated2.step_iter hres b A ext henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine EncodeRepeated2.step_latch_zero b A ext sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1))
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 59 := helem_cnt
      set tail := nextHead :: rest'
      refine step_latch_succ_59 b A ext v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
        tail.length hrest_pos helem_cnt'
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 ?_
      intro s1' hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
      have hfit_rest : (curBs ++ encodeBytesField tag (some elemBs)).length +
          (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat ∨
          (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length + 10 < 2 ^ 62 := by
        rw [List.length_append]
        rcases hfit with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      refine ih hrest_ne (by omega) (curBase + 24#64) cap1 ptr1
        (curBs ++ encodeBytesField tag (some elemBs)) hfit_rest
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗ F)
        hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
        (by ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 hge2 hpres2
      have hpres_all : curBs.length +
          (encodeRepeatedBytes tag (((elemPtr, elemBs) :: tail).map Prod.snd)).length ≤
          curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap
        simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit_cap
        obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
        have h2 : (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat := by
          rw [hc1, List.length_append]; omega
        obtain ⟨hc2, hp2⟩ := hpres2 h2
        exact ⟨hc2.trans hc1, hp2.trans hp1⟩
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 (by omega) hpres_all)
      clear_value tail
      rw [repeatedBytesSliceAt_cons, List.map_cons, encodeRepeatedBytes_cons, ← List.append_assoc]
      exact Entails.of_eq (by ac_rfl)

theorem encode_repeated_2_59_gen_ok_ext {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (withEncRepeatedCS s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy"))
      sessionMemcpyRegionSpec)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59SpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeated59SpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := step_loop_59 hres b A ext henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59SpecOf resStack A).pre x s0, hpre, ?_⟩
  encRepeated2_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" 0 56
  encRepeated2_fetches_range b (Rust.withPanics ext)
    "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" 228 252
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name = entry
  examples_hide_fetches
  dsimp only [encodeRepeated59SpecOf, encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩ => ?_
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit ⊢
  cases elems with
  | nil =>
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap.toNat ∧
        (bs.length +
            (encodeRepeatedBytes tag
              (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).length ≤ cap.toNat →
          cap = cap ∧ ptr = ptr)) = True :=
      eq_true ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨cap, ptr, by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    simpa only [List.map_nil, encodeRepeatedBytes_nil, List.append_nil, sepConj_assoc] using hPR
  | cons head rest =>
    have hne : head :: rest ≠ [] := List.cons_ne_nil _ _
    have hpos : 0 < (head :: rest).length := List.length_pos_of_ne_nil hne
    have hcbz : (BitVec.ofNat 64 (head :: rest).length == 0#64) = false :=
      len_beq_zero_false hpos (by omega)
    have hx24_setup := setup_x24_eq_59 helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
      SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
      SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
      SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
      SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => ?_
    apply SepWPp.of_sepWP_cs (mid := entry + 96#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_pro
    have hx20_setup := setup_x20_eq htag2
    set savedCells : SepProp :=
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ v3) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
    have hpre_loop :
        repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (0x30 + resStack) ∗ savedCells =
        (repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (0x30 + resStack)) ∗ savedCells := by
      simp only [sepConj_assoc]
    clear_value savedCells
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    refine hloop tag v s0.sp (head :: rest) hne helem_cnt base cap ptr bs hfit
      (F := savedCells)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign64
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ((EncRepeatedCalleeSaved.refl s0).step (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv_pro)
      hpre_loop ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hcsm hge hpres
    rcases hcsm with ⟨hx26m, hx27m, hx28m, hvregs, _⟩
    rw [hsaved_def]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap'.toNat ∧
        (bs.length + (encodeRepeatedBytes tag ((head :: rest).map Prod.snd)).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)) = True :=
      eq_true ⟨hge, hpres⟩
    simp only [satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 25#5), v3, s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 19#5), cap', ptr',
      by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    convert hPR using 1
    ac_rfl

theorem encode_repeated_2_59_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name)
      (encodeRepeated59SpecOf doReserveStack A) := by
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [EncodeRepeated2.encodeVarint4_fnAddr_eq]
    exact encode_varint4_fit_ok_ext hA
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      (doReserveSpecOf doReserveStack A) := by
    rw [EncodeRepeated2.doReserve7_fnAddr_eq]
    exact do_reserve_7_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeRepeated2Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeRepeated2Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  obtain ⟨P, hP, hwp⟩ := encode_repeated_2_59_gen_ok_ext (resStack := doReserveStack) (by decide)
    (subroutine_ok_withEncRepeatedCS s0 henc0)
    (subroutine_ok_withEncRepeatedCS s0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_2_59_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name)
      ((encodeRepeated59SpecOf doReserveStackX A).inImage img) := by
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [EncodeRepeated2.encodeVarint4_fnAddr_eq]
    exact encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name +
        bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" -
          ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"))
      ((doReserveSpecOf doReserveStackX A).inImage img) := by
    rw [EncodeRepeated2.doReserve7_fnAddr_eq]
    exact hdoReserve
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeRepeated2Name +
        BitVec.ofNat 64 (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy"))
      sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeRepeated2Name
      (ls_rel% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" "memcpy")
      (by rw [(ls_lemma% fnOff "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]"), (ls_stub% "memcpy")])
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (encodeRepeated59SpecOf doReserveStackX A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encode_repeated_2_59_gen_ok_ext (resStack := doReserveStackX) (by decide)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 henc0)
    (subroutine_ok_withEncRepeatedCS_x img s0 himg0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

/-! ## 2. Call & Tailcall Wrappers for `encodeRepeated59SpecOf` -/

theorem step_msg48_encode_repeated59_call {resStack : Nat} (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeRepeated59SpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp ret_pc : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29)
    (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag)
    (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length)
    (hx3 : s.readReg64 .x3 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → MsgEnc48CalleeSaved s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((repeatedBytesSliceAt base elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_48_aligned halign
  refine SepWPp.call_cs (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs) (F := F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withMsgEnc48CS, encodeRepeated59SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeRepeated59SpecOf, encodeRepeatedSpec, encodeRepeatedSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeRepeated59SpecOf, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)

theorem step_msg48_encode_repeated59_tailcall {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hencRep : subroutine_ok (tripleRatchetProgAtExt b ext) call_pc
      (withMsgEnc48CS s0 (encodeRepeated59SpecOf resStack A)))
    (tag : Nat) (base v curCap curPtr sp fp lr r21 v3 r20 r19 : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 29)
    (helems : elems.length < 2 ^ 59)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr)
    (hw0 : s.readReg32 .x0 = BitVec.ofNat 32 tag)
    (hx1 : s.readReg64 .x1 = base)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 elems.length)
    (hx3 : s.readReg64 .x3 = v)
    (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((repeatedBytesSliceAt base elems ∗
        vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact halign
  refine SepWPp.call_cs (x := EncodeRepeatedGhost.mk tag base elems v curCap curPtr curBs)
    (F := memRegion (sp - BitVec.ofNat 64 (msgEnc48RepeatedStackOf resStack)) 48 ∗ F)
    hencRep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hm0 : s.mem ⊨ (stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ msgEnc48SavedFrame sp fp lr r21 v3 r20 r19) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') := by
      rw [hP] at hm; convert hm using 1; ac_rfl
    have hm1 : s.mem ⊨ stackAt sp (msgEnc48RepeatedStackOf resStack) ∗
        (repeatedBytesSliceAt base elems ∗ vecU8At A v curCap curPtr curBs ∗ A.pool ∗ F ∗ R') :=
      Satisfies.mono
        (sepConj_mono_left (stackAt_msgEnc48_repeated_recombine hres sp fp lr r21 v3 r20 r19))
        hm0
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp] at hm1
    simp only [withMsgEnc48CS, encodeRepeated59SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcs, ⟨hw0, hx1, hx2, hx3, htag1, htag2, helems, hfit⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withMsgEnc48CS, encodeRepeated59SpecOf, encodeRepeatedSpec, encodeRepeatedSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withMsgEnc48CS, encodeRepeated59SpecOf, encodeRepeatedSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    rw [sepConj_left_comm (repeatedBytesSliceAt base elems)]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    have hccm : CalleeSavedPreserved s0 sm := by
      rcases hcc with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hv⟩
      rcases hcsm with ⟨h19', h20', h21', h22', h23', h24', h25', h26', h27', h28', hfp', hv'⟩
      exact ⟨h19'.trans h19, h20'.trans h20, h21'.trans h21, h22'.trans h22, h23'.trans h23,
        h24'.trans h24, h25'.trans h25, h26'.trans h26, h27'.trans h27, h28'.trans h28, hfp'.trans hfp, hv'.trans hv⟩
    refine SepWPp.weaken_pre ?_
      (SepWPp.done hpcm hrunm
        (hnext sm nextCap nextPtr hpcm hrunm hspm htrm' hccm
          (hcs.trans (MsgEnc48CalleeSaved.of_calleeSavedPreserved hcsm hinv_call)) hge hpres))
    rw [stackAt_msgEnc48_repeated_eq_bottom hres sp]
    exact Entails.of_eq (by ac_rfl)

private theorem cap_beq_len_false_of_lt {cap : BitVec 64} {len : Nat}
    (hlt : len < cap.toNat) :
    (cap == BitVec.ofNat 64 len) = false := by
  have hcap : cap.toNat < 2 ^ 64 := BitVec.isLt cap
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

/-! ## 3. Exact-Capacity `PolynomialEncoder::encode [local#2]` -/

def encodePolyEncoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

private theorem pe2_fetch_add' {b : BitVec 64} {ext : String → Option (State → State)}
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry)
    {k : Nat} {ins : Instr}
    (h1 : (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) = some ins) :
    (tripleRatchetProgAtExt b ext).fetch (entry + BitVec.ofNat 64 k) = some ins := by
  subst hfn; exact h1

open Lean Meta Elab Tactic in
scoped elab "pe2_fetches' " b:term:max H:term:max hfn:ident kStart:num kEnd:num : tactic => do
  let sym := Syntax.mkStrLit "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"
  let offExpr ← elabTerm (← `((ls_off% $sym : Nat))) (some (mkConst ``Nat))
  let off ← whnfD offExpr
  let some off := off.rawNatLit? <|> off.nat?
    | throwError "pe2_fetches': could not reduce ls_off%"
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      ("libsignalSessionBin_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k))))
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := pe2_fetch_add' $hfn (k := $kq) ($fetchAdd (b := $b) (H := $H) (k := $kq) (ls_lemma% fnOff $sym) (by decide) $dec)))

private theorem step_pe_hdr_exact {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn2 : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry)
    {s0 s : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"))
      (withMsgEnc48CS s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = entry + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A encA g ptsElems polysElems ∗
          vecU8At A v cap0 ptr0 (bs0 ++ polyEncoderHeaderBytes pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntry b ext entry := Or.inr hfn2
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  have hlt0 : bs0.length < cap0.toNat := by omega
  have hcap_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := cap_beq_len_false_of_lt hlt0
  refine step_polyEncoder_prologue hres b ext hfn encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1
  pe2_fetches' b (Rust.withPanics ext) hfn2 20 40
  pe2_fetches' b (Rust.withPanics ext) hfn2 64 68
  pe2_fetches' b (Rust.withPanics ext) hfn2 72 76
  examples_hide_fetches
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0, vecHeader]
  apply SepWPp.of_sepWP_cs (mid := entry + 40#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0]
  refine step_polyEncoder_push_hdr_tag b A ext hfn encA v cap0 ptr0 sp bs0 hlt0
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (F := stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ A.pool ∗ F)
    (by ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyEncLen_call hres128 b A ext hencLen encA sp (entry + 68#64) g pb hlen_lt
    (F := vecU8At A v cap0 ptr0 (bs0 ++ [0x12#8]) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyEncoder_mov_x1_x19_68 b ext hfn
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) encA v sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ [0x12#8]).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  refine step_msg48rep_encode_varint_call hres128 b A ext hencVarint
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) v cap0 ptr0 sp (entry + 76#64)
    (bs0 ++ [0x12#8]) (Or.inl hfit_len)
    (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      polyEncoderRestAt A encA g ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyEncoderHeaderBytes bs0 pb]
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

private theorem step_pe_idx_exact {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn2 : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry)
    {s0 s : State}
    (hencVarint : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (encA v curCap curPtr sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_idx : curBs.length + (Proto.encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 76#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A v curCap curPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.idx) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntry b ext entry := Or.inr hfn2
  refine step_polyEncoder_check_idx b ext hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt hlt0
    pe2_fetches' b (Rust.withPanics ext) hfn2 84 100
    pe2_fetches' b (Rust.withPanics ext) hfn2 124 128
    examples_hide_fetches
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
    apply SepWPp.of_sepWP_cs (mid := entry + 100#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs]
    refine step_polyEncoder_push_idx_tag b A ext hfn encA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ A.pool ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_msg48rep_encode_varint_call hres b A ext hencVarint
      (pb.idx.zeroExtend 64) v curCap curPtr sp (entry + 128#64) (curBs ++ [0x08#8]) (Or.inl hfit_v)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_idx_of_ne_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hidx, ↓reduceIte] at hpc1
    rw [← bs_append_idx_of_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pe_pts_polys_exact {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn2 : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry)
    {s0 s : State}
    (hencRep : subroutine_ok (tripleRatchetProgAtExt b ext)
      (entry + bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (withMsgEnc48CS s0 (encodeRepeated59SpecOf resStack A)))
    (encA v curCap curPtr sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts59 : pb.pts.length < 2 ^ 59)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys59 : pb.polys.length < 2 ^ 59)
    (hfit_pts : curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat)
    (hfit_polys : (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts).length +
      (Varint.encodeRepeatedBytes 3 pb.polys).length ≤ curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSaved s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSaved s0 sf →
      Q sf ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        vecU8At A v curCap curPtr
          ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntry b ext entry := Or.inr hfn2
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hpolys_len : polysElems.length = pb.polys.length := by rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_pts b ext hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  pe2_fetches' b (Rust.withPanics ext) hfn2 140 144
  pe2_fetches' b (Rust.withPanics ext) hfn2 168 172
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated59_call b A ext hencRep 2 g.pts.ptr v curCap curPtr sp
    (entry + 144#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact Or.inl hfit_pts)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.polys.ptr polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq] at hpres2 ⊢
  obtain ⟨hcap2, hptr2⟩ := hpres2 hfit_pts
  subst cap2 ptr2
  refine step_polyEncoder_prep_polys_epilogue b ext hfn encA v sp sv3 g pb ptsElems polysElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v curCap curPtr (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hw0_3 hx1_3 hx2_3 hx3_3 hcc3 hcs3
  apply SepWPp.of_sepWP_cs (mid := entry + bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]")); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  exact step_msg48_encode_repeated59_tailcall
    (s := s3.setPC (entry + bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]")))
    hres b A ext hencRep 3 g.polys.ptr v curCap curPtr sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems
    (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) (by decide) (by decide) (by omega)
    (by rw [hpolys_eq]; exact Or.inl hfit_polys)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun3)
    ((State.sp_setPC _ _).trans hsp3)
    halign
    ((State.trace_setPC _ _).trans htr3)
    ((State.readReg64_setPC _ _ _).trans hlr3)
    (by dsimp only [State.readReg32] at hw0_3 ⊢; rw [State.readReg64_setPC]; exact hw0_3)
    ((State.readReg64_setPC _ _ _).trans hx1_3)
    (by rw [State.readReg64_setPC, hpolys_len]; exact hx2_3)
    ((State.readReg64_setPC _ _ _).trans hx3_3)
    (calleeSavedPreserved_setPC _ hcc3)
    (msgEnc48CalleeSaved_setPC _ hcs3 hinv3)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl)
    (fun sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf _ hpres3 => by
      rw [hpolys_eq] at hpres3 ⊢
      obtain ⟨hncap, hnptr⟩ := hpres3 hfit_polys
      subst nextCap nextPtr
      have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
      have hEq :
          ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
            vecU8At A v curCap curPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
          ((repeatedBytesSliceAt g.polys.ptr polysElems ∗
            vecU8At A v curCap curPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
            (((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
              ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)) := by
        dsimp only [polyEncoderElemsAt]; ac_rfl
      rwa [← hEq])

theorem polyEncoder2_exact_gen_ok_ext {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodePolyEncoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"))
      (withMsgEnc48CS s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (withMsgEnc48CS s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (withMsgEnc48CS s0 (encodeRepeated59SpecOf resStack A)))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have hfn2 : (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name =
      (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name := rfl
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyEncoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyEncoderMsg_len_split x.enc
  have hlen_le_msg := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by omega
  refine step_pe_hdr_exact hres b A ext hfn2 hencLen hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc x.bs
    hlen_lt (by omega) (F := emp) rfl hpc hrun rfl halign rfl hx0 hx1 (MsgEnc48CalleeSaved.refl s0) rfl ?_
  intro s1 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  have hfit_idx : (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (Proto.encodeUint32Field 1#32 x.enc.idx).length ≤ x.cap.toNat := by
    rw [List.length_append]; omega
  refine step_pe_idx_exact hres128 b A ext hfn2 hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc
    ptsElems polysElems (x.bs ++ polyEncoderHeaderBytes x.enc) hfit_idx
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_idx := (x.bs ++ polyEncoderHeaderBytes x.enc) ++ Proto.encodeUint32Field 1#32 x.enc.idx
  have hfit_pts : bs_idx.length + (Varint.encodeRepeatedBytes 2 x.enc.pts).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega
  have hfit_polys : (bs_idx ++ Varint.encodeRepeatedBytes 2 x.enc.pts).length +
      (Varint.encodeRepeatedBytes 3 x.enc.polys).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pe_pts_polys_exact hres b A ext hfn2 hencR x.encA x.v x.cap x.ptr s0.sp sv3 x.g x.enc
    ptsElems polysElems bs_idx hpts_eq (by omega) hpolys_eq (by omega) hfit_pts hfit_polys
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗ emp) (by dsimp [bs_idx]; ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyEncoderElemsAt x.encA x.g x.enc ptsElems polysElems ∗
      polyEncoderRestAt A x.encA x.g ptsElems polysElems) ∗
      (vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyEncoderMsg x.bs x.enc]
    convert hm using 1; dsimp [bs_idx]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.encA x.enc _ sf.mem).mpr
    ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_pack⟩
  dsimp only [encodePolyEncoderExactSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; ac_rfl

theorem encode_polyEncoder_2_exact_pinned_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name)
      (encodePolyEncoderExactSpecOf doReserveStack A) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"))
      (polynomialEncoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyEncoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyEncLenElemsOut_of_pinned (polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [encodePolyEncoder2_encodeVarint4_fnAddr_eq]; exact encode_varint4_fit_ok_ext hA
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      (encodeRepeated59SpecOf doReserveStack A) := by
    rw [encodePolyEncoder2_encodeRepeated2_fnAddr_eq]; exact encode_repeated_2_59_ok_ext hA
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_exact_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencV0)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_exact_pinned_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name)
      ((encodePolyEncoderExactSpecOf doReserveStackX A).inImage img) := by
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::PolynomialEncoder as prost::message::Message>::encoded_len [local#2]"))
      (polynomialEncoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyEncoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyEncLenElemsOut_of_pinned (polynomialEncoderEncodedLen_local2_pinned_ok_ext img.base A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyEncoder2_encodeVarint4_fnAddr_eq]
    exact encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name +
        bv% (2 ^ 64 + ls_off% "prost::encoding::bytes::encode_repeated::<alloc::vec::Vec<u8>, alloc::vec::Vec<u8>> [local#2]" - ls_off% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"))
      ((encodeRepeated59SpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyEncoder2_encodeRepeated2_fnAddr_eq]
    exact encode_repeated_2_59_ok_ext_x hA
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_exact_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CS_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencV0)
    (subroutine_ok_withMsgEnc48CS_x img s0 hinv0 hencR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩


end CryptoVerification.SpqrV1.Prost.EncodeToVec
