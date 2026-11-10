/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<chain::MessageKey as prost::Message>::encoded_len`

Verifies the leaf function `MessageKey::encoded_len` (`16`-byte frame): sums the protobuf field
lengths of a stored skipped `MessageKey` (tag 1 `index`, empty tags 2–4, and tag 5 `seed`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  ule_zero_64 ult_zero_64

/-! ## Hardware Varint Length Equivalence -/

private theorem or_one_ne_zero (v : BitVec 64) : v ||| 1#64 ≠ 0#64 := by
  intro h
  have h0 := congrArg (fun x : BitVec 64 => x.getLsbD 0) h
  simp at h0

private theorem or_one_clz_toNat_lt (v : BitVec 64) : (v ||| 1#64).clz.toNat < 64 := by
  have hle : (v ||| 1#64).clz ≤ 64#64 := BitVec.clz_le
  have hne : (v ||| 1#64).clz ≠ 64#64 :=
    mt BitVec.clz_eq_iff_eq_zero.mp (or_one_ne_zero v)
  have hle_nat : (v ||| 1#64).clz.toNat ≤ 64 := hle
  have hne_nat : (v ||| 1#64).clz.toNat ≠ 64 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    exact h
  omega

private theorem shiftRight_lt_128_iff (v : BitVec 64) (s : Nat) :
    ((v >>> s).toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ s + 7 := by
  have hxne : v ||| 1#64 ≠ 0#64 := or_one_ne_zero v
  have hlo : 2 ^ (63 - (v ||| 1#64).clz.toNat) ≤ (v ||| 1#64).clz.toNat * 0 + (v ||| 1#64).toNat := by
    simpa using BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (by decide) hxne
  have hhi : (v ||| 1#64).toNat < 2 ^ (64 - (v ||| 1#64).clz.toNat) :=
    BitVec.toNat_lt_two_pow_sub_clz
  have h1 : (v >>> s).toNat < 128 ↔ v.toNat >>> (s + 7) = 0 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.pow_add, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_eq_zero_iff_lt (by decide)).symm
  have h2 : (v ||| 1#64).toNat >>> (s + 7) = v.toNat >>> (s + 7) := by
    change (v.toNat ||| 1) >>> (s + 7) = v.toNat >>> (s + 7)
    rw [Nat.shiftRight_or_distrib]
    have h1z : 1 >>> (s + 7) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      have : 2 ^ 7 ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.div_eq_of_lt (by omega)
    rw [h1z, Nat.or_zero]
  rw [h1, ← h2, Nat.shiftRight_eq_div_pow]
  constructor
  · intro hdiv
    by_contra hgt
    have hle : s + 7 ≤ 63 - (v ||| 1#64).clz.toNat := by omega
    have hpow : 2 ^ (s + 7) ≤ 2 ^ (63 - (v ||| 1#64).clz.toNat) := Nat.pow_le_pow_right (by decide) hle
    have hlt := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos (s + 7))).mp hdiv
    omega
  · intro hle
    have hpow : 2 ^ (64 - (v ||| 1#64).clz.toNat) ≤ 2 ^ (s + 7) := Nat.pow_le_pow_right (by decide) hle
    exact Nat.div_eq_of_lt (by omega)

private def clzTree (c : BitVec 64) : Nat :=
  if 64 - c.toNat ≤ 7 then 1
  else if 64 - c.toNat ≤ 14 then 2
  else if 64 - c.toNat ≤ 21 then 3
  else if 64 - c.toNat ≤ 28 then 4
  else if 64 - c.toNat ≤ 35 then 5
  else if 64 - c.toNat ≤ 42 then 6
  else if 64 - c.toNat ≤ 49 then 7
  else if 64 - c.toNat ≤ 56 then 8
  else if 64 - c.toNat ≤ 63 then 9
  else 10

private theorem hwFormula_eq_clzTree_of_lt :
    ∀ k : Fin 64,
      let c := BitVec.ofNat 64 k.val
      ((((c ^^^ 0x3f#64) + ((c ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
        BitVec.ofNat 64 (clzTree c)) := by
  decide

private theorem ushiftRight_add_64 (w : BitVec 64) (a b : Nat) :
    (w >>> a) >>> b = w >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

private theorem encodeVarint_length_eq_clzTree (v : BitVec 64) :
    (encodeVarint v).length = clzTree (v ||| 1#64).clz := by
  unfold encodeVarint clzTree
  dsimp only [encodeVarintAux]
  have h0_eq : (v.toNat < 128) ↔ 64 - (v ||| 1#64).clz.toNat ≤ 7 := by
    simpa using shiftRight_lt_128_iff v 0
  simp only [ushiftRight_add_64, Nat.reduceAdd, h0_eq, shiftRight_lt_128_iff]
  have h10 : 64 - (v ||| 1#64).clz.toNat ≤ 70 := by omega
  by_cases c1 : 64 - (v ||| 1#64).clz.toNat ≤ 7 <;> simp only [c1, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c2 : 64 - (v ||| 1#64).clz.toNat ≤ 14 <;> simp only [c2, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c3 : 64 - (v ||| 1#64).clz.toNat ≤ 21 <;> simp only [c3, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c4 : 64 - (v ||| 1#64).clz.toNat ≤ 28 <;> simp only [c4, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c5 : 64 - (v ||| 1#64).clz.toNat ≤ 35 <;> simp only [c5, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c6 : 64 - (v ||| 1#64).clz.toNat ≤ 42 <;> simp only [c6, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c7 : 64 - (v ||| 1#64).clz.toNat ≤ 49 <;> simp only [c7, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c8 : 64 - (v ||| 1#64).clz.toNat ≤ 56 <;> simp only [c8, ↓reduceIte, List.length_cons, List.length_nil]
  by_cases c9 : 64 - (v ||| 1#64).clz.toNat ≤ 63 <;> simp only [c9, ↓reduceIte, List.length_cons, List.length_nil, h10]

@[local simp, local arm64_norm]
private theorem mkHwVarintLen_eq_encodeVarint_length (v : BitVec 64) :
    ((((v ||| 1#64).clz ^^^ 0x3f#64) + (((v ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (encodeVarint v).length := by
  have hlt := or_one_clz_toNat_lt v
  have hfin := hwFormula_eq_clzTree_of_lt ⟨(v ||| 1#64).clz.toNat, hlt⟩
  have hclz : BitVec.ofNat 64 (v ||| 1#64).clz.toNat = (v ||| 1#64).clz := by
    apply BitVec.eq_of_toNat_eq
    simp
  dsimp only at hfin
  rw [hclz] at hfin
  rw [hfin, encodeVarint_length_eq_clzTree]

/-! ## Instruction Decode and Fetch Lemmas -/

gen_decodes libsignalSessionCode_tree mkLen [(ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len") → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 48), (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 120) → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 132),
    (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 164) → (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" + 248)]

open Lean Elab Tactic in
/-- Fetches instructions of `MessageKey::encoded_len` in `[kStart, kEnd)`. -/
elab "mkLen_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len")
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt |>.str
      s!"mkLen_decode_{"0x" ++ String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-! ## Layout decomposition and arithmetic helpers -/

private def msgKeyCells (a : BitVec 64) (mk : MessageKeyGenerator) : SepProp :=
  ((a + 16#64) ↦₆₄ 0#64) ∗
  ((a + 40#64) ↦₆₄ 0#64) ∗
  ((a + 64#64) ↦₆₄ 0#64) ∗
  ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗
  ((a + 96#64) ↦₃₂ mk.counter)

private def msgKeyRest (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
  (a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗ vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
  ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗ vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
  ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗ vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
  ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗ vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
  memRegion (a + 100#64) 4

private theorem messageKeyAt_eq_cells_sep_rest (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) (a : BitVec 64) :
    messageKeyAt A gk a = msgKeyCells a gk.2 ∗ msgKeyRest A gk a := by
  simp only [messageKeyAt, msgKeyCells, msgKeyRest, vecU8At_eq_header_sep_buf, vecHeader,
    List.length_nil, sepConj_assoc, arm64_norm]
  ac_rfl

private theorem msgKeyRest_seed_bounds {A : RustAlloc} {gk : MessageKeyGhost × MessageKeyGenerator}
    {a : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ msgKeyRest A gk a ∗ R) :
    gk.2.seed ≠ [] ∧ gk.2.seed.length < 2 ^ 63 := by
  unfold msgKeyRest at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  refine ⟨hm.1, ?_⟩
  have hbuf : m ⊨ vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      ((a ↦₆₄ gk.1.cipher.cap) ∗ ((a + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
        vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        ((a + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((a + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
        vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
        ((a + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((a + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
        vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
        ((a + 72#64) ↦₆₄ gk.1.seed.cap) ∗ ((a + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
        memRegion (a + 100#64) 4 ∗ R) := by
    convert hm.2 using 1; ac_rfl
  unfold vecU8Buf at hbuf
  rw [sepConj_assoc, satisfies_pure_sepConj] at hbuf
  have h1 := hbuf.1.1
  have h2 := hbuf.1.2.1
  omega

private theorem seed_len_beq_zero_false {bs : List (BitVec 8)}
    (hne : bs ≠ []) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
  rw [beq_eq_false_iff_ne]
  intro heq
  have h := congrArg BitVec.toNat heq
  change bs.length % 2 ^ 64 = 0 at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem bv_uint32Field_1_ne_zero {v : BitVec 32} (h : (v == 0#32) = false) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 v)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 v).length := by
  have hv : v ≠ 0 := by rwa [beq_eq_false_iff_ne] at h
  have hkey : (encodeKey 1 .varint).length = 1 := rfl
  simp only [uint32Field, hv, ↓reduceIte, List.length_append, hkey,
    ← BitVec.ofNat_add, Nat.add_comm]

private theorem uint32Field_1_length_le (v : BitVec 32) :
    (uint32Field 1 v).length ≤ 11 := by
  unfold uint32Field
  split
  · simp
  · have hkey : (encodeKey 1 .varint).length = 1 := rfl
    have hb := (encodeVarint_length_bounds (v.setWidth 64)).2
    simp only [List.length_append, hkey]
    omega

private theorem bv_bytesField_5_ne_nil {bs : List (BitVec 8)} (hne : bs ≠ []) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (encodeVarint (BitVec.ofNat 64 bs.length)).length + 1#64 =
      BitVec.ofNat 64 (bytesField 5 bs).length := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey, ← BitVec.ofNat_add]
  congr 1
  omega

private theorem bytesField_5_length_lt {bs : List (BitVec 8)} (hne : bs ≠ []) :
    (bytesField 5 bs).length ≤ bs.length + 11 := by
  have hkey : (encodeKey 5 .lengthDelimited).length = 1 := rfl
  have hb := (encodeVarint_length_bounds (BitVec.ofNat 64 bs.length)).2
  simp only [bytesField, hne, ↓reduceIte, lenField, List.length_append, hkey]
  omega

private theorem encMessageKey_length_eq (mk : MessageKeyGenerator) :
    (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
  simp only [encMessageKey, List.length_append]

private theorem stackAt_msgKeyLen_eq (sp : BitVec 64) :
    stackAt sp msgKeyLenStack = ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) :=
  stackAt_encodedLen_eq sp

@[local simp, local arm64_norm]
private theorem ule_self_64 (x : BitVec 64) : BitVec.ule x x = true := by
  simp [BitVec.ule]

@[local simp, local arm64_norm]
private theorem ult_self_64 (x : BitVec 64) : BitVec.ult x x = false := by
  simp [BitVec.ult]

/-! ## Step Lemmas -/

private theorem step_mkLen_f1 (b : BitVec 64)
    (ext : String → Option (State → State))
    (a sp v16 v8 : BitVec 64) (mk : MessageKeyGenerator)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (msgKeyCells a mk ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName + 120#64 →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 mk.counter).length →
      sm.readReg64 .x9 = 0#64 →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((msgKeyCells a mk ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  mkLen_fetches_range b (Rust.withPanics ext) 0 52
  mkLen_fetches_range b (Rust.withPanics ext) 224 252
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName = entry
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  by_cases hcnt : (mk.counter == 0#32) = true
  · have hcnt0 : mk.counter = 0#32 := by rwa [beq_iff_eq] at hcnt
    rw [hcells]
    apply SepWPp.of_sepWP (mid := entry + bv% (120))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hcells]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [uint32Field]) (by simp_all)
      (by simp_all [EncLenCalleeSaved])
  · have hcnt_f : (mk.counter == 0#32) = false := Bool.eq_false_iff.mpr hcnt
    have henc := bv_uint32Field_1_ne_zero hcnt_f
    rw [hcells]
    apply SepWPp.of_sepWP (mid := entry + bv% (120))
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← hcells]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [EncLenCalleeSaved])

private theorem step_mkLen_f2 (b : BitVec 64)
    (ext : String → Option (State → State))
    (a sp : BitVec 64) (mk : MessageKeyGenerator) (s1 : Nat)
    (hseed_ne : mk.seed ≠ [])
    (hseed_lt : mk.seed.length < 2 ^ 63)
    (hfit : s1 + (bytesField 5 mk.seed).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName + 120#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (msgKeyCells a mk ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s1 + (bytesField 5 mk.seed).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q Qp := by
  mkLen_fetches_range b (Rust.withPanics ext) 120 136
  mkLen_fetches_range b (Rust.withPanics ext) 164 224
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr msgKeyLenName = entry
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  have hseed_beq := seed_len_beq_zero_false hseed_ne hseed_lt
  have henc := bv_bytesField_5_ne_nil hseed_ne
  have hcs_ovf := ult_ofNat_add_of_lt hfit
  have hule_ovf := ule_ofNat_add_of_lt hfit
  have hadd := bv_add_ofNat_comm s1 (bytesField 5 mk.seed).length
  subst hP
  have hcells : msgKeyCells a mk =
      ((a + 16#64) ↦₆₄ 0#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 88#64) ↦₆₄ BitVec.ofNat 64 mk.seed.length) ∗ ((a + 96#64) ↦₃₂ mk.counter) := rfl
  rw [hcells]
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rw [← hcells]
  apply SepWPp.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by encodedLen_cc_close)

/-! ## Main Theorem -/

/-- `MessageKey::encoded_len` meets `msgKeyLenSpec`. -/
theorem msgKeyLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) :
    OkAtExt b ext msgKeyLenName (msgKeyLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, gk⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, hx0, hpre⟩
  have hrest_sat : s0.mem ⊨ msgKeyRest A gk a ∗
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre using 1; ac_rfl
  obtain ⟨hseed_ne, hseed_lt⟩ := msgKeyRest_seed_bounds hrest_sat
  let FRest : SepProp := msgKeyRest A gk a ∗ R
  have hmem0 : s0.mem ⊨
      (msgKeyCells a gk.2 ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest := by
    dsimp [FRest]; convert hpre using 1; ac_rfl
  refine ⟨(msgKeyCells a gk.2 ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ FRest, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_mkLen_f1 (F := FRest) b ext a s0.sp v16 v8 gk.2
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1
  have h1 := uint32Field_1_length_le gk.2.counter
  have h5 := bytesField_5_length_lt hseed_ne
  refine step_mkLen_f2 (F := FRest) b ext a s0.sp gk.2
    (uint32Field 1 gk.2.counter).length
    hseed_ne hseed_lt (by omega)
    hpc1 hrun1 hsp1 halign hx0_1 hx8_1 hx9_1 hcs1 rfl ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  have htr_all : sf.trace = s0.trace := by rw [htrf, htr1]
  rw [← encMessageKey_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [msgKeyLenSpec, messageKeyAt_eq_cells_sep_rest, stackAt_msgKeyLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hx0_f, htr_all⟩, ?_⟩
  dsimp [FRest] at hm_f
  convert hm_f using 1
  ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
