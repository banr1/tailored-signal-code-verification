/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

/-!
# Prost Field-Merging Loop Combinators (`Proto.mergeFieldsLoop`)

Compositional round-trip combinators for `Proto.mergeFieldsLoop`:

* `LoopsTo mf d m bs r`: `mergeFieldsLoop` over `bs` starting from `m` returns `r` for every
  `fuel ≥ bs.length` and recursion budget `depth ≥ d` (with `d ≤ RECURSION_LIMIT = 100`).
* `LoopsTo.append`: composes `LoopsTo` across concatenated field encodings for prefix-stable `mf`.
* Per-field step lemmas for `uint32`, `uint64`, `int32`, `bool`, `bytes`, repeated `bytes`,
  sub-messages (optional and `oneof` arms), and repeated sub-messages, plus `decodeTop_of_loopsTo`
  to close top-level `T.decode (T.encodeRaw m) = .ok m` goals.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
open CryptoVerification.SpqrV1.Prost.MessageMerge (ProtoPrefixStep)
/-- Field-merger callback signature taken by `Proto.mergeFieldsLoop`. -/
abbrev MergeFieldFn (M : Type) :=
  M → BitVec 32 → WireType → Bytes → Nat → Except DecodeErr (M × Bytes)

/-- Prefix-stability predicate on a per-type `mergeField` function. -/
def PrefixOk {M : Type} (mf : MergeFieldFn M) : Prop :=
  ∀ m tag wt depth, ProtoPrefixStep (fun bs => mf m tag wt bs depth)

/-- `Proto.mergeFieldsLoop` over `bs` from `m` returns `r` for all `fuel ≥ bs.length` and
recursion budget `depth ≥ d`. -/
def LoopsTo {M : Type} (mf : MergeFieldFn M) (d : Nat) (m : M) (bs : Bytes) (r : M) : Prop :=
  ∀ fuel depth, bs.length ≤ fuel → d ≤ depth → Proto.mergeFieldsLoop mf fuel m bs depth = .ok r

variable {M N : Type}

/-! ## Private wire and loop helpers -/

private theorem encodeVarintAux_ne_nil : ∀ (fuel : Nat) (v : BitVec 64),
    Proto.encodeVarintAux fuel v ≠ []
  | 0, _ => by simp [Proto.encodeVarintAux]
  | fuel + 1, v => by
    simp only [Proto.encodeVarintAux]
    split <;> simp

private theorem encodeKey_ne_nil (tag : BitVec 32) (wt : WireType) :
    Proto.encodeKey tag wt ≠ [] :=
  encodeVarintAux_ne_nil 10 _

private theorem decodeVarintAux_ok_append :
    ∀ (fuel idx : Nat) (acc : BitVec 64) (s a : Bytes) (v : BitVec 64) (r' : Bytes),
      Proto.decodeVarintAux fuel idx acc s = .ok (v, r') →
      r'.length < s.length ∧ Proto.decodeVarintAux fuel idx acc (s ++ a) = .ok (v, r' ++ a)
  | 0, _, _, _, _, _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, [], _, _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, b :: rest, a, v, r', h => by
    simp only [Proto.decodeVarintAux, List.cons_append] at h ⊢
    by_cases h9 : (idx == 9) = true
    · simp only [h9, ↓reduceIte] at h ⊢
      by_cases hb : b ≥ 0x02#8
      · simp [hb] at h
      · simp only [hb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        rcases h with ⟨rfl, rfl⟩
        exact ⟨Nat.lt_succ_self _, rfl, rfl⟩
    · simp only [Bool.not_eq_true] at h9
      simp only [h9, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hb : b < 0x80#8
      · simp only [hb, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        rcases h with ⟨rfl, rfl⟩
        exact ⟨Nat.lt_succ_self _, rfl, rfl⟩
      · simp only [hb, ↓reduceIte] at h ⊢
        obtain ⟨hlen, happ⟩ := decodeVarintAux_ok_append fuel (idx + 1) _ rest a v r' h
        exact ⟨Nat.lt_succ_of_lt hlen, happ⟩

private theorem decodeKey_ok_append (s a : Bytes) (tw : BitVec 32 × WireType) (r' : Bytes)
    (h : Proto.decodeKey s = .ok (tw, r')) :
    r'.length < s.length ∧ Proto.decodeKey (s ++ a) = .ok (tw, r' ++ a) := by
  unfold Proto.decodeKey Proto.decodeVarint at h ⊢
  cases hdv : Proto.decodeVarintAux 10 0 0#64 s with
  | error e => simp [hdv, Bind.bind, Except.bind] at h
  | ok p =>
    rcases p with ⟨key, rest⟩
    obtain ⟨hlen, happ⟩ := decodeVarintAux_ok_append 10 0 0#64 s a key rest hdv
    rw [hdv] at h
    rw [happ]
    simp only [Bind.bind, Except.bind] at h ⊢
    change (if 4294967295#64 < key then _ else _) = _ at h
    change _ ∧ (if 4294967295#64 < key then _ else _) = _
    by_cases hk : 4294967295#64 < key
    · simp [hk] at h
    · simp only [hk, ↓reduceIte] at h ⊢
      cases hwt : Proto.WireType.ofU64? (key &&& 0x7#64) with
      | none => simp [hwt] at h
      | some w =>
        simp only [hwt] at h ⊢
        by_cases htag : (key >>> 3).truncate 32 < Proto.MIN_TAG
        · simp [htag] at h
        · simp only [htag, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          rcases h with ⟨rfl, rfl⟩
          exact ⟨hlen, rfl, rfl⟩

private theorem mergeFieldsLoop_fuel {mf : MergeFieldFn M} (hmf : PrefixOk mf) (depth : Nat) :
    ∀ (n : Nat) (bs : Bytes), bs.length ≤ n →
      ∀ (f₁ f₂ : Nat) (m : M), bs.length ≤ f₁ → bs.length ≤ f₂ →
        Proto.mergeFieldsLoop mf f₁ m bs depth = Proto.mergeFieldsLoop mf f₂ m bs depth
  | 0, bs, hn, f₁, f₂, m, _, _ => by
    cases bs with
    | nil => cases f₁ <;> cases f₂ <;> rfl
    | cons _ _ => simp at hn
  | n + 1, [], _, f₁, f₂, m, _, _ => by
    cases f₁ <;> cases f₂ <;> rfl
  | n + 1, b :: tl, hn, f₁, f₂, m, hf₁, hf₂ => by
    cases f₁ with
    | zero => simp at hf₁
    | succ f₁' =>
      cases f₂ with
      | zero => simp at hf₂
      | succ f₂' =>
        simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind]
        cases hdk : Proto.decodeKey (b :: tl) with
        | error e => rfl
        | ok p =>
          rcases p with ⟨⟨tag, wt⟩, rest⟩
          obtain ⟨hrest_lt, _⟩ := decodeKey_ok_append (b :: tl) [] (tag, wt) rest hdk
          simp only []
          cases hm : mf m tag wt rest depth with
          | error e => rfl
          | ok p' =>
            rcases p' with ⟨m', rest'⟩
            obtain ⟨hrest'_le, _⟩ := (hmf m tag wt depth).ok_append rest [] m' rest' hm
            simp only [List.length_cons] at hn hf₁ hf₂ hrest_lt
            exact mergeFieldsLoop_fuel hmf depth n rest' (by omega) f₁' f₂' m' (by omega) (by omega)

private theorem loopsAt_append {mf : MergeFieldFn M} (hmf : PrefixOk mf) (depth : Nat) :
    ∀ (n : Nat) (bs₁ bs₂ : Bytes) (m m₁ r : M),
      bs₁.length ≤ n →
      (∀ fuel, bs₁.length ≤ fuel → Proto.mergeFieldsLoop mf fuel m bs₁ depth = .ok m₁) →
      (∀ fuel, bs₂.length ≤ fuel → Proto.mergeFieldsLoop mf fuel m₁ bs₂ depth = .ok r) →
      ∀ fuel, (bs₁ ++ bs₂).length ≤ fuel →
        Proto.mergeFieldsLoop mf fuel m (bs₁ ++ bs₂) depth = .ok r
  | 0, bs₁, bs₂, m, m₁, r, hn, h₁, h₂, fuel, hfuel => by
    cases bs₁ with
    | nil =>
      have hm : m = m₁ := by simpa [Proto.mergeFieldsLoop] using h₁ 0 (Nat.le_refl 0)
      subst hm
      exact h₂ fuel (by simpa using hfuel)
    | cons _ _ => simp at hn
  | n + 1, [], bs₂, m, m₁, r, _, h₁, h₂, fuel, hfuel => by
    have hm : m = m₁ := by simpa [Proto.mergeFieldsLoop] using h₁ 0 (Nat.le_refl 0)
    subst hm
    exact h₂ fuel (by simpa using hfuel)
  | n + 1, b :: tl, bs₂, m, m₁, r, hn, h₁, h₂, fuel, hfuel => by
    have hstep := h₁ (tl.length + 1) (Nat.le_refl _)
    simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind] at hstep
    cases hdk : Proto.decodeKey (b :: tl) with
    | error e => simp [hdk] at hstep
    | ok p =>
      rcases p with ⟨⟨tag, wt⟩, rest⟩
      rw [hdk] at hstep
      simp only [] at hstep
      obtain ⟨hrest_lt, hdk_app⟩ := decodeKey_ok_append (b :: tl) bs₂ (tag, wt) rest hdk
      cases hm : mf m tag wt rest depth with
      | error e => simp [hm] at hstep
      | ok p' =>
        rcases p' with ⟨m', rest'⟩
        rw [hm] at hstep
        simp only [] at hstep
        obtain ⟨hrest'_le, hm_app⟩ := (hmf m tag wt depth).ok_append rest bs₂ m' rest' hm
        simp only [List.length_cons] at hn hrest_lt
        have h₁' : ∀ f, rest'.length ≤ f → Proto.mergeFieldsLoop mf f m' rest' depth = .ok m₁ := by
          intro f hf
          rw [mergeFieldsLoop_fuel hmf depth tl.length rest' (by omega) f tl.length m' hf (by omega)]
          exact hstep
        have h_ih := loopsAt_append hmf depth n rest' bs₂ m' m₁ r (by omega) h₁' h₂
        cases fuel with
        | zero =>
          simp only [List.cons_append, List.length_cons] at hfuel
          omega
        | succ fuel' =>
          simp only [List.cons_append] at hdk_app hfuel ⊢
          simp only [Proto.mergeFieldsLoop, Bind.bind, Except.bind, hdk_app, hm_app]
          apply h_ih
          simp only [List.length_append, List.length_cons] at hfuel ⊢
          omega

private theorem bitvec64_varint_small (w : BitVec 64) (hw : w < 0x80#64) :
    ((w.truncate 8 &&& 0x7f#8).zeroExtend 64) = w := by
  bv_robdd

private theorem bitvec64_varint_cont_not_lt (w : BitVec 64) :
    ¬ ((w.truncate 8 ||| 0x80#8) < 0x80#8) := by
  bv_robdd

private theorem bitvec64_varint_cont_low7 (w : BitVec 64) :
    (((w.truncate 8 ||| 0x80#8) &&& 0x7f#8).zeroExtend 64) = (w &&& 0x7f#64) := by
  bv_slice

private theorem bitvec64_varint_reconstruct (w : BitVec 64) :
    (w &&& 0x7f#64) ||| ((w >>> 7) <<< 7) = w := by
  bv_slice

private theorem bitvec64_shl_or_combine (acc w : BitVec 64) (idx : Nat) :
    (acc ||| ((w &&& 0x7f#64) <<< (idx * 7))) ||| ((w >>> 7) <<< ((idx + 1) * 7)) =
      acc ||| (w <<< (idx * 7)) := by
  have hadd : (idx + 1) * 7 = 7 + idx * 7 := by omega
  rw [hadd, BitVec.shiftLeft_add, BitVec.or_assoc, ← BitVec.shiftLeft_or_distrib,
    bitvec64_varint_reconstruct]

private theorem decodeVarintAux_encodeVarintAux :
    ∀ (k : Nat), 1 ≤ k → ∀ (idx : Nat), idx + k = 10 →
      ∀ (acc w : BitVec 64) (rest : Bytes),
        w.toNat < 2 ^ (7 * (k - 1) + 1) →
        Proto.decodeVarintAux k idx acc (Proto.encodeVarintAux k w ++ rest) =
          .ok (acc ||| (w <<< (idx * 7)), rest)
  | 0, hk, _, _, _, _, _, _ => by omega
  | 1, _, idx, hidx, acc, w, rest, hw => by
    have hidx9 : idx = 9 := by omega
    subst hidx9
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_add, Nat.pow_one] at hw
    have hw128 : w < 0x80#64 := by simp [BitVec.lt_def]; omega
    have hb2 : ¬ (w.truncate 8 ≥ 0x02#8) := by
      simp [BitVec.le_def, BitVec.toNat_setWidth]
      omega
    simp only [Proto.encodeVarintAux, hw128, ↓reduceIte, List.singleton_append,
      Proto.decodeVarintAux, beq_self_eq_true, hb2, bitvec64_varint_small w hw128]
  | k' + 2, _, idx, hidx, acc, w, rest, hw => by
    have hidx_ne : (idx == 9) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    by_cases hw128 : w < 0x80#64
    · have hb128 : w.truncate 8 < 0x80#8 := by
        have hw_nat : w.toNat < 128 := by simpa [BitVec.lt_def] using hw128
        simp [BitVec.lt_def, BitVec.toNat_setWidth]
        omega
      have henc : Proto.encodeVarintAux (k' + 2) w = [w.truncate 8] := by
        rw [Proto.encodeVarintAux]
        simp [hw128]
      rw [henc, List.singleton_append]
      simp only [Proto.decodeVarintAux, hidx_ne, Bool.false_eq_true, ↓reduceIte, hb128,
        bitvec64_varint_small w hw128]
    · have henc : Proto.encodeVarintAux (k' + 2) w =
          (w.truncate 8 ||| 0x80#8) :: Proto.encodeVarintAux (k' + 1) (w >>> 7) := by
        rw [Proto.encodeVarintAux]
        simp [hw128]
      rw [henc, List.cons_append]
      have hdec : Proto.decodeVarintAux (k' + 2) idx acc
          ((w.truncate 8 ||| 0x80#8) :: (Proto.encodeVarintAux (k' + 1) (w >>> 7) ++ rest)) =
          Proto.decodeVarintAux (k' + 1) (idx + 1)
            (acc ||| ((w &&& 0x7f#64) <<< (idx * 7)))
            (Proto.encodeVarintAux (k' + 1) (w >>> 7) ++ rest) := by
        rw [Proto.decodeVarintAux]
        simp only [hidx_ne, Bool.false_eq_true, ↓reduceIte,
          bitvec64_varint_cont_not_lt w, bitvec64_varint_cont_low7 w]
      rw [hdec]
      have hw_shr : (w >>> 7).toNat < 2 ^ (7 * ((k' + 1) - 1) + 1) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have hpow : 2 ^ (7 * (k' + 2 - 1) + 1) = 2 ^ 7 * 2 ^ (7 * ((k' + 1) - 1) + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
        rw [hpow] at hw
        omega
      rw [decodeVarintAux_encodeVarintAux (k' + 1) (by omega) (idx + 1) (by omega) _ (w >>> 7) rest hw_shr]
      rw [bitvec64_shl_or_combine]

private theorem decodeVarint_encodeVarint (v : BitVec 64) (rest : Bytes) :
    Proto.decodeVarint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  unfold Proto.decodeVarint Proto.encodeVarint
  have h := decodeVarintAux_encodeVarintAux 10 (by omega) 0 rfl 0#64 v rest v.isLt
  simpa using h

private theorem bitvec32_zext64_not_gt_u32max (x : BitVec 32) :
    ¬ (x.zeroExtend 64 > BitVec.ofNat 64 (2 ^ 32 - 1)) := by
  bv_robdd

private theorem bitvec_key_low3 (t c : BitVec 32) :
    ((((t <<< 3) ||| c).zeroExtend 64) &&& 0x7#64) = (c.zeroExtend 64 &&& 0x7#64) := by
  bv_slice

private theorem bitvec_key_shr3 (t c : BitVec 32) :
    (((((t <<< 3) ||| c).zeroExtend 64) >>> 3).truncate 32) = ((t <<< 3) >>> 3) ||| (c >>> 3) := by
  bv_slice

private theorem bitvec_tag_shl3_shr3 (tag : BitVec 32) (h : tag < BitVec.ofNat 32 (2 ^ 29)) :
    (tag <<< 3) >>> 3 = tag := by
  bv_robdd

private theorem decodeKey_encodeKey (tag : BitVec 32) (wt : WireType) (rest : Bytes)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  unfold Proto.decodeKey Proto.encodeKey
  rw [decodeVarint_encodeVarint]
  have hnot_gt : ¬ ((((tag <<< 3) ||| wt.toU32).zeroExtend 64) > BitVec.ofNat 64 (2 ^ 32 - 1)) :=
    bitvec32_zext64_not_gt_u32max _
  simp only [Bind.bind, Except.bind]
  change (if (((tag <<< 3) ||| wt.toU32).zeroExtend 64) > BitVec.ofNat 64 (2 ^ 32 - 1) then _ else _) = _
  simp only [hnot_gt, ↓reduceIte, bitvec_key_low3, bitvec_key_shr3]
  have hwt : Proto.WireType.ofU64? (wt.toU32.zeroExtend 64 &&& 0x7#64) = some wt := by
    cases wt <;> rfl
  have hwt_shr : wt.toU32 >>> 3 = 0#32 := by
    cases wt <;> rfl
  have htag_lt : tag < BitVec.ofNat 32 (2 ^ 29) := by
    simp [BitVec.lt_def]
    exact h2
  have hmin : ¬ (tag < Proto.MIN_TAG) := by
    simp [Proto.MIN_TAG, BitVec.lt_def]
    omega
  rw [hwt]
  simp only [hwt_shr, BitVec.or_zero, bitvec_tag_shl3_shr3 tag htag_lt, hmin, ↓reduceIte]

private theorem takeExact_append : ∀ (v rest : Bytes),
    Proto.takeExact v.length (v ++ rest) = .ok (v, rest)
  | [], rest => rfl
  | b :: vs, rest => by
    simp [Proto.takeExact, takeExact_append vs rest, Bind.bind, Except.bind]

private theorem mergeBytes_encode_append (v rest : Bytes) (hlen : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  unfold Proto.mergeBytes Proto.checkWireType
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [decodeVarint_encodeVarint]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  exact takeExact_append v rest

/-! ## Loop combinators and field-step lemmas -/

theorem loopsTo_nil (mf : MergeFieldFn M) (d : Nat) (m : M) : LoopsTo mf d m [] m := by
  intro fuel depth _ _
  cases fuel <;> rfl

theorem LoopsTo.mono {mf : MergeFieldFn M} {d d' : Nat} {m r : M} {bs : Bytes}
    (h : LoopsTo mf d m bs r) (hd : d ≤ d') : LoopsTo mf d' m bs r := by
  intro fuel depth hfuel hdepth
  exact h fuel depth hfuel (Nat.le_trans hd hdepth)

theorem LoopsTo.congr_bytes {mf : MergeFieldFn M} {d : Nat} {m r : M} {bs bs' : Bytes}
    (h : LoopsTo mf d m bs r) (he : bs = bs') : LoopsTo mf d m bs' r := by
  subst he; exact h

theorem LoopsTo.congr_res {mf : MergeFieldFn M} {d : Nat} {m r r' : M} {bs : Bytes}
    (h : LoopsTo mf d m bs r) (he : r = r') : LoopsTo mf d m bs r' := by
  subst he; exact h

/-- Composes `LoopsTo` across concatenated field byte sequences for a prefix-stable `mf`. -/
theorem LoopsTo.append {mf : MergeFieldFn M} (hmf : PrefixOk mf) {d : Nat} {m m₁ r : M}
    {bs₁ bs₂ : Bytes} (h₁ : LoopsTo mf d m bs₁ m₁) (h₂ : LoopsTo mf d m₁ bs₂ r) :
    LoopsTo mf d m (bs₁ ++ bs₂) r := by
  intro fuel depth hfuel hd
  exact loopsAt_append hmf depth bs₁.length bs₁ bs₂ m m₁ r (Nat.le_refl _)
    (fun f hf => h₁ f depth hf hd) (fun f hf => h₂ f depth hf hd) fuel hfuel

/-- Single-field `LoopsTo` step when `mf` consumes the entire payload after `(tag, wt)`. -/
theorem loopsTo_field (mf : MergeFieldFn M) (d : Nat) (m m' : M) (tag : BitVec 32) (wt : WireType)
    (payload : Bytes) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29)
    (hmf : ∀ depth, d ≤ depth → mf m tag wt payload depth = .ok (m', [])) :
    LoopsTo mf d m (Proto.encodeKey tag wt ++ payload) m' := by
  intro fuel depth hfuel hd
  have hne : Proto.encodeKey tag wt ≠ [] := encodeKey_ne_nil tag wt
  cases hk : Proto.encodeKey tag wt with
  | nil => exact absurd hk hne
  | cons b krest =>
    cases fuel with
    | zero =>
      simp [hk] at hfuel
    | succ fuel' =>
      have hdk := decodeKey_encodeKey tag wt payload h1 h2
      rw [hk] at hdk
      simp only [List.cons_append, Proto.mergeFieldsLoop, Bind.bind, Except.bind] at hdk ⊢
      rw [hdk]
      simp only [hmf depth hd]
      cases fuel' <;> rfl

theorem loopsTo_uint32 (mf : MergeFieldFn M) (d : Nat) (m : M) (tag v : BitVec 32)
    (set : BitVec 32 → M) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hzero : set 0#32 = m)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeUint32 .varint bs; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeUint32Field tag v) (set v) := by
  unfold Proto.encodeUint32Field
  by_cases hv : v == 0#32
  · simp only [hv, ↓reduceIte]
    have hv0 : v = 0#32 := by simpa using hv
    rw [hv0, hzero]
    exact loopsTo_nil mf d m
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    apply loopsTo_field mf d m (set v) tag .varint _ h1 h2
    intro depth hd
    rw [hmf depth _ hd]
    unfold Proto.mergeUint32 Proto.checkWireType
    have hdv := decodeVarint_encodeVarint (v.zeroExtend 64) []
    rw [List.append_nil] at hdv
    have htr : (v.zeroExtend 64).truncate 32 = v := by bv_slice
    simp [Bind.bind, Except.bind, hdv, htr]

theorem loopsTo_uint64 (mf : MergeFieldFn M) (d : Nat) (m : M) (tag : BitVec 32) (v : BitVec 64)
    (set : BitVec 64 → M) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hzero : set 0#64 = m)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeUint64 .varint bs; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeUint64Field tag v) (set v) := by
  unfold Proto.encodeUint64Field
  by_cases hv : v == 0#64
  · simp only [hv, ↓reduceIte]
    have hv0 : v = 0#64 := by simpa using hv
    rw [hv0, hzero]
    exact loopsTo_nil mf d m
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    apply loopsTo_field mf d m (set v) tag .varint _ h1 h2
    intro depth hd
    rw [hmf depth _ hd]
    unfold Proto.mergeUint64 Proto.checkWireType
    have hdv := decodeVarint_encodeVarint v []
    rw [List.append_nil] at hdv
    simp [Bind.bind, Except.bind, hdv]

theorem loopsTo_int32 (mf : MergeFieldFn M) (d : Nat) (m : M) (tag v : BitVec 32)
    (set : BitVec 32 → M) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hzero : set 0#32 = m)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeInt32 .varint bs; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeInt32Field tag v) (set v) := by
  unfold Proto.encodeInt32Field
  by_cases hv : v == 0#32
  · simp only [hv, ↓reduceIte]
    have hv0 : v = 0#32 := by simpa using hv
    rw [hv0, hzero]
    exact loopsTo_nil mf d m
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    apply loopsTo_field mf d m (set v) tag .varint _ h1 h2
    intro depth hd
    rw [hmf depth _ hd]
    unfold Proto.mergeInt32 Proto.checkWireType
    have hdv := decodeVarint_encodeVarint (v.signExtend 64) []
    rw [List.append_nil] at hdv
    have htr : (v.signExtend 64).truncate 32 = v := by bv_slice
    simp [Bind.bind, Except.bind, hdv, htr]

theorem loopsTo_bool (mf : MergeFieldFn M) (d : Nat) (m : M) (tag : BitVec 32) (v : Bool)
    (set : Bool → M) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hfalse : set false = m)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeBool .varint bs; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeBoolField tag v) (set v) := by
  cases v with
  | false =>
    simp only [Proto.encodeBoolField, Bool.false_eq_true, ↓reduceIte, hfalse]
    exact loopsTo_nil mf d m
  | true =>
    simp only [Proto.encodeBoolField, ↓reduceIte]
    apply loopsTo_field mf d m (set true) tag .varint [1#8] h1 h2
    intro depth hd
    rw [hmf depth _ hd]
    have hmb : Proto.mergeBool .varint [1#8] = .ok (true, []) := rfl
    simp [Bind.bind, Except.bind, hmb]

theorem loopsTo_bytes (mf : MergeFieldFn M) (d : Nat) (m : M) (tag : BitVec 32) (v : Bytes)
    (set : Bytes → M) (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hempty : set [] = m)
    (hlen : v.length < 2 ^ 64)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeBytes .lengthDelimited bs; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeBytesField tag v) (set v) := by
  unfold Proto.encodeBytesField
  by_cases hv : v.isEmpty
  · simp only [hv, ↓reduceIte]
    have hv0 : v = [] := List.isEmpty_iff.mp hv
    rw [hv0, hempty]
    exact loopsTo_nil mf d m
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, Proto.encodeBytesUncond, List.append_assoc]
    apply loopsTo_field mf d m (set v) tag .lengthDelimited _ h1 h2
    intro depth hd
    rw [hmf depth _ hd]
    have hmb := mergeBytes_encode_append v [] hlen
    rw [List.append_nil] at hmb
    simp [Bind.bind, Except.bind, hmb]

/-- `LoopsTo` step for `encodeRepeatedBytes`, appending `vs` via the field lens `get`/`set`. -/
theorem loopsTo_repeatedBytes (mf : MergeFieldFn M) (hpre : PrefixOk mf) (d : Nat) (m : M)
    (tag : BitVec 32) (vs : List Bytes) (get : M → List Bytes) (set : M → List Bytes → M)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hlen : ∀ v ∈ vs, v.length < 2 ^ 64)
    (hgs : ∀ m' l, get (set m' l) = l) (hss : ∀ m' l l', set (set m' l) l' = set m' l')
    (hsg : ∀ m', set m' (get m') = m')
    (hmf : ∀ m' depth bs, d ≤ depth → mf m' tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeRepeatedBytes .lengthDelimited (get m') bs; .ok (set m' x, bs'))) :
    LoopsTo mf d m (Proto.encodeRepeatedBytes tag vs) (set m (get m ++ vs)) := by
  induction vs generalizing m with
  | nil =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_nil, List.append_nil, hsg]
    exact loopsTo_nil mf d m
  | cons v vs' ih =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_cons]
    have hv_len : v.length < 2 ^ 64 := hlen v (List.mem_cons_self ..)
    have hvs'_len : ∀ w ∈ vs', w.length < 2 ^ 64 := fun w hw => hlen w (List.mem_cons_of_mem _ hw)
    have hone : LoopsTo mf d m (Proto.encodeBytesUncond tag v) (set m (get m ++ [v])) := by
      unfold Proto.encodeBytesUncond
      rw [List.append_assoc]
      apply loopsTo_field mf d m (set m (get m ++ [v])) tag .lengthDelimited _ h1 h2
      intro depth hd
      rw [hmf m depth _ hd]
      unfold Proto.mergeRepeatedBytes
      have hmb := mergeBytes_encode_append v [] hv_len
      rw [List.append_nil] at hmb
      simp [Bind.bind, Except.bind, hmb]
    have hrest : LoopsTo mf d (set m (get m ++ [v]))
        (Proto.encodeRepeatedBytes tag vs')
        (set (set m (get m ++ [v])) (get (set m (get m ++ [v])) ++ vs')) :=
      ih (set m (get m ++ [v])) hvs'_len
    rw [hgs, hss, List.append_assoc] at hrest
    exact LoopsTo.append hpre hone hrest

/-- Length-delimited sub-message round-trip through `mergeMessage`, consuming one unit of
recursion depth. -/
theorem mergeMessage_encode (mfN : MergeFieldFn N) (dN : Nat) (encodeRaw : N → Bytes) (n₀ n : N)
    (depth : Nat) (rest : Bytes) (hsub : LoopsTo mfN dN n₀ (encodeRaw n) n)
    (hlen : (encodeRaw n).length < 2 ^ 64) (hd : dN < depth) :
    Proto.mergeMessage mfN .lengthDelimited n₀
        (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw n).length) ++ (encodeRaw n ++ rest)) depth =
      .ok (n, rest) := by
  cases depth with
  | zero => omega
  | succ depth' =>
    unfold Proto.mergeMessage Proto.checkWireType
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
    rw [decodeVarint_encodeVarint]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen, takeExact_append]
    rw [hsub (encodeRaw n).length depth' (Nat.le_refl _) (by omega)]

/-- `LoopsTo` step for `encodeMessage`, covering both optional fields and `oneof` arms. -/
theorem loopsTo_message (mf : MergeFieldFn M) (d : Nat) (m : M) (tag : BitVec 32)
    (mfN : MergeFieldFn N) (dN : Nat) (encodeRaw : N → Bytes) (n₀ n : N) (set : N → M)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hdd : dN < d)
    (hsub : LoopsTo mfN dN n₀ (encodeRaw n) n) (hlen : (encodeRaw n).length < 2 ^ 64)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeMessage mfN .lengthDelimited n₀ bs depth; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeMessage encodeRaw tag n) (set n) := by
  unfold Proto.encodeMessage
  rw [List.append_assoc]
  apply loopsTo_field mf d m (set n) tag .lengthDelimited _ h1 h2
  intro depth hd
  rw [hmf depth _ hd]
  have hmm := mergeMessage_encode mfN dN encodeRaw n₀ n depth [] hsub hlen (by omega)
  rw [List.append_nil] at hmm
  simp [Bind.bind, Except.bind, hmm]

theorem loopsTo_optMessage [Inhabited N] (mf : MergeFieldFn M) (d : Nat) (m : M) (tag : BitVec 32)
    (mfN : MergeFieldFn N) (dN : Nat) (encodeRaw : N → Bytes) (o : Option N) (set : Option N → M)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hdd : dN < d) (hnone : set none = m)
    (hsub : ∀ n, o = some n → LoopsTo mfN dN default (encodeRaw n) n ∧ (encodeRaw n).length < 2 ^ 64)
    (hmf : ∀ depth bs, d ≤ depth → mf m tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeOptMessage mfN .lengthDelimited none bs depth; .ok (set x, bs'))) :
    LoopsTo mf d m (Proto.encodeOptMessage encodeRaw tag o) (set o) := by
  cases o with
  | none =>
    simp only [Proto.encodeOptMessage, hnone]
    exact loopsTo_nil mf d m
  | some n =>
    simp only [Proto.encodeOptMessage]
    obtain ⟨hloop, hlen⟩ := hsub n rfl
    apply loopsTo_message mf d m tag mfN dN encodeRaw default n (fun x => set (some x)) h1 h2 hdd hloop hlen
    intro depth bs hd
    rw [hmf depth bs hd]
    unfold Proto.mergeOptMessage
    simp only [Option.getD_none, Bind.bind, Except.bind]
    cases Proto.mergeMessage mfN .lengthDelimited default bs depth <;> rfl

/-- `LoopsTo` step for `encodeRepeatedMessage`, appending decoded sub-messages via `get`/`set`. -/
theorem loopsTo_repeatedMessage [Inhabited N] (mf : MergeFieldFn M) (hpre : PrefixOk mf) (d : Nat)
    (m : M) (tag : BitVec 32) (mfN : MergeFieldFn N) (dN : Nat) (encodeRaw : N → Bytes)
    (ns : List N) (get : M → List N) (set : M → List N → M)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) (hdd : dN < d)
    (hsub : ∀ n ∈ ns, LoopsTo mfN dN default (encodeRaw n) n ∧ (encodeRaw n).length < 2 ^ 64)
    (hgs : ∀ m' l, get (set m' l) = l) (hss : ∀ m' l l', set (set m' l) l' = set m' l')
    (hsg : ∀ m', set m' (get m') = m')
    (hmf : ∀ m' depth bs, d ≤ depth → mf m' tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeRepeatedMessage mfN .lengthDelimited (get m') bs depth
          .ok (set m' x, bs'))) :
    LoopsTo mf d m (Proto.encodeRepeatedMessage encodeRaw tag ns) (set m (get m ++ ns)) := by
  induction ns generalizing m with
  | nil =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_nil, List.append_nil, hsg]
    exact loopsTo_nil mf d m
  | cons n ns' ih =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_cons]
    obtain ⟨hloop, hlen⟩ := hsub n (List.mem_cons_self ..)
    have hns'_sub : ∀ w ∈ ns', LoopsTo mfN dN default (encodeRaw w) w ∧ (encodeRaw w).length < 2 ^ 64 :=
      fun w hw => hsub w (List.mem_cons_of_mem _ hw)
    have hone : LoopsTo mf d m (Proto.encodeMessage encodeRaw tag n) (set m (get m ++ [n])) := by
      apply loopsTo_message mf d m tag mfN dN encodeRaw default n (fun x => set m (get m ++ [x]))
        h1 h2 hdd hloop hlen
      intro depth bs hd
      rw [hmf m depth bs hd]
      unfold Proto.mergeRepeatedMessage
      simp only [Bind.bind, Except.bind]
      cases Proto.mergeMessage mfN .lengthDelimited default bs depth <;> rfl
    have hrest : LoopsTo mf d (set m (get m ++ [n]))
        (Proto.encodeRepeatedMessage encodeRaw tag ns')
        (set (set m (get m ++ [n])) (get (set m (get m ++ [n])) ++ ns')) :=
      ih (set m (get m ++ [n])) hns'_sub
    rw [hgs, hss, List.append_assoc] at hrest
    exact LoopsTo.append hpre hone hrest

theorem mergeTop_of_loopsTo (mf : MergeFieldFn M) (d : Nat) (m : M) (bs : Bytes) (r : M)
    (hd : d ≤ Proto.RECURSION_LIMIT) (h : LoopsTo mf d m bs r) : Proto.mergeTopLevelMessage mf m bs = .ok r :=
  h bs.length Proto.RECURSION_LIMIT (Nat.le_refl _) hd

theorem decodeTop_of_loopsTo [Inhabited M] (mf : MergeFieldFn M) (d : Nat) (bs : Bytes) (r : M)
    (hd : d ≤ Proto.RECURSION_LIMIT) (h : LoopsTo mf d default bs r) : Proto.decodeTopLevelMessage mf bs = .ok r :=
  mergeTop_of_loopsTo mf d default bs r hd h

end CryptoVerification.SpqrV1Sync.Codec
