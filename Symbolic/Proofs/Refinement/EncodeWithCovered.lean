/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.EncodeWithSound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.EvalDist.ProbabilityNotation

/-!
# Coverage of `encodeWith` for `SignalMessage.tryFrom`

Proves `tryFrom_covered`, the converse of `tryFrom_encodeWith`: every byte string accepted by
`SignalMessage.tryFrom protoSignalCodec` decomposes as `encodeWith v f ++ mac` for a variation
`v` satisfying `HonestWF v f`, with decoded message fields matching `f`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Refinement

open DY DY.TrWire
open CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

/-! ## Single-field inversion -/

theorem mergeBytes_inv {wt : WireType} {bs v rest : HwBytes} (h : mergeBytes wt bs = some (v, rest)) :
    wt = .lengthDelimited ∧ ∃ vp, bs = (PbValue.bytes v).body vp ++ rest ∧ v.length < 2 ^ 64 ∧
      (paddedVarint v.length vp).length ≤ 10 := by
  unfold mergeBytes at h
  split at h
  · cases h
  · next hwt =>
    split at h
    · cases h
    · next len rest0 hd =>
      split at h
      · cases h
      · next hl =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pad, hbs, hlen⟩ := decodeVarint_inv hd
        have hv : (rest0.take len.toNat).length = len.toNat := by
          simp only [List.length_take]; omega
        refine ⟨by simpa using hwt, pad, ?_, by rw [hv]; exact len.isLt, by rw [hv]; exact hlen⟩
        simp only [PbValue.body, hv, List.append_assoc, List.take_append_drop]
        exact hbs

theorem mergeUint32_inv {wt : WireType} {bs rest : HwBytes} {v : BitVec 32}
    (h : mergeUint32 wt bs = some (v, rest)) :
    wt = .varint ∧ ∃ n vp, bs = (PbValue.varint n).body vp ++ rest ∧ v = BitVec.ofNat 32 n ∧
      n < 2 ^ 64 ∧ (paddedVarint n vp).length ≤ 10 := by
  unfold mergeUint32 at h
  split at h
  · cases h
  · next hwt =>
    split at h
    · cases h
    · next r rest0 hd =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨pad, hbs, hlen⟩ := decodeVarint_inv hd
      exact ⟨by simpa using hwt, r.toNat, pad, hbs, by rw [BitVec.ofNat_toNat], r.isLt, hlen⟩

theorem WireType.ofNat?_toNat (w : WireType) : WireType.ofNat? w.toNat = some w := by
  cases w <;> rfl

theorem mergeField_inv {m m' : ProtoSignalMessage} {tag : ℕ} {wt : WireType} {bs rest : HwBytes}
    (htag : 1 ≤ tag) (h : mergeField m tag wt bs = some (m', rest)) :
    ∃ x vp, wt = x.wireType ∧ bs = x.body vp ++ rest ∧ m' = setField m tag x ∧
      x.head < 2 ^ 64 ∧ (paddedVarint x.head vp).length ≤ 10 ∧ WireTypeOk tag x := by
  rcases tag with _ | _ | _ | _ | _ | _ | _ | t
  · omega
  all_goals simp only [mergeField, Option.map_eq_some_iff, Prod.mk.injEq] at h
  rotate_left 6
  ·
    obtain ⟨r, hs, rfl, rfl⟩ := h
    obtain ⟨c, hbs, hc⟩ := (skip_prefix _).1 _ _ _ _ _ hs
    have hwt : wt ≠ .endGroup := by rintro rfl; simp [skipField] at hs
    refine ⟨.unknown wt.toNat c, 0, ?_, hbs, rfl, by simp [PbValue.head], by simp [PbValue.head,
      paddedVarint], by omega, wt, WireType.ofNat?_toNat wt, by simpa using hc _ (by omega) []⟩
    simp [PbValue.wireType, WireType.ofNat?_toNat]
  all_goals first
    | (obtain ⟨⟨v, r⟩, hm, rfl, rfl⟩ := h
       obtain ⟨rfl, vp, hbs, hl, hlen⟩ := mergeBytes_inv hm
       exact ⟨.bytes v, vp, rfl, hbs, rfl, hl, hlen, by simp [WireTypeOk]⟩)
    | (obtain ⟨⟨v, r⟩, hm, rfl, rfl⟩ := h
       obtain ⟨rfl, n, vp, hbs, rfl, hl, hlen⟩ := mergeUint32_inv hm
       exact ⟨.varint n, vp, rfl, hbs, rfl, hl, hlen, by simp [WireTypeOk]⟩)

/-! ## Field list inversion -/

def RawItem (it : FieldItem) : Prop := ∃ t x kp vp, it = .extra t x kp vp ∧ FieldWF t kp vp x

theorem RawItem.itemWF {it : FieldItem} (h : RawItem it) (v : EncodingVariation) (f : WireFields) :
    ItemWF v f it := by
  obtain ⟨t, x, kp, vp, rfl, hf⟩ := h
  exact hf

theorem decodeLoop_inv : ∀ (fuel : ℕ) (m r : ProtoSignalMessage) (bs : HwBytes),
    decodeLoop fuel m bs = some r → ∃ items : List FieldItem, (∀ it ∈ items, RawItem it) ∧
      ∀ v f, bs = items.flatMap (FieldItem.encode v f) ∧ r = items.foldl (stepItem v f) m
  | _, m, r, [], h => by
    simp only [decodeLoop, Option.some.injEq] at h
    exact ⟨[], by simp, fun v f => by simp [h]⟩
  | 0, _, _, _ :: _, h => by simp [decodeLoop] at h
  | fuel + 1, m, r, b :: bs, h => by
    simp only [decodeLoop] at h
    split at h
    · cases h
    · next tag wt rest hkey =>
      split at h
      · cases h
      · next m' rest' hmerge =>
        obtain ⟨items, hraw, hrec⟩ := decodeLoop_inv fuel m' r rest' h
        obtain ⟨kp, hk, hkl, h1, h2⟩ := decodeKey_inv hkey
        obtain ⟨x, vp, rfl, hrest, rfl, hx, hl, hwt⟩ := mergeField_inv h1 hmerge
        refine ⟨.extra tag x kp vp :: items, ?_, fun v f => ?_⟩
        · intro it hit
          rcases List.mem_cons.mp hit with rfl | hit
          · exact ⟨tag, x, kp, vp, rfl, ⟨h1, h2, hkl, hx, hl, hwt⟩⟩
          · exact hraw it hit
        · obtain ⟨hbs, hr⟩ := hrec v f
          refine ⟨?_, hr⟩
          rw [hk, hrest, hbs, PbValue.wireType_toNat hwt]
          simp [FieldItem.encode, encodeField_eq]

/-! ## Marking the last item of each known tag -/

/-- Converts `it` to `.known` when it is an `.extra` item with tag in `1..4` absent from `rest`. -/
def markOne (rest : List FieldItem) : FieldItem → FieldItem
  | .extra t x kp vp =>
    if 1 ≤ t ∧ t ≤ 4 ∧ rest.all (·.tag != t) then .known t kp vp else .extra t x kp vp
  | it => it

/-- Replaces the last occurrence of each tag in `1..4` with `.known`. -/
def markLast : List FieldItem → List FieldItem
  | [] => []
  | it :: rest => markOne rest it :: markLast rest

theorem markOne_tag (rest : List FieldItem) (it : FieldItem) : (markOne rest it).tag = it.tag := by
  cases it with
  | known => rfl
  | extra t x kp vp => simp only [markOne]; split <;> rfl

theorem lastWithTag_cons (t : ℕ) (it : FieldItem) (l : List FieldItem) :
    lastWithTag t (it :: l) = (lastWithTag t l).or (if it.tag = t then some it else none) := by
  simp only [lastWithTag, List.filter_cons]
  by_cases h : it.tag = t
  · simp only [h, beq_self_eq_true, ↓reduceIte, List.getLast?_cons]
    cases (l.filter (·.tag == t)).getLast? <;> rfl
  · simp only [show (it.tag == t) = false by simpa using h, h, ↓reduceIte, Bool.false_eq_true]
    cases (l.filter (·.tag == t)).getLast? <;> rfl

theorem lastWithTag_eq_none_iff {t : ℕ} :
    ∀ {l : List FieldItem}, lastWithTag t l = none ↔ l.all (·.tag != t) = true
  | [] => by simp [lastWithTag]
  | it :: l => by
    rw [lastWithTag_cons, List.all_cons, Bool.and_eq_true, ← lastWithTag_eq_none_iff]
    cases lastWithTag t l <;> by_cases h : it.tag = t <;> simp [h]

theorem lastWithTag_mem {t : ℕ} {l : List FieldItem} {it : FieldItem}
    (h : lastWithTag t l = some it) : it ∈ l ∧ it.tag = t := by
  have hm := List.mem_of_getLast? h
  simp only [List.mem_filter, beq_iff_eq] at hm
  exact hm

theorem lastWithTag_markLast {t : ℕ} (ht1 : 1 ≤ t) (ht4 : t ≤ 4) :
    ∀ l : List FieldItem, lastWithTag t (markLast l) = (lastWithTag t l).map (markOne [])
  | [] => rfl
  | it :: l => by
    rw [markLast, lastWithTag_cons, lastWithTag_cons, lastWithTag_markLast ht1 ht4 l, markOne_tag]
    cases hl : lastWithTag t l with
    | some y => rfl
    | none =>
      by_cases ht : it.tag = t
      · simp only [ht, ↓reduceIte, Option.map_none, Option.none_or, Option.map_some]
        congr 1
        cases it with
        | known => rfl
        | extra u x kp vp =>
          simp only [FieldItem.tag] at ht; subst ht
          simp [markOne, ht1, ht4, lastWithTag_eq_none_iff.mp hl]
      · simp [ht]

/-- The last `.extra` item of each tag in `1..4` carries the value given by `knownValue? v f`. -/
def LastKnown (v : EncodingVariation) (f : WireFields) (l : List FieldItem) : Prop :=
  ∀ t x kp vp, lastWithTag t l = some (.extra t x kp vp) → 1 ≤ t → t ≤ 4 → knownValue? v f t = some x

theorem LastKnown.tail {v : EncodingVariation} {f : WireFields} {it : FieldItem}
    {l : List FieldItem} (h : LastKnown v f (it :: l)) : LastKnown v f l := by
  intro t x kp vp hl
  exact h t x kp vp (by rw [lastWithTag_cons, hl]; rfl)

theorem LastKnown.head {v : EncodingVariation} {f : WireFields} {t : ℕ} {x : PbValue}
    {kp vp : ℕ} {l : List FieldItem} (h : LastKnown v f (.extra t x kp vp :: l))
    (hc : 1 ≤ t ∧ t ≤ 4 ∧ l.all (·.tag != t) = true) : knownValue? v f t = some x :=
  h t x kp vp (by rw [lastWithTag_cons, lastWithTag_eq_none_iff.mpr hc.2.2]; simp [FieldItem.tag])
    hc.1 hc.2.1

theorem flatMap_markLast (v : EncodingVariation) (f : WireFields) :
    ∀ l : List FieldItem, LastKnown v f l →
      (markLast l).flatMap (FieldItem.encode v f) = l.flatMap (FieldItem.encode v f)
  | [] => fun _ => rfl
  | it :: l => fun hk => by
    simp only [markLast, List.flatMap_cons, flatMap_markLast v f l hk.tail]
    congr 1
    cases it with
    | known => rfl
    | extra u x kp vp =>
      simp only [markOne]
      split
      · next hc => simp [FieldItem.encode, hk.head hc]
      · rfl

theorem itemWF_markLast (v : EncodingVariation) (f : WireFields) :
    ∀ l : List FieldItem, (∀ it ∈ l, RawItem it) → LastKnown v f l →
      ∀ it ∈ markLast l, ItemWF v f it
  | [] => fun _ _ _ h => by simp [markLast] at h
  | it :: l => fun hraw hk it' hit' => by
    rcases List.mem_cons.mp hit' with rfl | hit'
    · obtain ⟨u, x, kp, vp, rfl, hf⟩ := hraw it (by simp)
      simp only [markOne]
      split
      · next hc => exact ⟨x, hk.head hc, hf⟩
      · exact hf
    · exact itemWF_markLast v f l (fun i hi => hraw i (by simp [hi])) hk.tail it' hit'

/-! ## Decoded field projections -/

theorem raw_proj {β : Type} (items : List FieldItem) (hraw : ∀ it ∈ items, RawItem it)
    (proj : ProtoSignalMessage → β) (t : ℕ)
    (hkeep : ∀ m u x, u ≠ t → proj (setField m u x) = proj m)
    (hset : ∀ m x, WireTypeOk t x → proj (setField m t x) = proj (setField emptyProtoSignalMessage t x))
    (v : EncodingVariation) (f : WireFields) :
    proj (items.foldl (stepItem v f) emptyProtoSignalMessage) =
      ((lastWithTag t items).map fun it => proj (stepItem v f emptyProtoSignalMessage it)).getD (proj emptyProtoSignalMessage) :=
  proj_foldl_stepItem v f proj t (stepItem_keep v f proj t hkeep) items emptyProtoSignalMessage
    fun it hit ht m => stepItem_set v f proj t hset it ((hraw it hit).itemWF v f) ht m

theorem raw_last (items : List FieldItem) (hraw : ∀ it ∈ items, RawItem it) (t : ℕ) :
    lastWithTag t items = none ∨
      ∃ x kp vp, lastWithTag t items = some (.extra t x kp vp) ∧ FieldWF t kp vp x := by
  cases hl : lastWithTag t items with
  | none => exact Or.inl rfl
  | some it =>
    obtain ⟨hm, ht⟩ := lastWithTag_mem hl
    obtain ⟨u, x, kp, vp, rfl, hf⟩ := hraw it hm
    simp only [FieldItem.tag] at ht; subst ht
    exact Or.inr ⟨x, kp, vp, rfl, hf⟩

/-! ## `tryFrom` -/

theorem tryFrom_ok_inv {b : HwBytes} {m : SignalMessage}
    (h : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    macLength + 1 ≤ b.length ∧ m.messageVersion = b.headD 0 >>> 4 ∧
      preKyberVersion ≤ m.messageVersion ∧ m.messageVersion ≤ currentVersion ∧
      ∃ p rk, decode ((b.take (b.length - macLength)).drop 1) = some p ∧ p.ratchetKey = some rk ∧
        PublicKey.deserialize rk = .ok m.senderRatchetKey ∧ p.counter = some m.counter ∧
        p.ciphertext = some m.ciphertext ∧ m.previousCounter = p.previousCounter.getD 0 := by
  unfold SignalMessage.tryFrom at h
  dsimp only at h
  generalize hv : b.headD 0 >>> 4 = ver at h
  generalize hd : protoSignalCodec.decode ((b.take (b.length - macLength)).drop 1) = od at h
  by_cases h1 : b.length < macLength + 1
  · simp only [h1, ↓reduceIte] at h; cases h
  by_cases h2 : ver < preKyberVersion
  · simp only [h1, h2, ↓reduceIte] at h; cases h
  by_cases h3 : currentVersion < ver
  · simp only [h1, h2, h3, ↓reduceIte] at h; cases h
  simp only [h1, h2, h3, ↓reduceIte] at h
  cases od with
  | none => simp at h
  | some p =>
    cases hrk : p.ratchetKey with
    | none => simp [hrk] at h
    | some rk =>
      cases hk : PublicKey.deserialize rk with
      | error e => simp [hrk, hk, bind, Except.bind] at h
      | ok k =>
        cases hc : p.counter with
        | none => simp [hrk, hk, hc, bind, Except.bind] at h
        | some c =>
          cases hct : p.ciphertext with
          | none => simp [hrk, hk, hc, hct, bind, Except.bind] at h
          | some ct =>
            simp [hrk, hk, hc, hct] at h
            subst h
            exact ⟨by omega, rfl, BitVec.not_lt.mp h2, BitVec.not_lt.mp h3, p, rk, hd, hrk, hk,
              hc, hct, rfl⟩

theorem deserialize_inv {rk : HwBytes} {k : PublicKey} (h : PublicKey.deserialize rk = .ok k) :
    ∃ rest, rk = 0x05#8 :: rest ∧ 32 ≤ rest.length ∧ k.bytes.toList = rest.take 32 := by
  unfold PublicKey.deserialize at h
  split at h
  · cases h
  · next t rest =>
    split at h
    · cases h
    · next ht =>
      split at h
      · next hl =>
        cases h
        simp only [ne_eq, Decidable.not_not] at ht
        exact ⟨rest, by rw [ht]; rfl, hl, rfl⟩
      · cases h

/-- Every byte string accepted by `SignalMessage.tryFrom protoSignalCodec` decomposes as
`encodeWith v f ++ mac` with `mac.length = macLength`, `HonestWF v f`, and decoded fields `f`. -/
theorem tryFrom_covered (b : HwBytes) (m : SignalMessage)
    (h : SignalMessage.tryFrom protoSignalCodec b = .ok m) :
    ∃ v f mac, b = encodeWith v f ++ mac ∧ mac.length = macLength ∧ HonestWF v f ∧
      m.messageVersion.toNat = f.version ∧ m.senderRatchetKey.bytes.toList = f.ratchetKey ∧
      m.counter.toNat = f.counter ∧ m.previousCounter.toNat = f.previousCounter ∧
      m.ciphertext = f.ciphertext := by
  obtain ⟨hlen, hver, hv3, hv4, p, rk, hdec, hrk, hdes, hctr, hct, hpc⟩ := tryFrom_ok_inv h
  obtain ⟨items, hraw, hitems⟩ := decodeLoop_inv _ _ _ _ hdec
  have hp := (hitems canonicalVariation ⟨0, [], 0, 0, []⟩).2
  obtain ⟨kp1, vp1, hl1⟩ : ∃ kp vp, lastWithTag 1 items = some (.extra 1 (.bytes rk) kp vp) := by
    have e := raw_proj items hraw (·.ratchetKey) 1
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl)
      canonicalVariation ⟨0, [], 0, 0, []⟩
    rw [← hp, hrk] at e
    rcases raw_last items hraw 1 with hn | ⟨x, kp, vp, hl, hf⟩
    · rw [hn] at e; cases e
    · rw [hl] at e
      have hw := hf.wireType
      cases x with
      | bytes y => cases e; exact ⟨kp, vp, hl⟩
      | varint => simp only [WireTypeOk] at hw; omega
      | unknown => simp only [WireTypeOk] at hw; omega
  obtain ⟨n2, kp2, vp2, hl2, hc2⟩ : ∃ n kp vp,
      lastWithTag 2 items = some (.extra 2 (.varint n) kp vp) ∧ m.counter = BitVec.ofNat 32 n := by
    have e := raw_proj items hraw (·.counter) 2
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl)
      canonicalVariation ⟨0, [], 0, 0, []⟩
    rw [← hp, hctr] at e
    rcases raw_last items hraw 2 with hn | ⟨x, kp, vp, hl, hf⟩
    · rw [hn] at e; cases e
    · rw [hl] at e
      have hw := hf.wireType
      cases x with
      | varint n =>
        have e' : some m.counter = some (BitVec.ofNat 32 n) := e
        exact ⟨n, kp, vp, hl, Option.some.inj e'⟩
      | bytes => simp only [WireTypeOk] at hw; omega
      | unknown => simp only [WireTypeOk] at hw; omega
  obtain ⟨n3, h3⟩ : ∃ n, (lastWithTag 3 items = none ∧ n = 0 ∧ p.previousCounter = none) ∨
      ∃ kp vp, lastWithTag 3 items = some (.extra 3 (.varint n) kp vp) ∧
        p.previousCounter = some (BitVec.ofNat 32 n) := by
    have e := raw_proj items hraw (·.previousCounter) 3
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl)
      canonicalVariation ⟨0, [], 0, 0, []⟩
    rw [← hp] at e
    rcases raw_last items hraw 3 with hn | ⟨x, kp, vp, hl, hf⟩
    · rw [hn] at e; exact ⟨0, Or.inl ⟨hn, rfl, e⟩⟩
    · rw [hl] at e
      have hw := hf.wireType
      cases x with
      | varint n => exact ⟨n, Or.inr ⟨kp, vp, hl, e⟩⟩
      | bytes => simp only [WireTypeOk] at hw; omega
      | unknown => simp only [WireTypeOk] at hw; omega
  obtain ⟨kp4, vp4, hl4⟩ : ∃ kp vp,
      lastWithTag 4 items = some (.extra 4 (.bytes m.ciphertext) kp vp) := by
    have e := raw_proj items hraw (·.ciphertext) 4
      (by intro m u x hu; rcases u with _|_|_|_|_|_|_|u <;> cases x <;> first | omega | rfl)
      (by intro m x hx; cases x <;> simp only [WireTypeOk] at hx <;> first | omega | rfl)
      canonicalVariation ⟨0, [], 0, 0, []⟩
    rw [← hp, hct] at e
    rcases raw_last items hraw 4 with hn | ⟨x, kp, vp, hl, hf⟩
    · rw [hn] at e; cases e
    · rw [hl] at e
      have hw := hf.wireType
      cases x with
      | bytes y => cases e; exact ⟨kp, vp, hl⟩
      | varint => simp only [WireTypeOk] at hw; omega
      | unknown => simp only [WireTypeOk] at hw; omega
  obtain ⟨rest0, rfl, hrl, hkb⟩ := deserialize_inv hdes
  obtain ⟨b0, bt, rfl⟩ : ∃ b0 bt, b = b0 :: bt := by
    cases b with
    | nil => simp [macLength] at hlen
    | cons b0 bt => exact ⟨b0, bt, rfl⟩
  let f : WireFields :=
    { version := b0.toNat / 16, ratchetKey := rest0.take 32, counter := n2 % 2 ^ 32,
      previousCounter := n3 % 2 ^ 32, ciphertext := m.ciphertext }
  let v : EncodingVariation :=
    { versionLowNibble := b0.toNat % 16, ratchetKeyTrailingBytes := rest0.drop 32,
      counterHigh := n2 / 2 ^ 32, previousCounterHigh := n3 / 2 ^ 32, fields := markLast items }
  have hknown : LastKnown v f items := by
    intro t x kp vp hl h1 h4
    interval_cases t
    · rw [hl1] at hl; cases hl
      simp [knownValue?, v, f]
    · rw [hl2] at hl; cases hl
      simp only [knownValue?, v, f, Option.some.injEq, PbValue.varint.injEq]
      omega
    · rcases h3 with ⟨hn, -, -⟩ | ⟨kp3, vp3, hl3, -⟩
      · rw [hn] at hl; cases hl
      · rw [hl3] at hl; cases hl
        simp only [knownValue?, v, f, Option.some.injEq, PbValue.varint.injEq]
        omega
    · rw [hl4] at hl; cases hl
      rfl
  have hb0 : (b0 >>> 4).toNat = b0.toNat / 16 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hvl : 3 ≤ b0.toNat / 16 ∧ b0.toNat / 16 ≤ 4 := by
    rw [hver] at hv3 hv4
    simp only [List.headD_cons, BitVec.le_def, preKyberVersion, currentVersion, hb0] at hv3 hv4
    exact ⟨hv3, hv4⟩
  have hbl : bt.length + 1 - macLength = (bt.length - macLength) + 1 := by
    simp only [List.length_cons, macLength] at hlen ⊢; omega
  refine ⟨v, f, bt.drop (bt.length - macLength), ?_, ?_, ?_, ?_, hkb, ?_, ?_, rfl⟩
  ·
    have hbody := (hitems v f).1
    simp only [List.length_cons, hbl, List.take_succ_cons, List.drop_succ_cons,
      List.drop_zero] at hbody
    simp only [encodeWith, List.cons_append, flatMap_markLast v f items hknown, v, ← hbody,
      List.take_append_drop, List.cons.injEq, and_true]
    apply BitVec.eq_of_toNat_eq
    have := b0.isLt
    have hfv : f.version = b0.toNat / 16 := rfl
    rw [BitVec.toNat_ofNat]
    omega
  · simp only [List.length_drop, macLength] at hlen ⊢; simp only [List.length_cons] at hlen; omega
  · exact
    { version := hvl
      ratchetKey := by simp only [f, List.length_take]; omega
      counter := Nat.mod_lt _ (by norm_num)
      previousCounter := Nat.mod_lt _ (by norm_num)
      items := itemWF_markLast v f items hraw hknown
      lastRatchetKey := ⟨kp1, vp1, by
        rw [lastWithTag_markLast (by norm_num) (by norm_num), hl1]; rfl⟩
      lastCounter := ⟨kp2, vp2, by
        rw [lastWithTag_markLast (by norm_num) (by norm_num), hl2]; rfl⟩
      lastPreviousCounter := by
        rcases h3 with ⟨hn, rfl, -⟩ | ⟨kp3, vp3, hl3, -⟩
        · right
          exact ⟨by rw [lastWithTag_markLast (by norm_num) (by norm_num), hn]; rfl, rfl⟩
        · left
          exact ⟨kp3, vp3, by rw [lastWithTag_markLast (by norm_num) (by norm_num), hl3]; rfl⟩
      lastCiphertext := ⟨kp4, vp4, by
        rw [lastWithTag_markLast (by norm_num) (by norm_num), hl4]; rfl⟩ }
  · rw [hver]; exact hb0
  · rw [hc2, BitVec.toNat_ofNat]
  · rw [hpc]
    rcases h3 with ⟨-, rfl, hn⟩ | ⟨-, -, -, hs⟩
    · rw [hn]; rfl
    · rw [hs, Option.getD_some, BitVec.toNat_ofNat]

/-! ## Varint and little-endian literal round-trips -/

theorem readVarint_paddedVarint (n : ℕ) (rest : HwBytes) :
    readVarint (paddedVarint n 0 ++ rest) = some (n, rest) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [paddedVarint]
    by_cases hn : n < 128
    · have h8 : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
      simp [hn, readVarint, h8]
    · have h8 : (BitVec.ofNat 8 (n % 128 + 128)).toNat = n % 128 + 128 := by
        rw [BitVec.toNat_ofNat]; omega
      simp only [hn, ↓reduceIte, List.cons_append, readVarint, h8,
        show ¬ n % 128 + 128 < 128 by omega, ih (n / 128) (by omega), Option.map_some,
        Option.some.injEq, Prod.mk.injEq, and_true]
      omega

def u32Bytes (n : ℕ) : HwBytes :=
  [BitVec.ofNat 8 n, BitVec.ofNat 8 (n / 2 ^ 8), BitVec.ofNat 8 (n / 2 ^ 16),
    BitVec.ofNat 8 (n / 2 ^ 24)]

theorem leNat_u32Bytes {n : ℕ} (h : n < 2 ^ 32) : decodeLittleEndianNat (u32Bytes n) = n := by
  simp only [decodeLittleEndianNat, u32Bytes, List.foldr_cons, List.foldr_nil, BitVec.toNat_ofNat]
  omega

end DY.Libsignal.Refinement
