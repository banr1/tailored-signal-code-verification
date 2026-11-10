/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

/-!
# Prost Round-Trip for `V1State.Chunked.*`

`LoopsTo` (recursion depth 2) and `decode (encodeRaw m) = .ok m` round-trip theorems for all eleven
`V1State.Chunked.*` protobuf message types when the encoded byte length fits in 64 bits.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
open CryptoVerification.SpqrV1.Prost.MessageMerge (ProtoPrefixStep)

/-! ### Private `ProtoPrefixStep` and length helpers -/

private theorem len_append_left {a b : Bytes} {B : Nat} (h : (a ++ b).length < B) : a.length < B := by
  rw [List.length_append] at h; omega

private theorem len_append_right {a b : Bytes} {B : Nat} (h : (a ++ b).length < B) : b.length < B := by
  rw [List.length_append] at h; omega

private theorem len_encodeBytesField {tag : BitVec 32} {v : Bytes} {B : Nat}
    (h : (Proto.encodeBytesField tag v).length < B) : v.length < B := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond at h
  split at h
  · rename_i he
    rw [List.isEmpty_iff.mp he]
    exact h
  · simp only [List.length_append] at h; omega

private theorem len_encodeOptMessage {N : Type} {enc : N → Bytes} {tag : BitVec 32} {o : Option N} {B : Nat}
    (h : (Proto.encodeOptMessage enc tag o).length < B) (n : N) (ho : o = some n) :
    (enc n).length < B := by
  subst ho
  simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.length_append] at h
  omega

private theorem len_encodeRepeatedBytes {tag : BitVec 32} {vs : List Bytes} {B : Nat}
    (h : (Proto.encodeRepeatedBytes tag vs).length < B) : ∀ v ∈ vs, v.length < B := by
  induction vs with
  | nil => intro _ hv; cases hv
  | cons w ws ih =>
    have hcons : Proto.encodeRepeatedBytes tag (w :: ws) =
        Proto.encodeBytesUncond tag w ++ Proto.encodeRepeatedBytes tag ws := rfl
    rw [hcons] at h
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hmem
    · have hw := len_append_left h
      simp only [Proto.encodeBytesUncond, List.length_append] at hw; omega
    · exact ih (len_append_right h) v hmem

private theorem pps_err {α : Type} (e : DecodeErr) :
    ProtoPrefixStep (α := α) (fun _ => .error e) where
  ok_append _ _ _ _ h := by cases h
  err_overshoot _ _ _ _ _ _ h := by cases h

private theorem pps_ok {α : Type} (v : α) :
    ProtoPrefixStep (fun bs => .ok (v, bs)) where
  ok_append s _ v' r' h := by
    injection h with hp; injection hp with hv hr; subst hv; subst hr
    exact ⟨Nat.le_refl _, rfl⟩
  err_overshoot _ _ _ _ _ h _ := by cases h

private theorem pps_congr {α : Type} {f g : Bytes → Except DecodeErr (α × Bytes)}
    (hf : ProtoPrefixStep f) (heq : ∀ bs, f bs = g bs) : ProtoPrefixStep g where
  ok_append s a v r' h := by rw [← heq] at h ⊢; exact hf.ok_append s a v r' h
  err_overshoot s a e v r herr hok := by rw [← heq] at herr hok; exact hf.err_overshoot s a e v r herr hok

private theorem pps_ite {α : Type} {f g : Bytes → Except DecodeErr (α × Bytes)} (c : Bool)
    (hf : ProtoPrefixStep f) (hg : ProtoPrefixStep g) :
    ProtoPrefixStep (fun bs => if c then f bs else g bs) := by
  cases c
  · simpa using hg
  · simpa using hf

private theorem pps_ite_prop {α : Type} {f g : Bytes → Except DecodeErr (α × Bytes)} (P : Prop) [Decidable P]
    (hf : ProtoPrefixStep f) (hg : ProtoPrefixStep g) :
    ProtoPrefixStep (fun bs => if P then f bs else g bs) := by
  by_cases hP : P
  · simpa [hP] using hf
  · simpa [hP] using hg

private theorem pps_seq {α β : Type} {f : Bytes → Except DecodeErr (α × Bytes)}
    {g : α → Bytes → Except DecodeErr (β × Bytes)}
    (hf : ProtoPrefixStep f) (hg : ∀ v, ProtoPrefixStep (g v)) :
    ProtoPrefixStep (fun bs => do let (v, rest) ← f bs; g v rest) where
  ok_append s a w r' h := by
    change Except.bind (f s) _ = .ok (w, r') at h
    cases hfs : f s with
    | error e => rw [hfs] at h; cases h
    | ok vr =>
      rcases vr with ⟨v, rest⟩
      rw [hfs] at h; dsimp only [Except.bind] at h
      obtain ⟨hl1, hfa⟩ := hf.ok_append s a v rest hfs
      obtain ⟨hl2, hga⟩ := (hg v).ok_append rest a w r' h
      refine ⟨Nat.le_trans hl2 hl1, ?_⟩
      change Except.bind (f (s ++ a)) _ = .ok (w, r' ++ a)
      rw [hfa]; exact hga
  err_overshoot s a e w r herr hok := by
    change Except.bind (f (s ++ a)) _ = .ok (w, r) at hok
    cases hfsa : f (s ++ a) with
    | error ea => rw [hfsa] at hok; cases hok
    | ok vra =>
      rcases vra with ⟨va, resta⟩
      rw [hfsa] at hok; dsimp only [Except.bind] at hok
      obtain ⟨hl_r, _⟩ := (hg va).ok_append resta [] w r hok
      cases hfs : f s with
      | error es =>
        exact Nat.lt_of_le_of_lt hl_r (hf.err_overshoot s a es va resta hfs hfsa)
      | ok vr0 =>
        rcases vr0 with ⟨v0, rest0⟩
        change Except.bind (f s) _ = .error e at herr
        rw [hfs] at herr; dsimp only [Except.bind] at herr
        obtain ⟨_, hfa0⟩ := hf.ok_append s a v0 rest0 hfs
        rw [hfsa] at hfa0; injection hfa0 with hp; injection hp with hv hrest
        subst hv; subst hrest
        exact (hg va).err_overshoot rest0 a e w r herr hok

private theorem pps_map {α β : Type} {f : Bytes → Except DecodeErr (α × Bytes)}
    (g : α → β) (hf : ProtoPrefixStep f) :
    ProtoPrefixStep (fun bs => do let (v, rest) ← f bs; .ok (g v, rest)) :=
  pps_seq hf (fun v => pps_ok (g v))

private theorem pps_guard {α : Type} {f : Bytes → Except DecodeErr (α × Bytes)}
    (c : Except DecodeErr Unit) (hf : ProtoPrefixStep f) :
    ProtoPrefixStep (fun bs => do c; f bs) := by
  cases c with
  | error e => exact pps_err e
  | ok _ => exact hf

private def readByte : Bytes → Except DecodeErr (BitVec 8 × Bytes)
  | [] => .error .bufferUnderflow
  | b :: rest => .ok (b, rest)

private theorem pps_readByte : ProtoPrefixStep readByte where
  ok_append s a v r' h := by
    cases s with
    | nil => cases h
    | cons b tl =>
      injection h with hp; injection hp with hv hr; subst hv; subst hr
      exact ⟨Nat.le_succ _, rfl⟩
  err_overshoot s a e v r herr hok := by
    cases s with
    | cons _ _ => cases herr
    | nil =>
      cases a with
      | nil => cases hok
      | cons b tl =>
        injection hok with hp; injection hp with _ hr; subst hr
        exact Nat.lt_succ_self _

private theorem pps_takeExact : ∀ n, ProtoPrefixStep (Proto.takeExact n)
  | 0 => pps_ok []
  | n + 1 =>
    pps_congr (pps_seq pps_readByte (fun b => pps_map (b :: ·) (pps_takeExact n)))
      (fun bs => by cases bs <;> rfl)

private theorem pps_dropExact : ∀ n, ProtoPrefixStep (fun bs => do let r ← Proto.dropExact n bs; .ok ((), r))
  | 0 => pps_ok ()
  | n + 1 =>
    pps_congr (pps_seq pps_readByte (fun _ => pps_dropExact n))
      (fun bs => by cases bs <;> rfl)

private theorem pps_decodeVarintAux : ∀ fuel idx acc, ProtoPrefixStep (Proto.decodeVarintAux fuel idx acc)
  | 0, _, _ => pps_err .invalidVarint
  | fuel + 1, idx, acc =>
    pps_congr
      (pps_seq pps_readByte fun b =>
        pps_ite (idx == 9)
          (pps_ite_prop (b ≥ 0x02#8) (pps_err .invalidVarint)
            (pps_ok (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 63))))
          (let acc' := acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7))
           pps_ite_prop (b < 0x80#8) (pps_ok acc') (pps_decodeVarintAux fuel (idx + 1) acc')))
      (fun bs => by cases bs <;> rfl)

private theorem pps_decodeVarint : ProtoPrefixStep Proto.decodeVarint :=
  pps_decodeVarintAux 10 0 0#64

private theorem pps_decodeKeyTail (key : BitVec 64) :
    ProtoPrefixStep (fun rest =>
      if key > 0xffffffff#64 then .error (.invalidKey key)
      else
        match WireType.ofU64? (key &&& 0x7#64) with
        | none => .error (.invalidWireType (key &&& 0x7#64))
        | some wt =>
          let tag : BitVec 32 := (key >>> 3).truncate 32
          if tag < Proto.MIN_TAG then .error (.invalidTag tag) else .ok ((tag, wt), rest)) := by
  by_cases hk : key > 0xffffffff#64
  · simpa [hk] using pps_err (.invalidKey key)
  · simp only [hk, ↓reduceIte]
    cases WireType.ofU64? (key &&& 0x7#64) with
    | none => exact pps_err _
    | some wt => exact pps_ite_prop _ (pps_err _) (pps_ok _)

private theorem pps_decodeKey : ProtoPrefixStep Proto.decodeKey :=
  pps_congr (pps_seq pps_decodeVarint pps_decodeKeyTail) (fun bs => by
    unfold Proto.decodeKey
    change Except.bind (Proto.decodeVarint bs) _ = Except.bind (Proto.decodeVarint bs) _
    cases Proto.decodeVarint bs with
    | error _ => rfl
    | ok kr =>
      rcases kr with ⟨key, rest⟩
      dsimp only [Except.bind]
      by_cases hk : key > 0xffffffff#64
      · simp only [hk, ↓reduceIte]
      · simp only [hk, ↓reduceIte]
        cases WireType.ofU64? (key &&& 0x7#64) <;> rfl)

private theorem decodeVarintAux_len :
    ∀ fuel idx acc bs v rest, Proto.decodeVarintAux fuel idx acc bs = .ok (v, rest) → rest.length < bs.length
  | 0, _, _, _, _, _, h => by cases h
  | _ + 1, _, _, [], _, _, h => by cases h
  | fuel + 1, idx, acc, b :: tl, v, rest, h => by
    dsimp only [Proto.decodeVarintAux] at h
    split at h
    · split at h
      · cases h
      · injection h with hp; injection hp with _ hr; subst hr; exact Nat.lt_succ_self _
    · split at h
      · injection h with hp; injection hp with _ hr; subst hr; exact Nat.lt_succ_self _
      · exact Nat.lt_trans (decodeVarintAux_len fuel _ _ tl v rest h) (Nat.lt_succ_self _)

private theorem decodeKey_len {bs : Bytes} {kw : BitVec 32 × WireType} {rest : Bytes}
    (h : Proto.decodeKey bs = .ok (kw, rest)) : rest.length < bs.length := by
  unfold Proto.decodeKey at h
  change Except.bind (Proto.decodeVarint bs) _ = .ok (kw, rest) at h
  cases hdv : Proto.decodeVarint bs with
  | error e => rw [hdv] at h; cases h
  | ok kr =>
    rcases kr with ⟨key, r0⟩
    rw [hdv] at h; dsimp only [Except.bind] at h
    have hlen := decodeVarintAux_len 10 0 0#64 bs key r0 hdv
    split at h
    · cases h
    · cases hwt : WireType.ofU64? (key &&& 0x7#64) with
      | none => rw [hwt] at h; cases h
      | some w =>
        rw [hwt] at h
        change (if (key >>> 3).truncate 32 < Proto.MIN_TAG then _ else _) = Except.ok (kw, rest) at h
        split at h
        · cases h
        · injection h with hp; injection hp with _ hr; subst hr; exact hlen

private theorem skipGroupLoop_fuel_irrel
    (skipInner : WireType → BitVec 32 → Bytes → Except DecodeErr Bytes)
    (hinner : ∀ wt tag s r', skipInner wt tag s = .ok r' → r'.length ≤ s.length) :
    ∀ (n : Nat) (bs : Bytes), bs.length ≤ n →
      ∀ {f1 f2 : Nat} (groupTag : BitVec 32), bs.length ≤ f1 → bs.length ≤ f2 →
        Proto.skipGroupLoop skipInner f1 groupTag bs = Proto.skipGroupLoop skipInner f2 groupTag bs
  | 0, bs, hn, f1, f2, groupTag, _, _ => by
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hn)
    subst hbs
    have hnil : ∀ f, Proto.skipGroupLoop skipInner f groupTag [] = .error .bufferUnderflow := by
      intro f; cases f <;> rfl
    rw [hnil, hnil]
  | _ + 1, [], _, _, _, groupTag, _, _ => by
    have hnil : ∀ f, Proto.skipGroupLoop skipInner f groupTag [] = .error .bufferUnderflow := by
      intro f; cases f <;> rfl
    rw [hnil, hnil]
  | n + 1, b :: tl, hn, f1, f2, groupTag, hf1, hf2 => by
    cases f1 with
    | zero => cases hf1
    | succ f1' =>
      cases f2 with
      | zero => cases hf2
      | succ f2' =>
        dsimp only [Proto.skipGroupLoop]
        change Except.bind (Proto.decodeKey (b :: tl)) _ = Except.bind (Proto.decodeKey (b :: tl)) _
        cases hdk : Proto.decodeKey (b :: tl) with
        | error _ => rfl
        | ok kwr =>
          rcases kwr with ⟨⟨innerTag, innerWt⟩, rest⟩
          dsimp only [Except.bind]
          split
          · rfl
          · change Except.bind (skipInner innerWt innerTag rest) _ = Except.bind (skipInner innerWt innerTag rest) _
            cases hsi : skipInner innerWt innerTag rest with
            | error _ => rfl
            | ok rest' =>
              dsimp only [Except.bind]
              have hlt : rest.length < (b :: tl).length := decodeKey_len hdk
              have hle : rest'.length ≤ rest.length := hinner innerWt innerTag rest rest' hsi
              exact skipGroupLoop_fuel_irrel skipInner hinner n rest' (by omega) groupTag (by omega) (by omega)

private theorem pps_skipGroupLoop_fixed
    (skipInner : WireType → BitVec 32 → Bytes → Except DecodeErr Bytes)
    (hinner : ∀ wt tag, ProtoPrefixStep (fun bs => do let r ← skipInner wt tag bs; .ok ((), r))) :
    ∀ fuel groupTag, ProtoPrefixStep (fun bs => do let r ← Proto.skipGroupLoop skipInner fuel groupTag bs; .ok ((), r))
  | 0, _ => pps_err .bufferUnderflow
  | fuel + 1, groupTag =>
    pps_congr
      (pps_seq pps_decodeKey fun kw =>
        pps_ite (kw.2 == .endGroup)
          (pps_ite (kw.1 != groupTag) (pps_err .unexpectedEndGroupTag) (pps_ok ()))
          (pps_seq (hinner kw.2 kw.1) fun _ => pps_skipGroupLoop_fixed skipInner hinner fuel groupTag))
      (fun bs => by
        dsimp only [Proto.skipGroupLoop]
        change Except.bind (Proto.decodeKey bs) _ = Except.bind (Except.bind (Proto.decodeKey bs) _) _
        cases Proto.decodeKey bs with
        | error _ => rfl
        | ok kwr =>
          rcases kwr with ⟨⟨innerTag, innerWt⟩, rest⟩
          dsimp only [Except.bind]
          by_cases he : (innerWt == .endGroup) = true
          · simp only [he, ↓reduceIte]
            by_cases ht : (innerTag != groupTag) = true
            · simp only [ht, ↓reduceIte]
            · have htf : (innerTag != groupTag) = false := Bool.eq_false_iff.mpr ht
              simp only [htf, Bool.false_eq_true, ↓reduceIte]
          · have hef : (innerWt == .endGroup) = false := Bool.eq_false_iff.mpr he
            simp only [hef, Bool.false_eq_true, ↓reduceIte]
            change Except.bind (Except.bind (skipInner innerWt innerTag rest) _) _ =
              Except.bind (Except.bind (skipInner innerWt innerTag rest) _) _
            cases skipInner innerWt innerTag rest <;> rfl)

private theorem pps_skipFieldAux :
    ∀ depth wt tag, ProtoPrefixStep (fun bs => do let r ← Proto.skipFieldAux depth wt tag bs; .ok ((), r))
  | 0, _, _ => pps_err .recursionLimitExceeded
  | depth' + 1, wt, tag => by
    have ih := pps_skipFieldAux depth'
    have hlen : ∀ iwt itag s r', Proto.skipFieldAux depth' iwt itag s = .ok r' → r'.length ≤ s.length := by
      intro iwt itag s r' hok
      refine ((ih iwt itag).ok_append s [] () r' ?_).1
      change Except.bind (Proto.skipFieldAux depth' iwt itag s) _ = .ok ((), r')
      rw [hok]; rfl
    cases wt with
    | startGroup =>
      refine ⟨fun s a _ r' hok => ?_, fun s a e _ r herr hok => ?_⟩
      · have hf := pps_skipGroupLoop_fixed (Proto.skipFieldAux depth') ih (s ++ a).length tag
        have hsa : s.length ≤ (s ++ a).length := by rw [List.length_append]; omega
        have heq1 := skipGroupLoop_fuel_irrel (Proto.skipFieldAux depth') hlen s.length s (Nat.le_refl _) tag (Nat.le_refl _) hsa
        dsimp only [Proto.skipFieldAux] at hok ⊢
        change Except.bind (Proto.skipGroupLoop _ s.length tag s) _ = .ok ((), r') at hok
        rw [heq1] at hok
        exact hf.ok_append s a () r' hok
      · have hf := pps_skipGroupLoop_fixed (Proto.skipFieldAux depth') ih (s ++ a).length tag
        have hsa : s.length ≤ (s ++ a).length := by rw [List.length_append]; omega
        have heq1 := skipGroupLoop_fuel_irrel (Proto.skipFieldAux depth') hlen s.length s (Nat.le_refl _) tag (Nat.le_refl _) hsa
        dsimp only [Proto.skipFieldAux] at herr hok
        change Except.bind (Proto.skipGroupLoop _ s.length tag s) _ = .error e at herr
        rw [heq1] at herr
        exact hf.err_overshoot s a e () r herr hok
    | varint =>
      exact pps_congr (pps_seq pps_decodeVarint fun _ => pps_ok ()) (fun bs => by
        dsimp only [Proto.skipFieldAux, Proto.skipFieldNonGroup]
        change Except.bind (Proto.decodeVarint bs) _ = Except.bind (Except.bind (Proto.decodeVarint bs) _) _
        cases Proto.decodeVarint bs <;> rfl)
    | SixtyFourBit =>
      exact pps_dropExact 8
    | lengthDelimited =>
      exact pps_congr (pps_seq pps_decodeVarint fun len => pps_dropExact len.toNat) (fun bs => by
        dsimp only [Proto.skipFieldAux, Proto.skipFieldNonGroup]
        change Except.bind (Proto.decodeVarint bs) _ = Except.bind (Except.bind (Proto.decodeVarint bs) _) _
        cases Proto.decodeVarint bs <;> rfl)
    | endGroup =>
      exact pps_err .unexpectedEndGroupTag
    | ThirtyTwoBit =>
      exact pps_dropExact 4

private theorem pps_skipField {M : Type} (m : M) (wt : WireType) (tag : BitVec 32) (depth : Nat) :
    ProtoPrefixStep (fun bs => do let bs' ← Proto.skipField wt tag bs depth; .ok (m, bs')) :=
  pps_congr (pps_map (fun _ => m) (pps_skipFieldAux depth wt tag))
    (fun bs => by
      unfold Proto.skipField
      change Except.bind (Except.bind (Proto.skipFieldAux depth wt tag bs) _) _ =
        Except.bind (Proto.skipFieldAux depth wt tag bs) _
      cases Proto.skipFieldAux depth wt tag bs <;> rfl)

private theorem pps_mergeUint32 (wt : WireType) : ProtoPrefixStep (Proto.mergeUint32 wt) :=
  pps_guard (Proto.checkWireType .varint wt) (pps_map (fun v => v.truncate 32) pps_decodeVarint)

private theorem pps_mergeUint64 (wt : WireType) : ProtoPrefixStep (Proto.mergeUint64 wt) :=
  pps_guard (Proto.checkWireType .varint wt) pps_decodeVarint

private theorem pps_mergeBool (wt : WireType) : ProtoPrefixStep (Proto.mergeBool wt) :=
  pps_guard (Proto.checkWireType .varint wt) (pps_map (fun v => v != 0#64) pps_decodeVarint)

private theorem pps_mergeBytes (wt : WireType) : ProtoPrefixStep (Proto.mergeBytes wt) :=
  pps_guard (Proto.checkWireType .lengthDelimited wt) (pps_seq pps_decodeVarint fun len => pps_takeExact len.toNat)

private theorem pps_mergeRepeatedBytes (wt : WireType) (vals : List Bytes) :
    ProtoPrefixStep (Proto.mergeRepeatedBytes wt vals) :=
  pps_map (fun b => vals ++ [b]) (pps_mergeBytes wt)

private theorem pps_pure {α : Type} (r : Except DecodeErr α) :
    ProtoPrefixStep (fun bs => do let v ← r; .ok (v, bs)) := by
  cases r with
  | ok v => exact pps_ok v
  | error e => exact pps_err e

private theorem pps_mergeMessage {M : Type} (mf : MergeFieldFn M) (wt : WireType) (m : M) (depth : Nat) :
    ProtoPrefixStep (fun bs => Proto.mergeMessage mf wt m bs depth) := by
  unfold Proto.mergeMessage
  refine pps_guard (Proto.checkWireType .lengthDelimited wt) ?_
  cases depth with
  | zero => exact pps_err .recursionLimitExceeded
  | succ depth' =>
    exact pps_congr
      (pps_seq pps_decodeVarint fun len =>
        pps_seq (pps_takeExact len.toNat) fun sub =>
          pps_pure (Proto.mergeFieldsLoop mf sub.length m sub depth'))
      (fun bs => by
        change Except.bind (Proto.decodeVarint bs) _ = Except.bind (Proto.decodeVarint bs) _
        cases Proto.decodeVarint bs with
        | error _ => rfl
        | ok lr =>
          rcases lr with ⟨len, rest⟩
          dsimp only [Except.bind])

private theorem pps_mergeOptMessage {M : Type} [Inhabited M] (mf : MergeFieldFn M) (wt : WireType)
    (opt : Option M) (depth : Nat) :
    ProtoPrefixStep (fun bs => Proto.mergeOptMessage mf wt opt bs depth) :=
  pps_map some (pps_mergeMessage mf wt (opt.getD default) depth)

/-! ### Private leaf and `Unchunked.*` `LoopsTo` helpers -/

private theorem prefixOk_authenticator : PrefixOk ProtoAuthenticator.mergeField := by
  intro m tag wt depth; unfold ProtoAuthenticator.mergeField
  split
  · exact pps_map (fun v => { m with rootKey := v }) (pps_mergeBytes wt)
  · split
    · exact pps_map (fun v => { m with macKey := v }) (pps_mergeBytes wt)
    · exact pps_skipField m wt tag depth

private theorem loopsTo_authenticator (m : ProtoAuthenticator)
    (h : (ProtoAuthenticator.encodeRaw m).length < 2 ^ 64) :
    LoopsTo ProtoAuthenticator.mergeField 0 default (ProtoAuthenticator.encodeRaw m) m := by
  have h1 := len_encodeBytesField (len_append_left h)
  have h2 := len_encodeBytesField (len_append_right h)
  have s1 := loopsTo_bytes ProtoAuthenticator.mergeField 0 default 1#32 m.rootKey
    (fun x => { (default : ProtoAuthenticator) with rootKey := x }) (by decide) (by decide) rfl h1 (fun _ _ _ => rfl)
  have s2 := loopsTo_bytes ProtoAuthenticator.mergeField 0 { (default : ProtoAuthenticator) with rootKey := m.rootKey } 2#32 m.macKey
    (fun x => { rootKey := m.rootKey, macKey := x }) (by decide) (by decide) rfl h2 (fun _ _ _ => rfl)
  exact (LoopsTo.append prefixOk_authenticator s1 s2).congr_res (by cases m; rfl)

private theorem prefixOk_polyEncoder : PrefixOk PolynomialEncoder.mergeField := by
  intro m tag wt depth; unfold PolynomialEncoder.mergeField
  split
  · exact pps_map (fun v => { m with idx := v }) (pps_mergeUint32 wt)
  · split
    · exact pps_map (fun v => { m with pts := v }) (pps_mergeRepeatedBytes wt m.pts)
    · split
      · exact pps_map (fun v => { m with polys := v }) (pps_mergeRepeatedBytes wt m.polys)
      · exact pps_skipField m wt tag depth

private theorem loopsTo_polyEncoder (m : PolynomialEncoder)
    (h : (PolynomialEncoder.encodeRaw m).length < 2 ^ 64) :
    LoopsTo PolynomialEncoder.mergeField 0 default (PolynomialEncoder.encodeRaw m) m := by
  have h12 := len_append_left h
  have h3 := len_encodeRepeatedBytes (len_append_right h)
  have h2 := len_encodeRepeatedBytes (len_append_right h12)
  have s1 := loopsTo_uint32 PolynomialEncoder.mergeField 0 default 1#32 m.idx
    (fun x => { (default : PolynomialEncoder) with idx := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_repeatedBytes PolynomialEncoder.mergeField prefixOk_polyEncoder 0
    { (default : PolynomialEncoder) with idx := m.idx } 2#32 m.pts
    PolynomialEncoder.pts (fun m' l => { m' with pts := l })
    (by decide) (by decide) h2 (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
  have s3 := loopsTo_repeatedBytes PolynomialEncoder.mergeField prefixOk_polyEncoder 0
    { idx := m.idx, pts := m.pts, polys := [] } 3#32 m.polys
    PolynomialEncoder.polys (fun m' l => { m' with polys := l })
    (by decide) (by decide) h3 (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
  exact (LoopsTo.append prefixOk_polyEncoder (LoopsTo.append prefixOk_polyEncoder s1 s2) s3).congr_res (by cases m; rfl)

private theorem loopsTo_uc_keysUnsampled (m : V1State.Unchunked.KeysUnsampled)
    (h : (V1State.Unchunked.KeysUnsampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.KeysUnsampled.mergeField 1 default (V1State.Unchunked.KeysUnsampled.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.KeysUnsampled.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.KeysUnsampled.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · exact pps_skipField m' wt tag depth
  have h2 := len_append_right h
  have s1 := loopsTo_uint64 V1State.Unchunked.KeysUnsampled.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.KeysUnsampled) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.KeysUnsampled.mergeField 1
    { epoch := m.epoch, auth := none } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

private theorem loopsTo_uc_headerSent (m : V1State.Unchunked.HeaderSent)
    (h : (V1State.Unchunked.HeaderSent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.HeaderSent.mergeField 1 default (V1State.Unchunked.HeaderSent.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.HeaderSent.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.HeaderSent.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with ek := v }) (pps_mergeBytes wt)
        · split
          · exact pps_map (fun v => { m' with dk := v }) (pps_mergeBytes wt)
          · exact pps_skipField m' wt tag depth
  have h123 := len_append_left h
  have h4 := len_encodeBytesField (len_append_right h)
  have h12 := len_append_left h123
  have h3 := len_encodeBytesField (len_append_right h123)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.HeaderSent.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.HeaderSent) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.HeaderSent.mergeField 1
    { epoch := m.epoch, auth := none, ek := [], dk := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, ek := [], dk := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.HeaderSent.mergeField 1
    { epoch := m.epoch, auth := m.auth, ek := [], dk := [] } 3#32 m.ek
    (fun x => { epoch := m.epoch, auth := m.auth, ek := x, dk := [] }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  have s4 := loopsTo_bytes V1State.Unchunked.HeaderSent.mergeField 1
    { epoch := m.epoch, auth := m.auth, ek := m.ek, dk := [] } 4#32 m.dk
    (fun x => { epoch := m.epoch, auth := m.auth, ek := m.ek, dk := x }) (by decide) (by decide) rfl h4 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3) s4).congr_res (by cases m; rfl)

theorem loopsTo_ch_keysUnsampled (m : V1State.Chunked.KeysUnsampled) (h : (V1State.Chunked.KeysUnsampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.KeysUnsampled.mergeField 2 default (V1State.Chunked.KeysUnsampled.encodeRaw m) m := by
  exact (loopsTo_optMessage V1State.Chunked.KeysUnsampled.mergeField 2 default 1#32
    V1State.Unchunked.KeysUnsampled.mergeField 1 V1State.Unchunked.KeysUnsampled.encodeRaw m.uc
    (fun x => { uc := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_keysUnsampled n (len_encodeOptMessage h n hn), len_encodeOptMessage h n hn⟩)
    (fun _ _ _ => rfl)).congr_res (by cases m; rfl)

theorem decode_ch_keysUnsampled (m : V1State.Chunked.KeysUnsampled) (h : (V1State.Chunked.KeysUnsampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.KeysUnsampled.decode (V1State.Chunked.KeysUnsampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.KeysUnsampled.mergeField 2 _ m (by decide) (loopsTo_ch_keysUnsampled m h)

theorem loopsTo_ch_keysSampled (m : V1State.Chunked.KeysSampled) (h : (V1State.Chunked.KeysSampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.KeysSampled.mergeField 2 default (V1State.Chunked.KeysSampled.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.KeysSampled.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.KeysSampled.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.HeaderSent.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingHdr := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingHdr depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.KeysSampled.mergeField 2 default 1#32
    V1State.Unchunked.HeaderSent.mergeField 1 V1State.Unchunked.HeaderSent.encodeRaw m.uc
    (fun x => { uc := x, sendingHdr := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_headerSent n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.KeysSampled.mergeField 2
    { uc := m.uc, sendingHdr := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingHdr
    (fun x => { uc := m.uc, sendingHdr := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_keysSampled (m : V1State.Chunked.KeysSampled) (h : (V1State.Chunked.KeysSampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.KeysSampled.decode (V1State.Chunked.KeysSampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.KeysSampled.mergeField 2 _ m (by decide) (loopsTo_ch_keysSampled m h)

private theorem prefixOk_polyDecoder : PrefixOk PolynomialDecoder.mergeField := by
  intro m tag wt depth; unfold PolynomialDecoder.mergeField
  split
  · exact pps_map (fun v => { m with ptsNeeded := v }) (pps_mergeUint32 wt)
  · split
    · exact pps_map (fun v => { m with polys := v }) (pps_mergeUint32 wt)
    · split
      · exact pps_map (fun v => { m with pts := v }) (pps_mergeRepeatedBytes wt m.pts)
      · split
        · exact pps_map (fun v => { m with isComplete := v }) (pps_mergeBool wt)
        · exact pps_skipField m wt tag depth

private theorem loopsTo_polyDecoder (m : PolynomialDecoder)
    (h : (PolynomialDecoder.encodeRaw m).length < 2 ^ 64) :
    LoopsTo PolynomialDecoder.mergeField 0 default (PolynomialDecoder.encodeRaw m) m := by
  have h123 := len_append_left h
  have h3 := len_encodeRepeatedBytes (len_append_right h123)
  have s1 := loopsTo_uint32 PolynomialDecoder.mergeField 0 default 1#32 m.ptsNeeded
    (fun x => { (default : PolynomialDecoder) with ptsNeeded := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_uint32 PolynomialDecoder.mergeField 0
    { ptsNeeded := m.ptsNeeded, polys := 0#32, pts := [], isComplete := false } 2#32 m.polys
    (fun x => { ptsNeeded := m.ptsNeeded, polys := x, pts := [], isComplete := false }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s3 := loopsTo_repeatedBytes PolynomialDecoder.mergeField prefixOk_polyDecoder 0
    { ptsNeeded := m.ptsNeeded, polys := m.polys, pts := [], isComplete := false } 3#32 m.pts
    PolynomialDecoder.pts (fun m' l => { m' with pts := l })
    (by decide) (by decide) h3 (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
  have s4 := loopsTo_bool PolynomialDecoder.mergeField 0
    { ptsNeeded := m.ptsNeeded, polys := m.polys, pts := m.pts, isComplete := false } 4#32 m.isComplete
    (fun x => { ptsNeeded := m.ptsNeeded, polys := m.polys, pts := m.pts, isComplete := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  exact (LoopsTo.append prefixOk_polyDecoder (LoopsTo.append prefixOk_polyDecoder (LoopsTo.append prefixOk_polyDecoder s1 s2) s3) s4).congr_res (by cases m; rfl)

private theorem loopsTo_uc_ekSent (m : V1State.Unchunked.EkSent)
    (h : (V1State.Unchunked.EkSent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.EkSent.mergeField 1 default (V1State.Unchunked.EkSent.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.EkSent.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.EkSent.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with dk := v }) (pps_mergeBytes wt)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_encodeBytesField (len_append_right h)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.EkSent.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.EkSent) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.EkSent.mergeField 1
    { epoch := m.epoch, auth := none, dk := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, dk := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.EkSent.mergeField 1
    { epoch := m.epoch, auth := m.auth, dk := [] } 3#32 m.dk
    (fun x => { epoch := m.epoch, auth := m.auth, dk := x }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3).congr_res (by cases m; rfl)

private theorem loopsTo_uc_ekSentCt1Received (m : V1State.Unchunked.EkSentCt1Received)
    (h : (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.EkSentCt1Received.mergeField 1 default (V1State.Unchunked.EkSentCt1Received.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.EkSentCt1Received.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.EkSentCt1Received.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with dk := v }) (pps_mergeBytes wt)
        · split
          · exact pps_map (fun v => { m' with ct1 := v }) (pps_mergeBytes wt)
          · exact pps_skipField m' wt tag depth
  have h123 := len_append_left h
  have h4 := len_encodeBytesField (len_append_right h)
  have h12 := len_append_left h123
  have h3 := len_encodeBytesField (len_append_right h123)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.EkSentCt1Received.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.EkSentCt1Received) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.EkSentCt1Received.mergeField 1
    { epoch := m.epoch, auth := none, dk := [], ct1 := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, dk := [], ct1 := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.EkSentCt1Received.mergeField 1
    { epoch := m.epoch, auth := m.auth, dk := [], ct1 := [] } 3#32 m.dk
    (fun x => { epoch := m.epoch, auth := m.auth, dk := x, ct1 := [] }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  have s4 := loopsTo_bytes V1State.Unchunked.EkSentCt1Received.mergeField 1
    { epoch := m.epoch, auth := m.auth, dk := m.dk, ct1 := [] } 4#32 m.ct1
    (fun x => { epoch := m.epoch, auth := m.auth, dk := m.dk, ct1 := x }) (by decide) (by decide) rfl h4 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3) s4).congr_res (by cases m; rfl)

private theorem loopsTo_uc_noHeaderReceived (m : V1State.Unchunked.NoHeaderReceived)
    (h : (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.NoHeaderReceived.mergeField 1 default (V1State.Unchunked.NoHeaderReceived.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.NoHeaderReceived.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.NoHeaderReceived.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · exact pps_skipField m' wt tag depth
  have h2 := len_append_right h
  have s1 := loopsTo_uint64 V1State.Unchunked.NoHeaderReceived.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.NoHeaderReceived) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.NoHeaderReceived.mergeField 1
    { epoch := m.epoch, auth := none } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

private theorem loopsTo_uc_headerReceived (m : V1State.Unchunked.HeaderReceived)
    (h : (V1State.Unchunked.HeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.HeaderReceived.mergeField 1 default (V1State.Unchunked.HeaderReceived.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.HeaderReceived.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.HeaderReceived.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with hdr := v }) (pps_mergeBytes wt)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_encodeBytesField (len_append_right h)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.HeaderReceived.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.HeaderReceived) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.HeaderReceived.mergeField 1
    { epoch := m.epoch, auth := none, hdr := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, hdr := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.HeaderReceived.mergeField 1
    { epoch := m.epoch, auth := m.auth, hdr := [] } 3#32 m.hdr
    (fun x => { epoch := m.epoch, auth := m.auth, hdr := x }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3).congr_res (by cases m; rfl)

private theorem loopsTo_uc_ct1Sent (m : V1State.Unchunked.Ct1Sent)
    (h : (V1State.Unchunked.Ct1Sent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct1Sent.mergeField 1 default (V1State.Unchunked.Ct1Sent.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.Ct1Sent.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.Ct1Sent.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with hdr := v }) (pps_mergeBytes wt)
        · split
          · exact pps_map (fun v => { m' with es := v }) (pps_mergeBytes wt)
          · split
            · exact pps_map (fun v => { m' with ct1 := v }) (pps_mergeBytes wt)
            · exact pps_skipField m' wt tag depth
  have h1234 := len_append_left h
  have h5 := len_encodeBytesField (len_append_right h)
  have h123 := len_append_left h1234
  have h4 := len_encodeBytesField (len_append_right h1234)
  have h12 := len_append_left h123
  have h3 := len_encodeBytesField (len_append_right h123)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.Ct1Sent.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.Ct1Sent) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.Ct1Sent.mergeField 1
    { epoch := m.epoch, auth := none, hdr := [], es := [], ct1 := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, hdr := [], es := [], ct1 := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1
    { epoch := m.epoch, auth := m.auth, hdr := [], es := [], ct1 := [] } 3#32 m.hdr
    (fun x => { epoch := m.epoch, auth := m.auth, hdr := x, es := [], ct1 := [] }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  have s4 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1
    { epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := [], ct1 := [] } 4#32 m.es
    (fun x => { epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := x, ct1 := [] }) (by decide) (by decide) rfl h4 (fun _ _ _ => rfl)
  have s5 := loopsTo_bytes V1State.Unchunked.Ct1Sent.mergeField 1
    { epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := m.es, ct1 := [] } 5#32 m.ct1
    (fun x => { epoch := m.epoch, auth := m.auth, hdr := m.hdr, es := m.es, ct1 := x }) (by decide) (by decide) rfl h5 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3) s4) s5).congr_res (by cases m; rfl)

private theorem loopsTo_uc_ct1SentEkReceived (m : V1State.Unchunked.Ct1SentEkReceived)
    (h : (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct1SentEkReceived.mergeField 1 default (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.Ct1SentEkReceived.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.Ct1SentEkReceived.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · split
        · exact pps_map (fun v => { m' with es := v }) (pps_mergeBytes wt)
        · split
          · exact pps_map (fun v => { m' with ek := v }) (pps_mergeBytes wt)
          · split
            · exact pps_map (fun v => { m' with ct1 := v }) (pps_mergeBytes wt)
            · exact pps_skipField m' wt tag depth
  have h1234 := len_append_left h
  have h5 := len_encodeBytesField (len_append_right h)
  have h123 := len_append_left h1234
  have h4 := len_encodeBytesField (len_append_right h1234)
  have h12 := len_append_left h123
  have h3 := len_encodeBytesField (len_append_right h123)
  have h2 := len_append_right h12
  have s1 := loopsTo_uint64 V1State.Unchunked.Ct1SentEkReceived.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.Ct1SentEkReceived) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.Ct1SentEkReceived.mergeField 1
    { epoch := m.epoch, auth := none, es := [], ek := [], ct1 := [] } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x, es := [], ek := [], ct1 := [] }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1
    { epoch := m.epoch, auth := m.auth, es := [], ek := [], ct1 := [] } 3#32 m.es
    (fun x => { epoch := m.epoch, auth := m.auth, es := x, ek := [], ct1 := [] }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  have s4 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1
    { epoch := m.epoch, auth := m.auth, es := m.es, ek := [], ct1 := [] } 4#32 m.ek
    (fun x => { epoch := m.epoch, auth := m.auth, es := m.es, ek := x, ct1 := [] }) (by decide) (by decide) rfl h4 (fun _ _ _ => rfl)
  have s5 := loopsTo_bytes V1State.Unchunked.Ct1SentEkReceived.mergeField 1
    { epoch := m.epoch, auth := m.auth, es := m.es, ek := m.ek, ct1 := [] } 5#32 m.ct1
    (fun x => { epoch := m.epoch, auth := m.auth, es := m.es, ek := m.ek, ct1 := x }) (by decide) (by decide) rfl h5 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3) s4) s5).congr_res (by cases m; rfl)

private theorem loopsTo_uc_ct2Sent (m : V1State.Unchunked.Ct2Sent)
    (h : (V1State.Unchunked.Ct2Sent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Unchunked.Ct2Sent.mergeField 1 default (V1State.Unchunked.Ct2Sent.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Unchunked.Ct2Sent.mergeField := by
    intro m' tag wt depth; unfold V1State.Unchunked.Ct2Sent.mergeField
    split
    · exact pps_map (fun v => { m' with epoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with auth := v }) (pps_mergeOptMessage ProtoAuthenticator.mergeField wt m'.auth depth)
      · exact pps_skipField m' wt tag depth
  have h2 := len_append_right h
  have s1 := loopsTo_uint64 V1State.Unchunked.Ct2Sent.mergeField 1 default 1#32 m.epoch
    (fun x => { (default : V1State.Unchunked.Ct2Sent) with epoch := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Unchunked.Ct2Sent.mergeField 1
    { epoch := m.epoch, auth := none } 2#32 ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw m.auth
    (fun x => { epoch := m.epoch, auth := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_authenticator n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem loopsTo_ch_headerSent (m : V1State.Chunked.HeaderSent) (h : (V1State.Chunked.HeaderSent.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.HeaderSent.mergeField 2 default (V1State.Chunked.HeaderSent.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.HeaderSent.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.HeaderSent.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.EkSent.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingEk := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingEk depth)
      · split
        · exact pps_map (fun v => { m' with receivingCt1 := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingCt1 depth)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_append_right h
  have h1 := len_append_left h12
  have h2 := len_append_right h12
  have s1 := loopsTo_optMessage V1State.Chunked.HeaderSent.mergeField 2 default 1#32
    V1State.Unchunked.EkSent.mergeField 1 V1State.Unchunked.EkSent.encodeRaw m.uc
    (fun x => { uc := x, sendingEk := none, receivingCt1 := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ekSent n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.HeaderSent.mergeField 2
    { uc := m.uc, sendingEk := none, receivingCt1 := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingEk
    (fun x => { uc := m.uc, sendingEk := x, receivingCt1 := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_optMessage V1State.Chunked.HeaderSent.mergeField 2
    { uc := m.uc, sendingEk := m.sendingEk, receivingCt1 := none } 3#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingCt1
    (fun x => { uc := m.uc, sendingEk := m.sendingEk, receivingCt1 := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h3 n hn), len_encodeOptMessage h3 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3).congr_res (by cases m; rfl)

theorem decode_ch_headerSent (m : V1State.Chunked.HeaderSent) (h : (V1State.Chunked.HeaderSent.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.HeaderSent.decode (V1State.Chunked.HeaderSent.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.HeaderSent.mergeField 2 _ m (by decide) (loopsTo_ch_headerSent m h)

theorem loopsTo_ch_ct1Received (m : V1State.Chunked.Ct1Received) (h : (V1State.Chunked.Ct1Received.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.Ct1Received.mergeField 2 default (V1State.Chunked.Ct1Received.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.Ct1Received.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.Ct1Received.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.EkSentCt1Received.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingEk := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingEk depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.Ct1Received.mergeField 2 default 1#32
    V1State.Unchunked.EkSentCt1Received.mergeField 1 V1State.Unchunked.EkSentCt1Received.encodeRaw m.uc
    (fun x => { uc := x, sendingEk := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ekSentCt1Received n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.Ct1Received.mergeField 2
    { uc := m.uc, sendingEk := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingEk
    (fun x => { uc := m.uc, sendingEk := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_ct1Received (m : V1State.Chunked.Ct1Received) (h : (V1State.Chunked.Ct1Received.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.Ct1Received.decode (V1State.Chunked.Ct1Received.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.Ct1Received.mergeField 2 _ m (by decide) (loopsTo_ch_ct1Received m h)

theorem loopsTo_ch_ekSentCt1Received (m : V1State.Chunked.EkSentCt1Received) (h : (V1State.Chunked.EkSentCt1Received.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.EkSentCt1Received.mergeField 2 default (V1State.Chunked.EkSentCt1Received.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.EkSentCt1Received.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.EkSentCt1Received.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.EkSentCt1Received.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with receivingCt2 := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingCt2 depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.EkSentCt1Received.mergeField 2 default 1#32
    V1State.Unchunked.EkSentCt1Received.mergeField 1 V1State.Unchunked.EkSentCt1Received.encodeRaw m.uc
    (fun x => { uc := x, receivingCt2 := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ekSentCt1Received n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.EkSentCt1Received.mergeField 2
    { uc := m.uc, receivingCt2 := none } 3#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingCt2
    (fun x => { uc := m.uc, receivingCt2 := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_ekSentCt1Received (m : V1State.Chunked.EkSentCt1Received) (h : (V1State.Chunked.EkSentCt1Received.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.EkSentCt1Received.decode (V1State.Chunked.EkSentCt1Received.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.EkSentCt1Received.mergeField 2 _ m (by decide) (loopsTo_ch_ekSentCt1Received m h)

theorem loopsTo_ch_noHeaderReceived (m : V1State.Chunked.NoHeaderReceived) (h : (V1State.Chunked.NoHeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.NoHeaderReceived.mergeField 2 default (V1State.Chunked.NoHeaderReceived.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.NoHeaderReceived.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.NoHeaderReceived.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.NoHeaderReceived.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with receivingHdr := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingHdr depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.NoHeaderReceived.mergeField 2 default 1#32
    V1State.Unchunked.NoHeaderReceived.mergeField 1 V1State.Unchunked.NoHeaderReceived.encodeRaw m.uc
    (fun x => { uc := x, receivingHdr := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_noHeaderReceived n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.NoHeaderReceived.mergeField 2
    { uc := m.uc, receivingHdr := none } 2#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingHdr
    (fun x => { uc := m.uc, receivingHdr := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_noHeaderReceived (m : V1State.Chunked.NoHeaderReceived) (h : (V1State.Chunked.NoHeaderReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.NoHeaderReceived.decode (V1State.Chunked.NoHeaderReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.NoHeaderReceived.mergeField 2 _ m (by decide) (loopsTo_ch_noHeaderReceived m h)

theorem loopsTo_ch_headerReceived (m : V1State.Chunked.HeaderReceived) (h : (V1State.Chunked.HeaderReceived.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.HeaderReceived.mergeField 2 default (V1State.Chunked.HeaderReceived.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.HeaderReceived.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.HeaderReceived.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.HeaderReceived.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with receivingEk := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingEk depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.HeaderReceived.mergeField 2 default 1#32
    V1State.Unchunked.HeaderReceived.mergeField 1 V1State.Unchunked.HeaderReceived.encodeRaw m.uc
    (fun x => { uc := x, receivingEk := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_headerReceived n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.HeaderReceived.mergeField 2
    { uc := m.uc, receivingEk := none } 2#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingEk
    (fun x => { uc := m.uc, receivingEk := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_headerReceived (m : V1State.Chunked.HeaderReceived) (h : (V1State.Chunked.HeaderReceived.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.HeaderReceived.decode (V1State.Chunked.HeaderReceived.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.HeaderReceived.mergeField 2 _ m (by decide) (loopsTo_ch_headerReceived m h)

theorem loopsTo_ch_ct1Sampled (m : V1State.Chunked.Ct1Sampled) (h : (V1State.Chunked.Ct1Sampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.Ct1Sampled.mergeField 2 default (V1State.Chunked.Ct1Sampled.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.Ct1Sampled.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.Ct1Sampled.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.Ct1Sent.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingCt1 := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingCt1 depth)
      · split
        · exact pps_map (fun v => { m' with receivingEk := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingEk depth)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_append_right h
  have h1 := len_append_left h12
  have h2 := len_append_right h12
  have s1 := loopsTo_optMessage V1State.Chunked.Ct1Sampled.mergeField 2 default 1#32
    V1State.Unchunked.Ct1Sent.mergeField 1 V1State.Unchunked.Ct1Sent.encodeRaw m.uc
    (fun x => { uc := x, sendingCt1 := none, receivingEk := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ct1Sent n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.Ct1Sampled.mergeField 2
    { uc := m.uc, sendingCt1 := none, receivingEk := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingCt1
    (fun x => { uc := m.uc, sendingCt1 := x, receivingEk := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s3 := loopsTo_optMessage V1State.Chunked.Ct1Sampled.mergeField 2
    { uc := m.uc, sendingCt1 := m.sendingCt1, receivingEk := none } 3#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingEk
    (fun x => { uc := m.uc, sendingCt1 := m.sendingCt1, receivingEk := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h3 n hn), len_encodeOptMessage h3 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3).congr_res (by cases m; rfl)

theorem decode_ch_ct1Sampled (m : V1State.Chunked.Ct1Sampled) (h : (V1State.Chunked.Ct1Sampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.Ct1Sampled.decode (V1State.Chunked.Ct1Sampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.Ct1Sampled.mergeField 2 _ m (by decide) (loopsTo_ch_ct1Sampled m h)

theorem loopsTo_ch_ekReceivedCt1Sampled (m : V1State.Chunked.EkReceivedCt1Sampled) (h : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.EkReceivedCt1Sampled.mergeField 2 default (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.EkReceivedCt1Sampled.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.Ct1SentEkReceived.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingCt1 := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingCt1 depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField 2 default 1#32
    V1State.Unchunked.Ct1SentEkReceived.mergeField 1 V1State.Unchunked.Ct1SentEkReceived.encodeRaw m.uc
    (fun x => { uc := x, sendingCt1 := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ct1SentEkReceived n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField 2
    { uc := m.uc, sendingCt1 := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingCt1
    (fun x => { uc := m.uc, sendingCt1 := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_ekReceivedCt1Sampled (m : V1State.Chunked.EkReceivedCt1Sampled) (h : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.EkReceivedCt1Sampled.decode (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.EkReceivedCt1Sampled.mergeField 2 _ m (by decide) (loopsTo_ch_ekReceivedCt1Sampled m h)

theorem loopsTo_ch_ct1Acknowledged (m : V1State.Chunked.Ct1Acknowledged) (h : (V1State.Chunked.Ct1Acknowledged.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.Ct1Acknowledged.mergeField 2 default (V1State.Chunked.Ct1Acknowledged.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.Ct1Acknowledged.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.Ct1Acknowledged.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.Ct1Sent.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with receivingEk := v }) (pps_mergeOptMessage PolynomialDecoder.mergeField wt m'.receivingEk depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.Ct1Acknowledged.mergeField 2 default 1#32
    V1State.Unchunked.Ct1Sent.mergeField 1 V1State.Unchunked.Ct1Sent.encodeRaw m.uc
    (fun x => { uc := x, receivingEk := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ct1Sent n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.Ct1Acknowledged.mergeField 2
    { uc := m.uc, receivingEk := none } 2#32
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw m.receivingEk
    (fun x => { uc := m.uc, receivingEk := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyDecoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_ct1Acknowledged (m : V1State.Chunked.Ct1Acknowledged) (h : (V1State.Chunked.Ct1Acknowledged.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.Ct1Acknowledged.decode (V1State.Chunked.Ct1Acknowledged.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.Ct1Acknowledged.mergeField 2 _ m (by decide) (loopsTo_ch_ct1Acknowledged m h)

theorem loopsTo_ch_ct2Sampled (m : V1State.Chunked.Ct2Sampled) (h : (V1State.Chunked.Ct2Sampled.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.Chunked.Ct2Sampled.mergeField 2 default (V1State.Chunked.Ct2Sampled.encodeRaw m) m := by
  have hpre : PrefixOk V1State.Chunked.Ct2Sampled.mergeField := by
    intro m' tag wt depth; unfold V1State.Chunked.Ct2Sampled.mergeField
    split
    · exact pps_map (fun v => { m' with uc := v }) (pps_mergeOptMessage V1State.Unchunked.Ct2Sent.mergeField wt m'.uc depth)
    · split
      · exact pps_map (fun v => { m' with sendingCt2 := v }) (pps_mergeOptMessage PolynomialEncoder.mergeField wt m'.sendingCt2 depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage V1State.Chunked.Ct2Sampled.mergeField 2 default 1#32
    V1State.Unchunked.Ct2Sent.mergeField 1 V1State.Unchunked.Ct2Sent.encodeRaw m.uc
    (fun x => { uc := x, sendingCt2 := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_uc_ct2Sent n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage V1State.Chunked.Ct2Sampled.mergeField 2
    { uc := m.uc, sendingCt2 := none } 2#32
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw m.sendingCt2
    (fun x => { uc := m.uc, sendingCt2 := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_polyEncoder n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

theorem decode_ch_ct2Sampled (m : V1State.Chunked.Ct2Sampled) (h : (V1State.Chunked.Ct2Sampled.encodeRaw m).length < 2 ^ 64) :
    V1State.Chunked.Ct2Sampled.decode (V1State.Chunked.Ct2Sampled.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.Chunked.Ct2Sampled.mergeField 2 _ m (by decide) (loopsTo_ch_ct2Sampled m h)

end CryptoVerification.SpqrV1Sync.Codec
