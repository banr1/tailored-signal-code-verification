/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
public import ProofLib

/-!
# Prost Round-Trip for `V1State` and `PqRatchetState`

`LoopsTo` and round-trip decode theorems for `V1State` (depth 3), `PqRatchetState` (depth 4),
`Proto.decodeState`, `Proto.spqrDecodeState`, and `Top.decodeState (spqrDeps F K)`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)
open CryptoVerification.SpqrV1.Prost.MessageMerge (ProtoPrefixStep)
open CryptoGames.LibsignalSession (ShaCompress)

/-! ### Private `ProtoPrefixStep`, length, and sub-message helpers -/

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

private theorem len_encodeMessage {N : Type} {enc : N → Bytes} {tag : BitVec 32} {n : N} {B : Nat}
    (h : (Proto.encodeMessage enc tag n).length < B) : (enc n).length < B := by
  simp only [Proto.encodeMessage, List.length_append] at h
  omega

private theorem len_encodeOptMessage {N : Type} {enc : N → Bytes} {tag : BitVec 32} {o : Option N} {B : Nat}
    (h : (Proto.encodeOptMessage enc tag o).length < B) (n : N) (ho : o = some n) :
    (enc n).length < B := by
  subst ho
  exact len_encodeMessage h

private theorem len_encodeRepeatedMessage {N : Type} {enc : N → Bytes} {tag : BitVec 32} {ns : List N} {B : Nat}
    (h : (Proto.encodeRepeatedMessage enc tag ns).length < B) : ∀ n ∈ ns, (enc n).length < B := by
  induction ns with
  | nil => intro _ hn; cases hn
  | cons w ws ih =>
    have hcons : Proto.encodeRepeatedMessage enc tag (w :: ws) =
        Proto.encodeMessage enc tag w ++ Proto.encodeRepeatedMessage enc tag ws := rfl
    rw [hcons] at h
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hmem
    · exact len_encodeMessage (len_append_left h)
    · exact ih (len_append_right h) n hmem

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

private theorem pps_pure {α : Type} (r : Except DecodeErr α) :
    ProtoPrefixStep (fun bs => do let v ← r; .ok (v, bs)) := by
  cases r with
  | ok v => exact pps_ok v
  | error e => exact pps_err e

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

private theorem pps_mergeInt32 (wt : WireType) : ProtoPrefixStep (Proto.mergeInt32 wt) :=
  pps_guard (Proto.checkWireType .varint wt) (pps_map (fun v => v.truncate 32) pps_decodeVarint)

private theorem pps_mergeBytes (wt : WireType) : ProtoPrefixStep (Proto.mergeBytes wt) :=
  pps_guard (Proto.checkWireType .lengthDelimited wt) (pps_seq pps_decodeVarint fun len => pps_takeExact len.toNat)

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

private theorem pps_mergeRepeatedMessage {M : Type} [Inhabited M] (mf : MergeFieldFn M) (wt : WireType)
    (ms : List M) (depth : Nat) :
    ProtoPrefixStep (fun bs => Proto.mergeRepeatedMessage mf wt ms bs depth) :=
  pps_map (fun m' => ms ++ [m']) (pps_mergeMessage mf wt default depth)

private theorem pps_pqInner_merge (cur : Option PqRatchetState.Inner) (tag : BitVec 32) (wt : WireType) (depth : Nat) :
    ProtoPrefixStep (fun bs => PqRatchetState.Inner.merge cur tag wt bs depth) := by
  unfold PqRatchetState.Inner.merge
  split
  · exact pps_map (fun v => some (PqRatchetState.Inner.v1 v))
      (pps_mergeMessage V1State.mergeField wt (match cur with | some (.v1 v) => v | none => default) depth)
  · exact pps_skipField cur wt tag depth

private theorem loopsTo_chainParams (m : ChainParamsPB) :
    LoopsTo ChainParamsPB.mergeField 0 default (ChainParamsPB.encodeRaw m) m := by
  have hpre : PrefixOk ChainParamsPB.mergeField := by
    intro m' tag wt depth; unfold ChainParamsPB.mergeField
    split
    · exact pps_map (fun v => { m' with maxJump := v }) (pps_mergeUint32 wt)
    · split
      · exact pps_map (fun v => { m' with maxOooKeys := v }) (pps_mergeUint32 wt)
      · exact pps_skipField m' wt tag depth
  have s1 := loopsTo_uint32 ChainParamsPB.mergeField 0 default 1#32 m.maxJump
    (fun x => { maxJump := x, maxOooKeys := 0#32 }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_uint32 ChainParamsPB.mergeField 0 { maxJump := m.maxJump, maxOooKeys := 0#32 } 2#32 m.maxOooKeys
    (fun x => { maxJump := m.maxJump, maxOooKeys := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

private theorem loopsTo_epochDirection (m : EpochDirectionPB)
    (h : (EpochDirectionPB.encodeRaw m).length < 2 ^ 64) :
    LoopsTo EpochDirectionPB.mergeField 0 default (EpochDirectionPB.encodeRaw m) m := by
  have hpre : PrefixOk EpochDirectionPB.mergeField := by
    intro m' tag wt depth; unfold EpochDirectionPB.mergeField
    split
    · exact pps_map (fun v => { m' with ctr := v }) (pps_mergeUint32 wt)
    · split
      · exact pps_map (fun v => { m' with next := v }) (pps_mergeBytes wt)
      · split
        · exact pps_map (fun v => { m' with prev := v }) (pps_mergeBytes wt)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_encodeBytesField (len_append_right h)
  have h2 := len_encodeBytesField (len_append_right h12)
  have s1 := loopsTo_uint32 EpochDirectionPB.mergeField 0 default 1#32 m.ctr
    (fun x => { ctr := x, next := [], prev := [] }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_bytes EpochDirectionPB.mergeField 0 { ctr := m.ctr, next := [], prev := [] } 2#32 m.next
    (fun x => { ctr := m.ctr, next := x, prev := [] }) (by decide) (by decide) rfl h2 (fun _ _ _ => rfl)
  have s3 := loopsTo_bytes EpochDirectionPB.mergeField 0 { ctr := m.ctr, next := m.next, prev := [] } 3#32 m.prev
    (fun x => { ctr := m.ctr, next := m.next, prev := x }) (by decide) (by decide) rfl h3 (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3).congr_res (by cases m; rfl)

private theorem loopsTo_chainEpoch (m : ChainEpochPB)
    (h : (ChainEpochPB.encodeRaw m).length < 2 ^ 64) :
    LoopsTo ChainEpochPB.mergeField 1 default (ChainEpochPB.encodeRaw m) m := by
  have hpre : PrefixOk ChainEpochPB.mergeField := by
    intro m' tag wt depth; unfold ChainEpochPB.mergeField
    split
    · exact pps_map (fun v => { m' with send := v }) (pps_mergeOptMessage EpochDirectionPB.mergeField wt m'.send depth)
    · split
      · exact pps_map (fun v => { m' with recv := v }) (pps_mergeOptMessage EpochDirectionPB.mergeField wt m'.recv depth)
      · exact pps_skipField m' wt tag depth
  have h1 := len_append_left h
  have h2 := len_append_right h
  have s1 := loopsTo_optMessage ChainEpochPB.mergeField 1 default 1#32
    EpochDirectionPB.mergeField 0 EpochDirectionPB.encodeRaw m.send
    (fun x => { send := x, recv := none }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_epochDirection n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage ChainEpochPB.mergeField 1 { send := m.send, recv := none } 2#32
    EpochDirectionPB.mergeField 0 EpochDirectionPB.encodeRaw m.recv
    (fun x => { send := m.send, recv := x }) (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_epochDirection n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre s1 s2).congr_res (by cases m; rfl)

private theorem prefixOk_chain : PrefixOk ChainPB.mergeField := by
  intro m' tag wt depth; unfold ChainPB.mergeField
  split
  · exact pps_map (fun v => { m' with direction := v }) (pps_mergeInt32 wt)
  · split
    · exact pps_map (fun v => { m' with currentEpoch := v }) (pps_mergeUint64 wt)
    · split
      · exact pps_map (fun v => { m' with links := v }) (pps_mergeRepeatedMessage ChainEpochPB.mergeField wt m'.links depth)
      · split
        · exact pps_map (fun v => { m' with nextRoot := v }) (pps_mergeBytes wt)
        · split
          · exact pps_map (fun v => { m' with sendEpoch := v }) (pps_mergeUint64 wt)
          · split
            · exact pps_map (fun v => { m' with params := v }) (pps_mergeOptMessage ChainParamsPB.mergeField wt m'.params depth)
            · exact pps_skipField m' wt tag depth

private theorem loopsTo_chain (m : ChainPB)
    (h : (ChainPB.encodeRaw m).length < 2 ^ 64) :
    LoopsTo ChainPB.mergeField 2 default (ChainPB.encodeRaw m) m := by
  have h12345 := len_append_left h
  have h6 := len_append_right h
  have h1234 := len_append_left h12345
  have h123 := len_append_left h1234
  have h4 := len_encodeBytesField (len_append_right h1234)
  have h3 := len_encodeRepeatedMessage (len_append_right h123)
  have s1 := loopsTo_int32 ChainPB.mergeField 2 default 1#32 m.direction
    (fun x => { (default : ChainPB) with direction := x }) (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s2 := loopsTo_uint64 ChainPB.mergeField 2
    { direction := m.direction, currentEpoch := 0#64, links := [], nextRoot := [], sendEpoch := 0#64, params := none } 2#32 m.currentEpoch
    (fun x => { direction := m.direction, currentEpoch := x, links := [], nextRoot := [], sendEpoch := 0#64, params := none })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s3 := loopsTo_repeatedMessage ChainPB.mergeField prefixOk_chain 2
    { direction := m.direction, currentEpoch := m.currentEpoch, links := [], nextRoot := [], sendEpoch := 0#64, params := none }
    3#32 ChainEpochPB.mergeField 1 ChainEpochPB.encodeRaw m.links
    ChainPB.links (fun m' l => { m' with links := l })
    (by decide) (by decide) (by decide)
    (fun n hn => ⟨loopsTo_chainEpoch n (h3 n hn), h3 n hn⟩)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
  have s4 := loopsTo_bytes ChainPB.mergeField 2
    { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := [], sendEpoch := 0#64, params := none }
    4#32 m.nextRoot
    (fun x => { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := x, sendEpoch := 0#64, params := none })
    (by decide) (by decide) rfl h4 (fun _ _ _ => rfl)
  have s5 := loopsTo_uint64 ChainPB.mergeField 2
    { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := m.nextRoot, sendEpoch := 0#64, params := none }
    5#32 m.sendEpoch
    (fun x => { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := m.nextRoot, sendEpoch := x, params := none })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s6 := loopsTo_optMessage ChainPB.mergeField 2
    { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := m.nextRoot, sendEpoch := m.sendEpoch, params := none }
    6#32 ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw m.params
    (fun x => { direction := m.direction, currentEpoch := m.currentEpoch, links := m.links, nextRoot := m.nextRoot, sendEpoch := m.sendEpoch, params := x })
    (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_chainParams n, len_encodeOptMessage h6 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append prefixOk_chain
    (LoopsTo.append prefixOk_chain
      (LoopsTo.append prefixOk_chain
        (LoopsTo.append prefixOk_chain
          (LoopsTo.append prefixOk_chain s1 s2) s3) s4) s5) s6).congr_res (by cases m; rfl)

private theorem loopsTo_versionNegotiation (m : VersionNegotiationPB)
    (h : (VersionNegotiationPB.encodeRaw m).length < 2 ^ 64) :
    LoopsTo VersionNegotiationPB.mergeField 1 default (VersionNegotiationPB.encodeRaw m) m := by
  have hpre : PrefixOk VersionNegotiationPB.mergeField := by
    intro m' tag wt depth; unfold VersionNegotiationPB.mergeField
    split
    · exact pps_map (fun v => { m' with authKey := v }) (pps_mergeBytes wt)
    · split
      · exact pps_map (fun v => { m' with direction := v }) (pps_mergeInt32 wt)
      · split
        · exact pps_map (fun v => { m' with minVersion := v }) (pps_mergeInt32 wt)
        · split
          · exact pps_map (fun v => { m' with chainParams := v }) (pps_mergeOptMessage ChainParamsPB.mergeField wt m'.chainParams depth)
          · exact pps_skipField m' wt tag depth
  have h123 := len_append_left h
  have h4 := len_append_right h
  have h12 := len_append_left h123
  have h1 := len_encodeBytesField (len_append_left h12)
  have s1 := loopsTo_bytes VersionNegotiationPB.mergeField 1 default 1#32 m.authKey
    (fun x => { authKey := x, direction := 0#32, minVersion := 0#32, chainParams := none })
    (by decide) (by decide) rfl h1 (fun _ _ _ => rfl)
  have s2 := loopsTo_int32 VersionNegotiationPB.mergeField 1
    { authKey := m.authKey, direction := 0#32, minVersion := 0#32, chainParams := none } 2#32 m.direction
    (fun x => { authKey := m.authKey, direction := x, minVersion := 0#32, chainParams := none })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s3 := loopsTo_int32 VersionNegotiationPB.mergeField 1
    { authKey := m.authKey, direction := m.direction, minVersion := 0#32, chainParams := none } 3#32 m.minVersion
    (fun x => { authKey := m.authKey, direction := m.direction, minVersion := x, chainParams := none })
    (by decide) (by decide) rfl (fun _ _ _ => rfl)
  have s4 := loopsTo_optMessage VersionNegotiationPB.mergeField 1
    { authKey := m.authKey, direction := m.direction, minVersion := m.minVersion, chainParams := none }
    4#32 ChainParamsPB.mergeField 0 ChainParamsPB.encodeRaw m.chainParams
    (fun x => { authKey := m.authKey, direction := m.direction, minVersion := m.minVersion, chainParams := x })
    (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_chainParams n, len_encodeOptMessage h4 n hn⟩)
    (fun _ _ _ => rfl)
  exact (LoopsTo.append hpre (LoopsTo.append hpre (LoopsTo.append hpre s1 s2) s3) s4).congr_res (by cases m; rfl)

/-! ### `V1State` and `PqRatchetState` round-trip theorems -/

theorem v1State_default_innerState : (default : V1State).innerState = none := rfl

theorem loopsTo_v1State (m : V1State) (h : (V1State.encodeRaw m).length < 2 ^ 64) :
    LoopsTo V1State.mergeField 3 default (V1State.encodeRaw m) m := by
  rcases m with ⟨innerState⟩
  cases innerState with
  | none => exact loopsTo_nil V1State.mergeField 3 default
  | some is =>
    cases is with
    | keysUnsampled v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 1#32
        V1State.Chunked.KeysUnsampled.mergeField 2 V1State.Chunked.KeysUnsampled.encodeRaw default v
        (fun x => { innerState := some (.keysUnsampled x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_keysUnsampled v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default bs depth <;> rfl)
    | keysSampled v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 2#32
        V1State.Chunked.KeysSampled.mergeField 2 V1State.Chunked.KeysSampled.encodeRaw default v
        (fun x => { innerState := some (.keysSampled x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_keysSampled v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField .lengthDelimited default bs depth <;> rfl)
    | headerSent v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 3#32
        V1State.Chunked.HeaderSent.mergeField 2 V1State.Chunked.HeaderSent.encodeRaw default v
        (fun x => { innerState := some (.headerSent x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_headerSent v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField .lengthDelimited default bs depth <;> rfl)
    | ct1Received v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 4#32
        V1State.Chunked.Ct1Received.mergeField 2 V1State.Chunked.Ct1Received.encodeRaw default v
        (fun x => { innerState := some (.ct1Received x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ct1Received v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.Ct1Received.mergeField .lengthDelimited default bs depth <;> rfl)
    | ekSentCt1Received v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 5#32
        V1State.Chunked.EkSentCt1Received.mergeField 2 V1State.Chunked.EkSentCt1Received.encodeRaw default v
        (fun x => { innerState := some (.ekSentCt1Received x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ekSentCt1Received v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.EkSentCt1Received.mergeField .lengthDelimited default bs depth <;> rfl)
    | noHeaderReceived v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 6#32
        V1State.Chunked.NoHeaderReceived.mergeField 2 V1State.Chunked.NoHeaderReceived.encodeRaw default v
        (fun x => { innerState := some (.noHeaderReceived x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_noHeaderReceived v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField .lengthDelimited default bs depth <;> rfl)
    | headerReceived v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 7#32
        V1State.Chunked.HeaderReceived.mergeField 2 V1State.Chunked.HeaderReceived.encodeRaw default v
        (fun x => { innerState := some (.headerReceived x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_headerReceived v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField .lengthDelimited default bs depth <;> rfl)
    | ct1Sampled v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 8#32
        V1State.Chunked.Ct1Sampled.mergeField 2 V1State.Chunked.Ct1Sampled.encodeRaw default v
        (fun x => { innerState := some (.ct1Sampled x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ct1Sampled v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField .lengthDelimited default bs depth <;> rfl)
    | ekReceivedCt1Sampled v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 9#32
        V1State.Chunked.EkReceivedCt1Sampled.mergeField 2 V1State.Chunked.EkReceivedCt1Sampled.encodeRaw default v
        (fun x => { innerState := some (.ekReceivedCt1Sampled x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ekReceivedCt1Sampled v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField .lengthDelimited default bs depth <;> rfl)
    | ct1Acknowledged v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 10#32
        V1State.Chunked.Ct1Acknowledged.mergeField 2 V1State.Chunked.Ct1Acknowledged.encodeRaw default v
        (fun x => { innerState := some (.ct1Acknowledged x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ct1Acknowledged v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField .lengthDelimited default bs depth <;> rfl)
    | ct2Sampled v =>
      have hv := len_encodeMessage h
      exact loopsTo_message V1State.mergeField 3 default 11#32
        V1State.Chunked.Ct2Sampled.mergeField 2 V1State.Chunked.Ct2Sampled.encodeRaw default v
        (fun x => { innerState := some (.ct2Sampled x) }) (by decide) (by decide) (by decide)
        (loopsTo_ch_ct2Sampled v hv) hv
        (fun depth bs _ => by
          change Except.bind (Except.bind (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField .lengthDelimited default bs depth) _) _ =
            Except.bind (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField .lengthDelimited default bs depth) _
          cases Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField .lengthDelimited default bs depth <;> rfl)

theorem decode_v1State (m : V1State) (h : (V1State.encodeRaw m).length < 2 ^ 64) :
    V1State.decode (V1State.encodeRaw m) = .ok m :=
  decodeTop_of_loopsTo V1State.mergeField 3 _ m (by decide) (loopsTo_v1State m h)

theorem loopsTo_pqInner_v1 (vn : Option VersionNegotiationPB) (ch : Option ChainPB) (v : V1State)
    (h : (Proto.encodeMessage V1State.encodeRaw 3#32 v).length < 2 ^ 64) :
    LoopsTo PqRatchetState.mergeField 4 { versionNegotiation := vn, chain := ch, inner := none }
      (Proto.encodeMessage V1State.encodeRaw 3#32 v)
      { versionNegotiation := vn, chain := ch, inner := some (.v1 v) } := by
  have hv := len_encodeMessage h
  exact loopsTo_message PqRatchetState.mergeField 4
    { versionNegotiation := vn, chain := ch, inner := none } 3#32
    V1State.mergeField 3 V1State.encodeRaw default v
    (fun x => { versionNegotiation := vn, chain := ch, inner := some (.v1 x) })
    (by decide) (by decide) (by decide) (loopsTo_v1State v hv) hv
    (fun depth bs _ => by
      change Except.bind (Except.bind (Proto.mergeMessage V1State.mergeField .lengthDelimited default bs depth) _) _ =
        Except.bind (Proto.mergeMessage V1State.mergeField .lengthDelimited default bs depth) _
      cases Proto.mergeMessage V1State.mergeField .lengthDelimited default bs depth <;> rfl)

theorem loopsTo_pqRatchetState (m : PqRatchetState)
    (h : (PqRatchetState.encodeRaw m).length < 2 ^ 64) :
    LoopsTo PqRatchetState.mergeField 4 default (PqRatchetState.encodeRaw m) m := by
  have hpre : PrefixOk PqRatchetState.mergeField := by
    intro m' tag wt depth; unfold PqRatchetState.mergeField
    split
    · exact pps_map (fun v => { m' with versionNegotiation := v })
        (pps_mergeOptMessage VersionNegotiationPB.mergeField wt m'.versionNegotiation depth)
    · split
      · exact pps_map (fun v => { m' with chain := v })
          (pps_mergeOptMessage ChainPB.mergeField wt m'.chain depth)
      · split
        · exact pps_map (fun v => { m' with inner := v })
            (pps_pqInner_merge m'.inner tag wt depth)
        · exact pps_skipField m' wt tag depth
  have h12 := len_append_left h
  have h3 := len_append_right h
  have h1 := len_append_left h12
  have h2 := len_append_right h12
  have s1 := loopsTo_optMessage PqRatchetState.mergeField 4 default 1#32
    VersionNegotiationPB.mergeField 1 VersionNegotiationPB.encodeRaw m.versionNegotiation
    (fun x => { versionNegotiation := x, chain := none, inner := none })
    (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_versionNegotiation n (len_encodeOptMessage h1 n hn), len_encodeOptMessage h1 n hn⟩)
    (fun _ _ _ => rfl)
  have s2 := loopsTo_optMessage PqRatchetState.mergeField 4
    { versionNegotiation := m.versionNegotiation, chain := none, inner := none } 2#32
    ChainPB.mergeField 2 ChainPB.encodeRaw m.chain
    (fun x => { versionNegotiation := m.versionNegotiation, chain := x, inner := none })
    (by decide) (by decide) (by decide) rfl
    (fun n hn => ⟨loopsTo_chain n (len_encodeOptMessage h2 n hn), len_encodeOptMessage h2 n hn⟩)
    (fun _ _ _ => rfl)
  have s12 := LoopsTo.append hpre s1 s2
  rcases m with ⟨vn, ch, inner⟩
  cases inner with
  | none =>
    exact LoopsTo.append hpre s12 (loopsTo_nil PqRatchetState.mergeField 4 _)
  | some inn =>
    cases inn with
    | v1 v =>
      exact LoopsTo.append hpre s12 (loopsTo_pqInner_v1 vn ch v h3)

/-- `Proto.decodeState` inverts `Proto.encodeState` when the encoded byte length fits in 64 bits. -/
theorem decodeState_encodeState (s : PqRatchetState) (h : (Proto.encodeState s).length < 2 ^ 64) :
    Proto.decodeState (Proto.encodeState s) = .ok s :=
  decodeTop_of_loopsTo PqRatchetState.mergeField 4 _ s (by decide) (loopsTo_pqRatchetState s h)

/-- Only the empty `PqRatchetState` encodes to `[]`. -/
theorem encodeState_eq_nil (s : PqRatchetState) (h : (Proto.encodeState s).length < 2 ^ 64)
    (he : Proto.encodeState s = []) : s = { versionNegotiation := none, chain := none, inner := none } := by
  have hd := decodeState_encodeState s h
  rw [he] at hd
  have hdef : Proto.decodeState [] = .ok { versionNegotiation := none, chain := none, inner := none } := rfl
  rw [hdef] at hd
  injection hd with hs
  exact hs.symm

/-- `Proto.spqrDecodeState` inverts `Proto.encodeState` (handling both empty and non-empty slices). -/
theorem spqrDecodeState_encodeState (s : PqRatchetState) (h : (Proto.encodeState s).length < 2 ^ 64) :
    Proto.spqrDecodeState (Proto.encodeState s) = .ok s := by
  unfold Proto.spqrDecodeState
  by_cases he : (Proto.encodeState s).isEmpty = true
  · simp only [he, ↓reduceIte]
    exact congrArg Except.ok (encodeState_eq_nil s h (List.isEmpty_iff.mp he)).symm
  · have hne : (Proto.encodeState s).isEmpty = false := Bool.eq_false_iff.mpr he
    have hd : PqRatchetState.decode (Proto.encodeState s) = .ok s := decodeState_encodeState s h
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hd]

theorem decodeState_spqrDeps_encodeState_pb (F : ShaCompress) (K : MlKem) (s : PqRatchetState)
    (h : (Proto.encodeState s).length < 2 ^ 64) :
    decodeState (spqrDeps F K) (Proto.encodeState s) = .ok (pqRatchetStateToPb s) := by
  unfold CryptoVerification.LibsignalSpqrV1.decodeState
  by_cases he : (Proto.encodeState s).isEmpty = true
  · simp only [he, ↓reduceIte]
    rw [encodeState_eq_nil s h (List.isEmpty_iff.mp he)]
    rfl
  · have hne : (Proto.encodeState s).isEmpty = false := Bool.eq_false_iff.mpr he
    simp only [hne, Bool.false_eq_true, ↓reduceIte, spqrDeps, decodeState_encodeState s h]

/-- `Top.decodeState` inverts `encodeState` on the concrete `spqrDeps F K` bundle. -/
theorem decodeState_spqrDeps_encodeState (F : ShaCompress) (K : MlKem) (st : PqRatchetStatePB V1State)
    (h : ((spqrDeps F K).encodeState st).length < 2 ^ 64) :
    decodeState (spqrDeps F K) ((spqrDeps F K).encodeState st) = .ok st := by
  have hpb := decodeState_spqrDeps_encodeState_pb F K (pbToPqRatchetState st) h
  simpa only [spqrDeps, pqRatchetStateToPb_pbToPqRatchetState] using hpb

end CryptoVerification.SpqrV1Sync.Codec
