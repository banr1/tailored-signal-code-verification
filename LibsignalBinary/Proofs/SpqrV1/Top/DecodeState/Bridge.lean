/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Specifications.LibsignalSpqrV1.Top -- shake: keep

/-!
# `spqr::decode_state`: Pure `Proto` / `LibsignalProtoCodec` Wire Equivalence

**Checked by Lean.** Equivalences between `LibsignalProtoCodec` (`decodeVarint`, `WireType.ofTag?`,
`skipField`) and `LibsignalSpqrV1.Proto`, plus strict length-decrease lemmas for `mergeLoop` termination.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.DecodeState

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

def codecWireTypeToProto : CryptoVerification.LibsignalProtoCodec.WireType → Proto.WireType
  | .varint => .varint
  | .sixtyFourBit => .SixtyFourBit
  | .lengthDelimited => .lengthDelimited
  | .startGroup => .startGroup
  | .endGroup => .endGroup
  | .thirtyTwoBit => .ThirtyTwoBit

@[simp]
theorem codecWireTypeToProto_protoWireTypeToCodec (wt : Proto.WireType) :
    codecWireTypeToProto (protoWireTypeToCodec wt) = wt := by
  cases wt <;> rfl

@[simp]
theorem protoWireTypeToCodec_codecWireTypeToProto (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    protoWireTypeToCodec (codecWireTypeToProto wt) = wt := by
  cases wt <;> rfl

@[simp]
theorem proto_dropExact_toOption (n : Nat) (bs : List (BitVec 8)) :
    (Proto.dropExact n bs).toOption = skipBytes n bs := by
  induction n generalizing bs with
  | zero =>
    simp [Proto.dropExact, skipBytes, Except.toOption]
  | succ n ih =>
    cases bs with
    | nil =>
      simp [Proto.dropExact, skipBytes, Except.toOption]
    | cons b rest =>
      simp only [Proto.dropExact, ih rest, skipBytes, List.length_cons,
        Nat.add_lt_add_iff_right, List.drop_succ_cons]

private theorem key_gt_u32Max_iff (key : BitVec 64) :
    (0xffffffff#64 < key) ↔ 2 ^ 32 ≤ key.toNat := by
  rw [BitVec.lt_def]
  change 0xffffffff < key.toNat ↔ 4294967296 ≤ key.toNat
  omega

private theorem wireType_ofU64_eq_ofNat (key : BitVec 64) :
    Proto.WireType.ofU64? (key &&& 0x7#64) =
      (CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8)).map codecWireTypeToProto := by
  have hmod : (key &&& 0x7#64).toNat = key.toNat % 8 := by
    rw [BitVec.toNat_and, show (0x7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rcases h : key.toNat % 8 with _ | _ | _ | _ | _ | _ | _ | n
  · have hb : (key &&& 0x7#64) = 0#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 1#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 2#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 3#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 4#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 5#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?, codecWireTypeToProto]
  · have hb : (key &&& 0x7#64) = 6#64 := BitVec.eq_of_toNat_eq (by rw [hmod, h]; rfl)
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?]
  · have hb : (key &&& 0x7#64) = BitVec.ofNat 64 (n + 7) := BitVec.eq_of_toNat_eq (by
      rw [hmod, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have hn0 : n = 0 := by omega
    subst hn0
    simp [hb, Proto.WireType.ofU64?, CryptoVerification.LibsignalProtoCodec.WireType.ofNat?]

private theorem key_tag_toNat_of_lt (key : BitVec 64) (h : key.toNat < 2 ^ 32) :
    ((key >>> 3).truncate 32).toNat = key.toNat / 8 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (key.toNat / 8) % 4294967296 = key.toNat / 8
  exact Nat.mod_eq_of_lt (by omega)

theorem proto_decodeKey_toOption (bs : List (BitVec 8)) :
    (Proto.decodeKey bs).toOption =
      (decodeKey bs).map (fun ((tag, wt), rest) => ((BitVec.ofNat 32 tag, codecWireTypeToProto wt), rest)) := by
  unfold Proto.decodeKey decodeKey
  rcases hdv : Proto.decodeVarint bs with err | ⟨key, rest⟩
  · have hdv' : decodeVarint bs = none := by
      rw [← proto_decodeVarint_toOption bs, hdv]; rfl
    simp [hdv', Bind.bind, Except.bind, Except.toOption]
  · have hdv' : decodeVarint bs = some (key, rest) := by
      rw [← proto_decodeVarint_toOption bs, hdv]; rfl
    simp only [hdv, hdv', Bind.bind, Except.bind, gt_iff_lt]
    by_cases hk : 2 ^ 32 ≤ key.toNat
    · have hk' : 0xffffffff#64 < key := (key_gt_u32Max_iff key).mpr hk
      simp only [hk, hk', ↓reduceIte, Option.map_none, Except.toOption]
    · have hk' : ¬ (0xffffffff#64 < key) := fun h => hk ((key_gt_u32Max_iff key).mp h)
      simp only [hk, hk', ↓reduceIte, wireType_ofU64_eq_ofNat]
      rcases hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) with _ | wt
      · simp [Except.toOption]
      · simp only [Option.map_some]
        have htag_nat : ((key >>> 3).truncate 32).toNat = key.toNat / 8 :=
          key_tag_toNat_of_lt key (by omega)
        have hmin : ((key >>> 3).truncate 32 < Proto.MIN_TAG) ↔ key.toNat / 8 < 1 := by
          rw [BitVec.lt_def, htag_nat]; rfl
        by_cases ht : key.toNat / 8 < 1
        · have ht' : (key >>> 3).truncate 32 < Proto.MIN_TAG := hmin.mpr ht
          simp [ht, ht', Except.toOption]
        · have ht' : ¬ ((key >>> 3).truncate 32 < Proto.MIN_TAG) := fun h => ht (hmin.mp h)
          have htag_bv : BitVec.ofNat 32 (key.toNat / 8) = (key >>> 3).truncate 32 := by
            apply BitVec.eq_of_toNat_eq
            rw [htag_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          simp [ht, ht', htag_bv, Except.toOption]

theorem proto_skipFieldNonGroup_toOption (wt : Proto.WireType) (bs : List (BitVec 8))
    (hng : wt ≠ .startGroup) :
    (Proto.skipFieldNonGroup wt bs).toOption =
      if wt == .endGroup then none else skipScalar (protoWireTypeToCodec wt) bs := by
  cases wt <;> simp only [Proto.skipFieldNonGroup, protoWireTypeToCodec, skipScalar]
  case varint =>
    rcases hdv : Proto.decodeVarint bs with err | ⟨v, rest⟩
    · have hdv' : decodeVarint bs = none := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (v, rest) := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  case SixtyFourBit =>
    exact proto_dropExact_toOption 8 bs
  case lengthDelimited =>
    rcases hdv : Proto.decodeVarint bs with err | ⟨len, rest⟩
    · have hdv' : decodeVarint bs = none := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint bs = some (len, rest) := by rw [← proto_decodeVarint_toOption bs, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, proto_dropExact_toOption]
  case startGroup =>
    exact (hng rfl).elim
  case endGroup =>
    rfl
  case ThirtyTwoBit =>
    exact proto_dropExact_toOption 4 bs

theorem proto_skipGroupLoop_toOption (depth' : Nat)
    (ih : ∀ (wt : Proto.WireType) (tag : BitVec 32) (bs : List (BitVec 8)),
      (Proto.skipFieldAux depth' wt tag bs).toOption =
        skipField (2 * bs.length + 2) depth' tag.toNat (protoWireTypeToCodec wt) bs) :
    ∀ (fuel : Nat) (tag : BitVec 32) (bs : List (BitVec 8)),
      bs.length ≤ fuel →
      (Proto.skipGroupLoop (Proto.skipFieldAux depth') fuel tag bs).toOption =
        skipGroup (2 * bs.length + 1) (depth' + 1) tag.toNat bs := by
  intro fuel
  induction fuel with
  | zero =>
    intro tag bs hlen
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    rfl
  | succ fuel ihFuel =>
    intro tag bs hlen
    unfold Proto.skipGroupLoop
    rw [skipGroup.eq_def]
    simp only [Nat.add_eq]
    rcases hdk : Proto.decodeKey bs with err | ⟨⟨itag, iwt⟩, rest⟩
    · have hdk' : decodeKey bs = none := by
        have h := proto_decodeKey_toOption bs
        rw [hdk] at h
        cases hd : decodeKey bs <;> simp [hd, Except.toOption] at h ⊢
      simp [hdk', Bind.bind, Except.bind, Except.toOption]
    · have hdk_opt := proto_decodeKey_toOption bs
      rw [hdk] at hdk_opt
      rcases hdk' : decodeKey bs with _ | ⟨⟨itag_n, iwt_c⟩, rest'⟩
      · simp [hdk', Except.toOption] at hdk_opt
      · simp only [hdk', Option.map_some, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hdk_opt
        rcases hdk_opt with ⟨⟨hitag, hiwt⟩, hrest⟩
        subst hitag hiwt hrest
        have hlt_len : rest.length < bs.length := decodeKey_length hdk'
        have hitag_lt : itag_n < 2 ^ 32 := by
          unfold decodeKey at hdk'
          cases hd : decodeVarint bs with
          | none => simp [hd] at hdk'
          | some p =>
            simp only [hd] at hdk'
            split at hdk'
            · simp at hdk'
            · cases hwt : WireType.ofNat? (p.1.toNat % 8) with
              | none => simp [hwt] at hdk'
              | some w =>
                simp only [hwt] at hdk'
                split at hdk'
                · simp at hdk'
                · simp only [Option.some.injEq, Prod.mk.injEq] at hdk'
                  omega
        have hitag_toNat : (BitVec.ofNat 32 itag_n).toNat = itag_n := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hitag_lt]
        have hih := ih (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest
        rw [hitag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hih
        have hfuel_sf : skipField (2 * bs.length) depth' itag_n iwt_c rest =
            skipField (2 * rest.length + 2) depth' itag_n iwt_c rest :=
          skipField_fuel (2 * bs.length) depth' itag_n iwt_c rest (by omega)
        have hstep :
            (do
              let rest' ← Proto.skipFieldAux depth' (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest
              Proto.skipGroupLoop (Proto.skipFieldAux depth') fuel tag rest').toOption =
            (match skipField (2 * bs.length) depth' itag_n iwt_c rest with
              | none => none
              | some rest' => skipGroup (2 * bs.length) (depth' + 1) tag.toNat rest') := by
          rw [hfuel_sf]
          rcases hsf : Proto.skipFieldAux depth' (codecWireTypeToProto iwt_c) (BitVec.ofNat 32 itag_n) rest with err | rest2
          · rw [hsf] at hih
            dsimp [Except.toOption] at hih
            rw [← hih]
            rfl
          · rw [hsf] at hih
            dsimp [Except.toOption] at hih
            rw [← hih]
            dsimp only [Bind.bind, Except.bind]
            have hle_rest2 : rest2.length ≤ rest.length :=
              (skip_length (2 * rest.length + 2)).1 depth' itag_n iwt_c rest rest2 hih.symm
            rw [ihFuel tag rest2 (by omega)]
            exact ((skip_fuel (2 * rest2.length + 1)).2 (2 * bs.length) (depth' + 1) tag.toNat rest2
              (Nat.le_refl _) (by omega))
        cases iwt_c <;> simp only [codecWireTypeToProto, Bind.bind, Except.bind]
        case endGroup =>
          simp only [beq_self_eq_true, ↓reduceIte]
          by_cases heq : itag_n = tag.toNat
          · have hbeq : (BitVec.ofNat 32 itag_n != tag) = false := by
              rw [bne_eq_false_iff_eq]
              apply BitVec.eq_of_toNat_eq
              rw [hitag_toNat, heq]
            simp [heq, hbeq, Except.toOption]
          · have hbeq : (BitVec.ofNat 32 itag_n != tag) = true := by
              rw [bne_iff_ne]
              intro h
              apply heq
              have := congrArg BitVec.toNat h
              rwa [hitag_toNat] at this
            simp [heq, hbeq, Except.toOption]
        all_goals
          exact hstep

@[simp]
theorem proto_skipFieldAux_toOption (depth : Nat) (wt : Proto.WireType) (tag : BitVec 32)
    (bs : List (BitVec 8)) :
    (Proto.skipFieldAux depth wt tag bs).toOption =
      skipField (2 * bs.length + 2) depth tag.toNat (protoWireTypeToCodec wt) bs := by
  induction depth generalizing wt tag bs with
  | zero =>
    simp [Proto.skipFieldAux, skipField, Except.toOption]
  | succ depth' ih =>
    unfold Proto.skipFieldAux
    rw [skipField.eq_def]
    simp only [Nat.add_eq, Nat.succ_ne_zero, ↓reduceIte]
    by_cases hsg : wt = .startGroup
    · subst hsg
      simp only [beq_self_eq_true, ↓reduceIte, protoWireTypeToCodec]
      exact proto_skipGroupLoop_toOption depth' ih bs.length tag bs (Nat.le_refl _)
    · have hbeq : (wt == .startGroup) = false := beq_false_of_ne hsg
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [proto_skipFieldNonGroup_toOption wt bs hsg]
      cases wt <;> simp [protoWireTypeToCodec]
      case startGroup => exact (hsg rfl).elim

@[simp]
theorem proto_skipField_toOption (wt : Proto.WireType) (tag : BitVec 32)
    (bs : List (BitVec 8)) (depth : Nat) :
    (Proto.skipField wt tag bs depth).toOption =
      skipField (2 * bs.length + 2) depth tag.toNat (protoWireTypeToCodec wt) bs :=
  proto_skipFieldAux_toOption depth wt tag bs

theorem proto_decodeVarint_suffix {bs r : List (BitVec 8)} {v : BitVec 64}
    (h : (Proto.decodeVarint bs).toOption = some (v, r)) :
    r.length < bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_decodeVarint_toOption] at h
  exact ⟨decodeVarint_length h, decodeVarint_suffix h⟩

theorem proto_takeExact_suffix {n : Nat} {bs sub after : List (BitVec 8)}
    (h : Proto.takeExact n bs = .ok (sub, after)) :
    after.length ≤ bs.length ∧ after = bs.drop (bs.length - after.length) := by
  rw [takeExact_eq_take_drop] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [List.length_drop, Nat.sub_sub_self (by omega)]
  · simp at h

theorem proto_mergeBytes_suffix {wt : Proto.WireType} {bs v r : List (BitVec 8)}
    (h : (Proto.mergeBytes wt bs).toOption = some (v, r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  unfold Proto.mergeBytes at h
  rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩
  · simp [hcw, Bind.bind, Except.bind, Except.toOption] at h
  · simp only [hcw, Bind.bind, Except.bind] at h
    rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
    · simp [hdv, Except.toOption] at h
    · simp only [hdv] at h
      rcases hte : Proto.takeExact len64.toNat rest with e | ⟨sub, after⟩
      · simp [hte, Except.toOption] at h
      · simp only [hte, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        obtain ⟨hlt1, hsuf1⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
        obtain ⟨hle2, hsuf2⟩ := proto_takeExact_suffix hte
        exact ⟨by omega, suffix_trans (Nat.le_of_lt hlt1) hsuf1 hle2 hsuf2⟩

theorem proto_mergeMessage_suffix {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    {wt : Proto.WireType} {m m' : M} {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.mergeMessage mergeField wt m bs depth).toOption = some (m', r)) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  cases depth with
  | zero =>
    rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩ <;>
      simp [Proto.mergeMessage, hcw, Bind.bind, Except.bind, Except.toOption] at h
  | succ depth' =>
    simp only [Proto.mergeMessage, Bind.bind, Except.bind] at h
    rcases hcw : Proto.checkWireType .lengthDelimited wt with e | ⟨⟩
    · simp [hcw, Except.toOption] at h
    · simp only [hcw] at h
      rcases hdv : Proto.decodeVarint bs with e | ⟨len64, rest⟩
      · simp [hdv, Except.toOption] at h
      · simp only [hdv] at h
        rcases hte : Proto.takeExact len64.toNat rest with e | ⟨sub, after⟩
        · simp [hte, Except.toOption] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop mergeField sub.length m sub depth' with e | m2
          · simp [hloop, Except.toOption] at h
          · simp only [hloop, Pure.pure, Except.pure, Except.toOption, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨_, rfl⟩
            obtain ⟨hlt1, hsuf1⟩ := proto_decodeVarint_suffix (by rw [hdv]; rfl)
            obtain ⟨hle2, hsuf2⟩ := proto_takeExact_suffix hte
            exact ⟨by omega, suffix_trans (Nat.le_of_lt hlt1) hsuf1 hle2 hsuf2⟩

theorem proto_skipField_suffix {wt : Proto.WireType} {tag : BitVec 32}
    {bs r : List (BitVec 8)} {depth : Nat}
    (h : (Proto.skipField wt tag bs depth).toOption = some r) :
    r.length ≤ bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_skipField_toOption] at h
  exact ⟨(skip_length (2 * bs.length + 2)).1 depth tag.toNat (protoWireTypeToCodec wt) bs r h,
    (skip_suffix (2 * bs.length + 2)).1 depth tag.toNat (protoWireTypeToCodec wt) bs r h⟩

theorem proto_decodeKey_suffix {bs r : List (BitVec 8)} {k : BitVec 32 × Proto.WireType}
    (h : (Proto.decodeKey bs).toOption = some (k, r)) :
    r.length < bs.length ∧ r = bs.drop (bs.length - r.length) := by
  rw [proto_decodeKey_toOption, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨tag, wt⟩, r'⟩, hdk, heq⟩ := h
  injection heq with _ hr
  subst hr
  exact ⟨decodeKey_length hdk, decodeKey_suffix hdk⟩

theorem mergeLoopBin_top {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (bs : List (BitVec 8)) (depth' : Nat) :
    mergeLoopBin mergeField bs.length m bs 0 depth' =
      (Proto.mergeFieldsLoop mergeField bs.length m bs depth').toOption := by
  have h := mergeLoopBin_append_eq hmf bs.length bs [] bs.length m depth' (Nat.le_refl _) (Nat.le_refl _)
  simpa using h

theorem mergeLoopBin_eq_limit {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (fuel : Nat) (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (heq : cur.length = limit) :
    mergeLoopBin mergeField fuel m cur limit depth' = some m := by
  rw [mergeLoopBin.eq_def]
  simp [heq]

theorem mergeLoopBin_lt_limit {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8)))
    (fuel : Nat) (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (hlt : cur.length < limit) :
    mergeLoopBin mergeField fuel m cur limit depth' = none := by
  rw [mergeLoopBin.eq_def]
  have hle : cur.length ≤ limit := Nat.le_of_lt hlt
  have hne : (cur.length == limit) = false := beq_false_of_ne (Nat.ne_of_lt hlt)
  simp [hle, hne]

theorem mergeLoopBin_gt_unfold {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (cur : List (BitVec 8)) (limit depth' : Nat)
    (hgt : ¬ cur.length ≤ limit) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' =
      match decodeKey cur with
      | none => none
      | some ((tag, wt), rest) =>
        match (mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth').toOption with
        | none => none
        | some (m', rest') =>
          mergeLoopBin mergeField (rest'.length - limit) m' rest' limit depth' := by
  obtain ⟨f, hf⟩ : ∃ f, cur.length - limit = f + 1 := ⟨cur.length - limit - 1, by omega⟩
  rw [hf, mergeLoopBin.eq_def]
  simp only [hgt, ↓reduceIte, proto_decodeKey_toOption]
  cases hdk : decodeKey cur with
  | none => rfl
  | some p =>
    rcases p with ⟨⟨tag, wt⟩, rest⟩
    dsimp only [Option.map_some]
    have hlt1 : rest.length < cur.length := decodeKey_length hdk
    cases hstep : (mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth').toOption with
    | none => rfl
    | some mr =>
      rcases mr with ⟨m', rest'⟩
      dsimp only
      rcases hmf_ex : mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto wt) rest depth' with e | ⟨m2, rest2⟩
      · simp [hmf_ex, Except.toOption] at hstep
      · simp only [hmf_ex, Except.toOption, Option.some.injEq, Prod.mk.injEq] at hstep
        rcases hstep with ⟨hm, hr⟩
        subst m2 rest2
        have hle2 : rest'.length ≤ rest.length := (hmf m _ _ depth').length_le hmf_ex
        exact mergeLoopBin_fuel hmf (rest'.length - limit) rest' limit f (rest'.length - limit) m' depth'
          (Nat.le_refl _) (by omega) (Nat.le_refl _)

theorem mergeLoopBin_of_decodeVarint_none {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur : List (BitVec 8)} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = none) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]

theorem mergeLoopBin_of_key_ge {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : 2 ^ 32 ≤ key.toNat) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : 4294967296 ≤ key.toNat := hk
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk']

theorem mergeLoopBin_of_wt_none {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = none) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt]

theorem mergeLoopBin_of_tag_zero {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag : key.toNat / 8 < 1) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' = none := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : key.toNat < 8 := by omega
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt, htag']

theorem mergeLoopBin_of_key_ok {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → List (BitVec 8) → Nat → Except Proto.DecodeErr (M × List (BitVec 8))}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    {m : M} {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {limit depth' : Nat}
    (hgt : ¬ cur.length ≤ limit) (hd : decodeVarint cur = some (key, rest))
    (hk : ¬ 2 ^ 32 ≤ key.toNat) (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag : ¬ key.toNat / 8 < 1) :
    mergeLoopBin mergeField (cur.length - limit) m cur limit depth' =
      match (mergeField m (BitVec.ofNat 32 (key.toNat / 8)) (codecWireTypeToProto iwt) rest depth').toOption with
      | none => none
      | some (m', rest') =>
        mergeLoopBin mergeField (rest'.length - limit) m' rest' limit depth' := by
  have hk' : ¬ 4294967296 ≤ key.toNat := hk
  have htag' : ¬ key.toNat < 8 := by omega
  rw [mergeLoopBin_gt_unfold hmf m cur limit depth' hgt, decodeKey, hd]
  simp [hk', hwt, htag']

theorem wt_beq_two_of_lengthDelimited {w : BitVec 64} (h : w.setWidth 8 = 2#8) :
    (BitVec.truncate 32 w &&& 255#32 == 2#32) = true := by
  revert h; bv_bits

theorem wt_beq_two_of_ne_lengthDelimited {w : BitVec 64} {wt : WireType}
    (h : w.setWidth 8 = BitVec.ofNat 8 wt.toNat) (hne : wt ≠ .lengthDelimited) :
    (BitVec.truncate 32 w &&& 255#32 == 2#32) = false := by
  cases wt <;> first | contradiction | (dsimp [WireType.toNat] at h; revert h; bv_bits)

theorem bv_len_sub_limit {rest_len : Nat} {len : BitVec 64}
    (hge : ¬ rest_len < len.toNat) :
    BitVec.ofNat 64 rest_len - len = BitVec.ofNat 64 (rest_len - len.toNat) := by
  have hsplit : rest_len = (rest_len - len.toNat) + len.toNat := by omega
  conv => lhs; arg 1; rw [hsplit]
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_sub_cancel]

theorem cmp_len_limit_of_gt {cur_len limit : Nat} (hgt : ¬ cur_len ≤ limit)
    (hcur : cur_len < 2 ^ 63) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = true ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = false := by
  simp only [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem cmp_len_limit_of_eq {cur_len limit : Nat} (heq : cur_len = limit) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = false ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = true ∧
      (BitVec.ofNat 64 cur_len == BitVec.ofNat 64 limit) = true := by
  subst heq
  simp [BitVec.ult, BitVec.ule]

theorem cmp_len_limit_of_lt {cur_len limit : Nat} (hlt : cur_len < limit)
    (hlim : limit < 2 ^ 63) :
    (BitVec.ofNat 64 limit).ult (BitVec.ofNat 64 cur_len) = false ∧
      (BitVec.ofNat 64 cur_len).ule (BitVec.ofNat 64 limit) = true ∧
      (BitVec.ofNat 64 cur_len == BitVec.ofNat 64 limit) = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
      decide_eq_false_iff_not]
    omega
  · simp only [BitVec.ule, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64),
      decide_eq_true_eq]
    omega
  · rw [beq_eq_false_iff_ne]
    intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : limit < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : cur_len < 2 ^ 64)] at h1
    omega

theorem suffix_eq_drop_of_len_eq {bs rest0 cur : List (BitVec 8)} {len_nat : Nat}
    (hle0 : rest0.length ≤ bs.length) (hsuf0 : IsDropSuffix bs rest0)
    (hge : ¬ rest0.length < len_nat)
    (hle : cur.length ≤ bs.length) (hsuf : IsDropSuffix bs cur)
    (heq : cur.length = rest0.length - len_nat) :
    cur = rest0.drop len_nat := by
  unfold IsDropSuffix at hsuf0 hsuf
  rw [hsuf, hsuf0, List.drop_drop]
  congr 1
  omega

end CryptoVerification.SpqrV1.Top.DecodeState
