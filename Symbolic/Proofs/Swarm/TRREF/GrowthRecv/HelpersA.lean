/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import Symbolic.Proofs.Swarm.SHARED.StateSizePure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf -- shake: keep

/-!
# SPQR V1 Protobuf Wire Lower Bounds and Chain Weight Lemmas

Proves byte-length lower bounds on protobuf wire decoding and field merging, out-of-order key
advance growth bounds for `ChainEpochDirection`, and weight bounds for `ChainPB` and
`VersionNegotiationPB`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecv

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3

/-! ## Protobuf Wire Decode Lower Bounds -/

theorem encodeUint64Field_length_le (tag : BitVec 32) (v : BitVec 64) :
    (Proto.encodeUint64Field tag v).length ≤ 22 := by
  unfold Proto.encodeUint64Field
  split
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le v
    omega

theorem decodeVarintAux_length_lt :
    ∀ (fuel idx : Nat) (acc : BitVec 64) (bs rest : Bytes) (v : BitVec 64),
      Proto.decodeVarintAux fuel idx acc bs = .ok (v, rest) →
      rest.length + 1 ≤ bs.length
  | 0, _, _, _, _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, [], _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, b :: bs, rest, v, h => by
    rw [Proto.decodeVarintAux] at h
    dsimp only at h
    split at h
    · split at h
      · contradiction
      · injection h with hpair
        injection hpair with _ hrest
        subst hrest
        simp
    · split at h
      · injection h with hpair
        injection hpair with _ hrest
        subst hrest
        simp
      · have ih := decodeVarintAux_length_lt fuel (idx + 1) _ bs rest v h
        simp only [List.length_cons]
        omega

theorem decodeVarint_length_lt {bs rest : Bytes} {v : BitVec 64}
    (h : Proto.decodeVarint bs = .ok (v, rest)) :
    rest.length + 1 ≤ bs.length :=
  decodeVarintAux_length_lt 10 0 0#64 bs rest v h

theorem decodeKey_length_lt {bs rest : Bytes} {tag : BitVec 32} {wt : Proto.WireType}
    (h : Proto.decodeKey bs = .ok ((tag, wt), rest)) :
    rest.length + 1 ≤ bs.length := by
  unfold Proto.decodeKey at h
  cases hdv : Proto.decodeVarint bs with
  | error e => simp [hdv, Bind.bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨key, rest0⟩
    rw [hdv] at h
    dsimp only [Bind.bind, Except.bind] at h
    have hlt := decodeVarint_length_lt hdv
    split at h
    · contradiction
    · cases hwt : Proto.WireType.ofU64? (key &&& 7#64) with
      | none => simp [hwt] at h
      | some w =>
        rw [hwt] at h
        dsimp only at h
        split at h
        · contradiction
        · injection h with hpair
          injection hpair with _ hrest
          subst hrest
          exact hlt

theorem takeExact_eq_ok :
    ∀ (n : Nat) (bs sub after : Bytes),
      Proto.takeExact n bs = .ok (sub, after) →
      bs = sub ++ after ∧ sub.length = n
  | 0, bs, sub, after, h => by
    simp [Proto.takeExact] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | n + 1, [], _, _, h => by simp [Proto.takeExact] at h
  | n + 1, b :: rest, sub, after, h => by
    rw [Proto.takeExact] at h
    cases ht : Proto.takeExact n rest with
    | error e => simp [ht, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨hd, tl⟩
      rw [ht] at h
      dsimp only [Bind.bind, Except.bind] at h
      injection h with hpair
      injection hpair with hsub htl
      subst hsub; subst htl
      rcases takeExact_eq_ok n rest hd tl ht with ⟨rfl, hlen⟩
      exact ⟨rfl, by simp [hlen]⟩

theorem takeExact_length_eq {n : Nat} {bs sub after : Bytes}
    (h : Proto.takeExact n bs = .ok (sub, after)) :
    sub.length = n ∧ sub.length + after.length = bs.length := by
  rcases takeExact_eq_ok n bs sub after h with ⟨rfl, hlen⟩
  exact ⟨hlen, by simp⟩

theorem dropExact_length_le :
    ∀ (n : Nat) (bs after : Bytes),
      Proto.dropExact n bs = .ok after →
      after.length + n = bs.length
  | 0, bs, after, h => by
    simp [Proto.dropExact] at h
    subst h
    omega
  | n + 1, [], _, h => by simp [Proto.dropExact] at h
  | n + 1, _ :: rest, after, h => by
    rw [Proto.dropExact] at h
    have ih := dropExact_length_le n rest after h
    simp only [List.length_cons]
    omega

theorem skipFieldNonGroup_length_le {wt : Proto.WireType} {bs after : Bytes}
    (h : Proto.skipFieldNonGroup wt bs = .ok after) :
    after.length ≤ bs.length := by
  unfold Proto.skipFieldNonGroup at h
  cases wt with
  | varint =>
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨v, rest⟩
      rw [hdv] at h
      dsimp only [Bind.bind, Except.bind] at h
      injection h with hrest
      subst hrest
      have hlt := decodeVarint_length_lt hdv
      omega
  | ThirtyTwoBit =>
    have hd := dropExact_length_le 4 bs after h
    omega
  | SixtyFourBit =>
    have hd := dropExact_length_le 8 bs after h
    omega
  | lengthDelimited =>
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨len, rest⟩
      rw [hdv] at h
      dsimp only [Bind.bind, Except.bind] at h
      have hlt := decodeVarint_length_lt hdv
      have hd := dropExact_length_le len.toNat rest after h
      omega
  | startGroup => contradiction
  | endGroup => contradiction

theorem skipGroupLoop_length_le
    (skipInner : Proto.WireType → BitVec 32 → Bytes → Except Proto.DecodeErr Bytes)
    (hInner : ∀ wt tag bs after, skipInner wt tag bs = .ok after → after.length ≤ bs.length) :
    ∀ (fuel : Nat) (groupTag : BitVec 32) (bs after : Bytes),
      Proto.skipGroupLoop skipInner fuel groupTag bs = .ok after →
      after.length ≤ bs.length
  | 0, _, _, _, h => by simp [Proto.skipGroupLoop] at h
  | fuel + 1, groupTag, bs, after, h => by
    unfold Proto.skipGroupLoop at h
    cases hdk : Proto.decodeKey bs with
    | error e => simp [hdk, Bind.bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨⟨innerTag, innerWt⟩, rest⟩
      rw [hdk] at h
      dsimp only [Bind.bind, Except.bind] at h
      have hlt := decodeKey_length_lt hdk
      split at h
      · split at h
        · contradiction
        · injection h with hrest
          subst hrest
          omega
      · cases hsi : skipInner innerWt innerTag rest with
        | error e => simp [hsi] at h
        | ok rest' =>
          rw [hsi] at h
          dsimp only at h
          have h1 := hInner innerWt innerTag rest rest' hsi
          have h2 := skipGroupLoop_length_le skipInner hInner fuel groupTag rest' after h
          omega

theorem skipFieldAux_length_le :
    ∀ (depth : Nat) (wt : Proto.WireType) (tag : BitVec 32) (bs after : Bytes),
      Proto.skipFieldAux depth wt tag bs = .ok after →
      after.length ≤ bs.length
  | 0, _, _, _, _, h => by simp [Proto.skipFieldAux] at h
  | depth + 1, wt, tag, bs, after, h => by
    unfold Proto.skipFieldAux at h
    split at h
    · exact skipGroupLoop_length_le (Proto.skipFieldAux depth) (skipFieldAux_length_le depth)
        bs.length tag bs after h
    · exact skipFieldNonGroup_length_le h

theorem skipField_length_le {wt : Proto.WireType} {tag : BitVec 32} {bs after : Bytes} {depth : Nat}
    (h : Proto.skipField wt tag bs depth = .ok after) :
    after.length ≤ bs.length :=
  skipFieldAux_length_le depth wt tag bs after h

theorem mergeUint32_length_lt {wt : Proto.WireType} {bs rest : Bytes} {v : BitVec 32}
    (h : Proto.mergeUint32 wt bs = .ok (v, rest)) :
    rest.length + 1 ≤ bs.length := by
  unfold Proto.mergeUint32 Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv] at h
    | ok pair =>
      rcases pair with ⟨v64, rest0⟩
      rw [hdv] at h
      dsimp only at h
      injection h with hpair
      injection hpair with _ hrest
      subst hrest
      exact decodeVarint_length_lt hdv

theorem mergeUint64_length_lt {wt : Proto.WireType} {bs rest : Bytes} {v : BitVec 64}
    (h : Proto.mergeUint64 wt bs = .ok (v, rest)) :
    rest.length + 1 ≤ bs.length := by
  unfold Proto.mergeUint64 Proto.checkWireType at h
  split at h
  · contradiction
  · exact decodeVarint_length_lt h

theorem mergeInt32_length_lt {wt : Proto.WireType} {bs rest : Bytes} {v : BitVec 32}
    (h : Proto.mergeInt32 wt bs = .ok (v, rest)) :
    rest.length + 1 ≤ bs.length := by
  unfold Proto.mergeInt32 Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv] at h
    | ok pair =>
      rcases pair with ⟨v64, rest0⟩
      rw [hdv] at h
      dsimp only at h
      injection h with hpair
      injection hpair with _ hrest
      subst hrest
      exact decodeVarint_length_lt hdv

theorem mergeBool_length_lt {wt : Proto.WireType} {bs rest : Bytes} {v : Bool}
    (h : Proto.mergeBool wt bs = .ok (v, rest)) :
    rest.length + 1 ≤ bs.length := by
  unfold Proto.mergeBool Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv] at h
    | ok pair =>
      rcases pair with ⟨v64, rest0⟩
      rw [hdv] at h
      dsimp only at h
      injection h with hpair
      injection hpair with _ hrest
      subst hrest
      exact decodeVarint_length_lt hdv

theorem mergeBytes_length_le {wt : Proto.WireType} {bs rest v : Bytes}
    (h : Proto.mergeBytes wt bs = .ok (v, rest)) :
    v.length + 1 + rest.length ≤ bs.length ∧ v.length < 2 ^ 64 := by
  unfold Proto.mergeBytes Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    cases hdv : Proto.decodeVarint bs with
    | error e => simp [hdv] at h
    | ok pair =>
      rcases pair with ⟨len, rest0⟩
      rw [hdv] at h
      dsimp only at h
      have hlt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq h with ⟨hvlen, hsum⟩
      exact ⟨by omega, by rw [hvlen]; exact len.isLt⟩

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = Except.ok b) : ∃ a, m = Except.ok a ∧ f a = Except.ok b := by
  cases m with
  | error _ => contradiction
  | ok a => exact ⟨a, rfl, h⟩

theorem keyAdvanceLoop_ooo_length_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection}
    (h : ed.keyAdvanceLoop hkdf atIdx params = .ok ed') :
    ed'.next.length ≤ max ed.next.length 32 ∧
      ed'.prev.data.length ≤ ed.prev.data.length + 36 * (params.maxOooKeysOrDefault.toNat + 1) := by
  refine ⟨(ChainEpochDirection.keyAdvanceLoop_length_le hkdf ed atIdx params h).1, ?_⟩
  suffices ∀ n (ed : ChainEpochDirection), atIdx.toNat - ed.ctr.toNat ≤ n →
      ed.keyAdvanceLoop hkdf atIdx params = .ok ed' →
      ed'.prev.data.length ≤ ed.prev.data.length + 36 * (params.maxOooKeysOrDefault.toNat + 1) from
    this (atIdx.toNat - ed.ctr.toNat) ed (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · omega
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; omega
  | succ n ih =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · rename_i hlt; split at h
      · contradiction
      · rename_i next' ctr' k hnk
        have hctr' := ChainEpochDirection.nextKeyInternal_ctr hkdf ed.next next' ed.ctr ctr' k hnk
        dsimp only [] at h; split at h
        · contradiction
        · obtain ⟨_, hnk2⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf ed.next ed.ctr hnk
          by_cases hge : ctr' + params.maxOooKeysOrDefault ≥ atIdx
          · have ⟨_, hrem⟩ := ChainEpochDirection.keyAdvanceLoop_length_le hkdf _ atIdx params h
            dsimp only [] at hrem
            simp only [hge, ↓reduceIte] at hrem
            have hadd := KeyHistory.add_length_le ed.prev k params hnk2
            have hat_le : atIdx.toNat ≤ (ctr' + params.maxOooKeysOrDefault).toNat :=
              (BitVec.le_def).mp hge
            have hmod_le : (ctr' + params.maxOooKeysOrDefault).toNat ≤
                ctr'.toNat + params.maxOooKeysOrDefault.toNat := by
              rw [BitVec.toNat_add]
              exact Nat.mod_le _ _
            have hdiff : atIdx.toNat - ctr'.toNat ≤ params.maxOooKeysOrDefault.toNat := by omega
            have hmul : 36 * (atIdx.toNat - ctr'.toNat) ≤ 36 * params.maxOooKeysOrDefault.toNat :=
              Nat.mul_le_mul_left 36 hdiff
            omega
          · have ihp := ih _ (by dsimp only []; omega) h
            dsimp only [] at ihp
            simp only [hge, ↓reduceIte] at ihp
            exact ihp
    · split at h
      · contradiction
      · simp only [Except.ok.injEq] at h; subst h; omega

theorem key_ooo_encodeRaw_le (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection} {out : Bytes}
    (hooo : params.maxOooKeysOrDefault.toNat ≤ 2000)
    (h : ed.key hkdf atIdx params = .ok (ed', out)) :
    (EpochDirectionPB.encodeRaw ed'.intoPb).length ≤
      (EpochDirectionPB.encodeRaw ed.intoPb).length + 72112 := by
  unfold ChainEpochDirection.key at h; dsimp only [] at h; split at h
  · rcases hget : ed.prev.get atIdx ed.ctr params with e | ⟨prev', out'⟩
    · simp [hget, Bind.bind, Except.bind] at h
    · simp only [hget, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hp := KeyHistory.get_length_le ed.prev atIdx ed.ctr params hget
      simp only [ChainEpochDirection.intoPb, EpochDirectionPB.encodeRaw, List.length_append]
      have h3 := encodeBytesField_length_le 3#32 prev'.data
      have h3_old : ed.prev.data.length ≤ (Proto.encodeBytesField 3#32 ed.prev.data).length := by
        unfold Proto.encodeBytesField Proto.encodeBytesUncond
        split
        · rename_i heq; simp [List.isEmpty_iff.mp heq]
        · simp only [List.length_append]; omega
      omega
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · contradiction
        · set self0 := if atIdx > ed.ctr + params.maxOooKeysOrDefault then { ed with prev := ed.prev.clear } else ed
          rcases hadv : self0.keyAdvanceLoop hkdf atIdx params with e | self1
          · simp [self0, hadv, Bind.bind, Except.bind] at h
          · simp only [self0, hadv, Bind.bind, Except.bind] at h
            rcases hgc : ChainResult.ofPanic (self1.prev.gc self1.ctr params) with e | prevGc
            · simp [hgc] at h
            · simp only [hgc] at h
              rcases hnk : ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr) with e | ⟨next', ctr', _, outKey⟩
              · simp [hnk] at h
              · simp only [hnk, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                have h0 : self0.prev.data.length ≤ ed.prev.data.length := by
                  dsimp [self0]; split <;> simp [KeyHistory.clear]
                have ⟨_, hadvp⟩ := keyAdvanceLoop_ooo_length_le hkdf self0 atIdx params hadv
                have hgc' : self1.prev.gc self1.ctr params = .ok prevGc := (ChainResult.ofPanic_eq_ok).mp hgc
                have hgcp := KeyHistory.gc_length_le self1.prev self1.ctr params hgc'
                have hnk' : ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr = .ok (next', ctr', _, outKey) :=
                  (ChainResult.ofPanic_eq_ok).mp hnk
                have ⟨hn, _⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf self1.next self1.ctr hnk'
                simp only [ChainEpochDirection.intoPb, EpochDirectionPB.encodeRaw, List.length_append]
                have h1 : (Proto.encodeUint32Field 1#32 ctr').length ≤ 12 := by
                  unfold Proto.encodeUint32Field; split; · simp
                  · rw [List.length_append]; have : (Proto.encodeKey 1#32 .varint).length = 1 := rfl
                    have := encodeVarint_length_le (ctr'.zeroExtend 64); omega
                have h2 : (Proto.encodeBytesField 2#32 next').length ≤ next'.length + 12 := by
                  unfold Proto.encodeBytesField Proto.encodeBytesUncond; split; · simp
                  · rw [List.length_append, List.length_append]
                    have : (Proto.encodeKey 2#32 .lengthDelimited).length = 1 := rfl
                    have := encodeVarint_length_le (BitVec.ofNat 64 next'.length); omega
                have h3 : (Proto.encodeBytesField 3#32 prevGc.data).length ≤ prevGc.data.length + 12 := by
                  unfold Proto.encodeBytesField Proto.encodeBytesUncond; split; · simp
                  · rw [List.length_append, List.length_append]
                    have : (Proto.encodeKey 3#32 .lengthDelimited).length = 1 := rfl
                    have := encodeVarint_length_le (BitVec.ofNat 64 prevGc.data.length); omega
                have h3_old : ed.prev.data.length ≤ (Proto.encodeBytesField 3#32 ed.prev.data).length := by
                  unfold Proto.encodeBytesField Proto.encodeBytesUncond
                  split
                  · rename_i heq; simp [List.isEmpty_iff.mp heq]
                  · simp only [List.length_append]; omega
                omega

theorem encodeVarintAux_mono :
    ∀ (fuel : Nat) {u v : BitVec 64}, u ≤ v →
      (Proto.encodeVarintAux fuel u).length ≤ (Proto.encodeVarintAux fuel v).length
  | 0, _, _, _ => by simp [Proto.encodeVarintAux]
  | fuel + 1, u, v, huv => by
    unfold Proto.encodeVarintAux; split
    · split <;> simp
    · split
      · rename_i hnu hv
        exfalso
        rw [BitVec.lt_def] at hnu hv
        rw [BitVec.le_def] at huv
        omega
      · simp only [List.length_cons]
        have hshift : u >>> 7 ≤ v >>> 7 := by
          rw [BitVec.le_def] at huv ⊢
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          exact Nat.div_le_div_right huv
        have ih := encodeVarintAux_mono fuel hshift; omega

theorem encodeVarint_mono {u v : BitVec 64} (huv : u ≤ v) :
    (Proto.encodeVarint u).length ≤ (Proto.encodeVarint v).length :=
  encodeVarintAux_mono 10 huv

theorem encodeVarintAux_length_le_of_shift :
    ∀ (fuel k : Nat) (v : BitVec 64),
      fuel ≤ 10 → k ≤ fuel → v >>> (7 * k) < 0x80#64 →
      (Proto.encodeVarintAux fuel v).length ≤ k + 1
  | 0, 0, _, _, _, _ => by simp [Proto.encodeVarintAux]
  | 0, _ + 1, _, _, hkf, _ => by omega
  | fuel + 1, 0, v, _, _, hlt => by
    have hv : v < 0x80#64 := by simpa using hlt
    simp [Proto.encodeVarintAux, hv]
  | fuel + 1, k + 1, v, hfuel, hkf, hlt => by
    unfold Proto.encodeVarintAux; split
    · simp
    · simp only [List.length_cons]
      have hlt' : (v >>> 7) >>> (7 * k) < 0x80#64 := by
        have hsh : (v >>> 7) >>> (7 * k) = v >>> (7 * (k + 1)) := by
          ext i; simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight]; congr 1; omega
        rw [hsh]; exact hlt
      have ih := encodeVarintAux_length_le_of_shift fuel k (v >>> 7) (by omega) (by omega) hlt'
      omega

private theorem ushiftRight_or_eq (a c : BitVec 64) (n : Nat) :
    (a ||| c) >>> n = (a >>> n) ||| (c >>> n) := by
  ext i; simp only [BitVec.getElem_ushiftRight, BitVec.getElem_or, BitVec.getLsbD_or]

private theorem varint_acc_shift_step (idx : Nat) (acc : BitVec 64) (b : BitVec 8)
    (hidx : idx < 9) (hacc : acc >>> (7 * idx) = 0#64) :
    (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7))) >>> (7 * idx) < 0x80#64 ∧
    (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7))) >>> (7 * (idx + 1)) = 0#64 := by
  have hacc2 : acc >>> (7 * (idx + 1)) = 0#64 := by
    have hsh : acc >>> (7 * (idx + 1)) = (acc >>> (7 * idx)) >>> 7 := by
      ext i; simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_ushiftRight]; congr 1; omega
    rw [hsh, hacc]; rfl
  rw [ushiftRight_or_eq, hacc, BitVec.zero_or]
  rw [ushiftRight_or_eq, hacc2, BitVec.zero_or]
  have hcases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨
      idx = 5 ∨ idx = 6 ∨ idx = 7 ∨ idx = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (revert b; decide)

theorem decodeVarintAux_encodeVarint_length_le :
    ∀ (fuel idx : Nat) (acc : BitVec 64) (bs rest : Bytes) (v : BitVec 64),
      idx + fuel ≤ 10 → acc >>> (7 * idx) = 0#64 →
      Proto.decodeVarintAux fuel idx acc bs = .ok (v, rest) →
      (Proto.encodeVarint v).length + rest.length ≤ idx + bs.length
  | 0, _, _, _, _, _, _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, [], _, _, _, _, h => by simp [Proto.decodeVarintAux] at h
  | fuel + 1, idx, acc, b :: bs, rest, v, hif, hacc, h => by
    simp only [Proto.decodeVarintAux] at h; split at h
    · rename_i hidx9; have hidx_eq : idx = 9 := by simpa using hidx9
      split at h; · contradiction
      · injection h with hpair; injection hpair with hv hrest; subst hv hrest hidx_eq
        have hlt9 : (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 63)) >>> (7 * 9) < 0x80#64 := by
          rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          have hlt64 := (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< 63)).isLt
          change _ < 128
          omega
        have hlen := encodeVarintAux_length_le_of_shift 10 9 _ (by omega) (by omega) hlt9
        simp only [Proto.encodeVarint, List.length_cons]; omega
    · rename_i hidx9; have hidx_lt : idx < 9 := by simp at hidx9; omega
      rcases varint_acc_shift_step idx acc b hidx_lt hacc with ⟨hlt_cur, hacc_next⟩
      split at h
      · injection h with hpair; injection hpair with hv hrest; subst hv hrest
        have hlen := encodeVarintAux_length_le_of_shift 10 idx _ (by omega) (by omega) hlt_cur
        simp only [Proto.encodeVarint, List.length_cons]; omega
      · have ih := decodeVarintAux_encodeVarint_length_le fuel (idx + 1)
          (acc ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (idx * 7))) bs rest v (by omega) hacc_next h
        simp only [List.length_cons]; omega

theorem decodeVarint_encodeVarint_length_le {bs rest : Bytes} {v : BitVec 64}
    (h : Proto.decodeVarint bs = .ok (v, rest)) :
    (Proto.encodeVarint v).length + rest.length ≤ bs.length := by
  have h0 := decodeVarintAux_encodeVarint_length_le 10 0 0#64 bs rest v (by omega) rfl h; omega

theorem encodeVarintAux_fuel_mono :
    ∀ (fuel : Nat) (v : BitVec 64),
      (Proto.encodeVarintAux fuel v).length ≤ (Proto.encodeVarintAux (fuel + 1) v).length
  | 0, v => by unfold Proto.encodeVarintAux; split <;> simp
  | fuel + 1, v => by
    conv_lhs => unfold Proto.encodeVarintAux
    conv_rhs => unfold Proto.encodeVarintAux
    split; · simp
    · simp only [List.length_cons]; have ih := encodeVarintAux_fuel_mono fuel (v >>> 7); omega

theorem encodeVarintAux_length_pos :
    ∀ (fuel : Nat) (v : BitVec 64), 1 ≤ (Proto.encodeVarintAux fuel v).length
  | 0, _ => by simp [Proto.encodeVarintAux]
  | _ + 1, _ => by unfold Proto.encodeVarintAux; split <;> simp

theorem encodeVarintAux_subadd :
    ∀ (fuel : Nat) {w u v : BitVec 64},
      w.toNat ≤ u.toNat + v.toNat →
      (Proto.encodeVarintAux fuel w).length ≤
        (Proto.encodeVarintAux fuel u).length + (Proto.encodeVarintAux fuel v).length
  | 0, _, _, _, _ => by simp [Proto.encodeVarintAux]
  | fuel + 1, w, u, v, h => by
    have hpos_u := encodeVarintAux_length_pos (fuel + 1) u
    have hpos_v := encodeVarintAux_length_pos (fuel + 1) v
    have hfv := encodeVarintAux_fuel_mono fuel v
    by_cases hw : w < 128#64
    · have hlen_w : (Proto.encodeVarintAux (fuel + 1) w).length = 1 := by simp [Proto.encodeVarintAux, hw]
      omega
    · have hlen_w : (Proto.encodeVarintAux (fuel + 1) w).length =
          (Proto.encodeVarintAux fuel (w >>> 7)).length + 1 := by simp [Proto.encodeVarintAux, hw]
      by_cases hu : u < 128#64
      · have hlen_u : (Proto.encodeVarintAux (fuel + 1) u).length = 1 := by simp [Proto.encodeVarintAux, hu]
        have hfu : (Proto.encodeVarintAux fuel u).length = 1 := by
          cases fuel <;> simp [Proto.encodeVarintAux, hu]
        by_cases hv : v < 128#64
        · have hlen_v : (Proto.encodeVarintAux (fuel + 1) v).length = 1 := by simp [Proto.encodeVarintAux, hv]
          have hw7 : w >>> 7 < 128#64 := by
            have : u.toNat < 128 := by simpa [BitVec.lt_def] using hu
            have : v.toNat < 128 := by simpa [BitVec.lt_def] using hv
            have : (w >>> 7).toNat < 128 := by rw [BitVec.toNat_ushiftRight]; omega
            simpa [BitVec.lt_def] using this
          have hlen7 : (Proto.encodeVarintAux fuel (w >>> 7)).length = 1 := by
            cases fuel <;> simp [Proto.encodeVarintAux, hw7]
          omega
        · have hlen_v : (Proto.encodeVarintAux (fuel + 1) v).length =
              (Proto.encodeVarintAux fuel (v >>> 7)).length + 1 := by simp [Proto.encodeVarintAux, hv]
          have hvge : 128 ≤ v.toNat := by simpa [BitVec.lt_def] using hv
          have hshift : (w >>> 7).toNat ≤ u.toNat + (v >>> 7).toNat := by
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]; omega
          have ih := encodeVarintAux_subadd fuel hshift; omega
      · have hlen_u : (Proto.encodeVarintAux (fuel + 1) u).length =
            (Proto.encodeVarintAux fuel (u >>> 7)).length + 1 := by simp [Proto.encodeVarintAux, hu]
        have huge : 128 ≤ u.toNat := by simpa [BitVec.lt_def] using hu
        have hshift : (w >>> 7).toNat ≤ (u >>> 7).toNat + v.toNat := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]; omega
        have ih := encodeVarintAux_subadd fuel hshift; omega

theorem encodeVarint_subadd {w u v : BitVec 64} (h : w.toNat ≤ u.toNat + v.toNat) :
    (Proto.encodeVarint w).length ≤ (Proto.encodeVarint u).length + (Proto.encodeVarint v).length :=
  encodeVarintAux_subadd 10 h

theorem mergeFieldsLoop_weight_le {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (depth : Nat)
    (hstep : ∀ m tag wt rest m' rest',
      mergeField m tag wt rest depth = .ok (m', rest') →
      w m' + rest'.length ≤ w m + rest.length + 1) :
    ∀ (fuel : Nat) (m m' : M) (bs : Bytes),
      Proto.mergeFieldsLoop mergeField fuel m bs depth = .ok m' →
      w m' ≤ w m + bs.length
  | _, m, m', [], h => by simp [Proto.mergeFieldsLoop] at h; subst h; simp
  | 0, _, _, _ :: _, h => by simp [Proto.mergeFieldsLoop] at h
  | fuel + 1, m, m', b :: bs, h => by
    unfold Proto.mergeFieldsLoop at h
    rcases except_bind_eq_ok h with ⟨⟨⟨tag, wt⟩, rest⟩, hdk, h⟩
    rcases except_bind_eq_ok h with ⟨⟨m1, rest'⟩, hmf, h⟩
    have h1 := decodeKey_length_lt hdk
    have h2 := hstep m tag wt rest m1 rest' hmf
    have ih := mergeFieldsLoop_weight_le mergeField w depth hstep fuel m1 m' rest' h
    simp only [List.length_cons] at h1 ⊢; omega

theorem mergeFieldsLoop_weight_le_lt64 {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (depth : Nat)
    (hstep : ∀ m tag wt rest m' rest',
      w m + rest.length < 2 ^ 64 →
      mergeField m tag wt rest depth = .ok (m', rest') →
      w m' + rest'.length ≤ w m + rest.length + 1) :
    ∀ (fuel : Nat) (m m' : M) (bs : Bytes),
      w m + bs.length < 2 ^ 64 →
      Proto.mergeFieldsLoop mergeField fuel m bs depth = .ok m' →
      w m' ≤ w m + bs.length
  | _, m, m', [], _, h => by simp [Proto.mergeFieldsLoop] at h; subst h; simp
  | 0, _, _, _ :: _, _, h => by simp [Proto.mergeFieldsLoop] at h
  | fuel + 1, m, m', b :: bs, hlt, h => by
    unfold Proto.mergeFieldsLoop at h
    rcases except_bind_eq_ok h with ⟨⟨⟨tag, wt⟩, rest⟩, hdk, h⟩
    rcases except_bind_eq_ok h with ⟨⟨m1, rest'⟩, hmf, h⟩
    have h1 := decodeKey_length_lt hdk
    simp only [List.length_cons] at h1 hlt ⊢
    have h2 := hstep m tag wt rest m1 rest' (by omega) hmf
    have ih := mergeFieldsLoop_weight_le_lt64 mergeField w depth hstep fuel m1 m' rest' (by omega) h
    omega

theorem mergeUint32_encodeUint32Field_length_le (tag : BitVec 32) {wt : Proto.WireType} {bs rest : Bytes} {v : BitVec 32}
    (htag : (Proto.encodeKey tag .varint).length = 1)
    (h : Proto.mergeUint32 wt bs = .ok (v, rest)) :
    (Proto.encodeUint32Field tag v).length + rest.length ≤ bs.length + 1 := by
  unfold Proto.mergeUint32 Proto.checkWireType at h; split at h; · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_eq_ok h with ⟨⟨v64, rest0⟩, hdv, h⟩
    dsimp only at h
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have hd := decodeVarint_encodeVarint_length_le hdv
    have hle : (v64.truncate 32).zeroExtend 64 ≤ v64 := by
      rw [BitVec.le_def]
      simp only [BitVec.toNat_setWidth]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)
    have hm := encodeVarint_mono hle
    unfold Proto.encodeUint32Field; split; · simp; omega
    · rw [List.length_append, htag]; omega

theorem mergeBytes_encodeBytesUncond_length_le (tag : BitVec 32) {wt : Proto.WireType} {bs rest v : Bytes}
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (h : Proto.mergeBytes wt bs = .ok (v, rest)) :
    (Proto.encodeBytesUncond tag v).length + rest.length ≤ bs.length + 1 := by
  unfold Proto.mergeBytes Proto.checkWireType at h; split at h; · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_eq_ok h with ⟨⟨len, rest0⟩, hdv, h⟩
    dsimp only at h
    have hd := decodeVarint_encodeVarint_length_le hdv
    rcases takeExact_length_eq h with ⟨hvlen, hsum⟩
    have hlen_eq : BitVec.ofNat 64 v.length = len := by
      rw [hvlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold Proto.encodeBytesUncond
    rw [List.length_append, List.length_append, htag, hlen_eq]; omega

theorem mergeBytes_encodeBytesField_length_le (tag : BitVec 32) {wt : Proto.WireType} {bs rest v : Bytes}
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (h : Proto.mergeBytes wt bs = .ok (v, rest)) :
    (Proto.encodeBytesField tag v).length + rest.length ≤ bs.length + 1 := by
  have h1 := mergeBytes_encodeBytesUncond_length_le tag htag h
  unfold Proto.encodeBytesField; split <;> [simp; skip] <;> omega

theorem epochDir_mergeField_length_le (depth : Nat) (m : EpochDirectionPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : EpochDirectionPB) (rest' : Bytes)
    (h : EpochDirectionPB.mergeField m tag wt rest depth = .ok (m', rest')) :
    (EpochDirectionPB.encodeRaw m').length + rest'.length ≤
      (EpochDirectionPB.encodeRaw m).length + rest.length + 1 := by
  unfold EpochDirectionPB.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeUint32_encodeUint32Field_length_le 1#32 rfl hm
    simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h2 := mergeBytes_encodeBytesField_length_le 2#32 rfl hm
      simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h3 := mergeBytes_encodeBytesField_length_le 3#32 rfl hm
        simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
      · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have hs := skipField_length_le hskip; omega

theorem mergeOptMessage_epochDir_length_le (tag : BitVec 32) (wt : Proto.WireType)
    (opt opt' : Option EpochDirectionPB) (rest rest' : Bytes) (depth : Nat)
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (hlt : (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt).length + rest.length < 2 ^ 64)
    (h : Proto.mergeOptMessage EpochDirectionPB.mergeField wt opt rest depth = .ok (opt', rest')) :
    (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt').length + rest'.length ≤
      (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt).length + rest.length + 1 := by
  unfold Proto.mergeOptMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨d0', after⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm; · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm; split at hm; · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after0⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨d', hloop, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake hloop ⊢
      have hdv_len := decodeVarint_encodeVarint_length_le hdv
      rcases takeExact_length_eq htake with ⟨hsub_len, htake_sum⟩
      have hd1 := mergeFieldsLoop_weight_le EpochDirectionPB.mergeField
        (fun d => (EpochDirectionPB.encodeRaw d).length) depth' (epochDir_mergeField_length_le depth')
        sub.length (opt.getD default) d' sub hloop
      cases opt with
      | none =>
        have hdef : (EpochDirectionPB.encodeRaw (default : EpochDirectionPB)).length = 0 := rfl
        simp only [Option.getD_none, hdef, Nat.zero_add] at hd1
        have hle_len : BitVec.ofNat 64 (EpochDirectionPB.encodeRaw d').length ≤ len := by
          rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        have hm_var := encodeVarint_mono hle_len
        simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.length_nil, List.length_append]
        rw [htag]; omega
      | some d0 =>
        simp only [Option.getD_some] at hd1
        simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.length_append, htag] at hlt ⊢
        have hsubadd : (BitVec.ofNat 64 (EpochDirectionPB.encodeRaw d').length).toNat ≤
            (BitVec.ofNat 64 (EpochDirectionPB.encodeRaw d0).length).toNat + len.toNat := by
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        have hm_var := encodeVarint_subadd hsubadd; omega

theorem chainEpoch_mergeField_length_le (m : ChainEpochPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (depth : Nat) (m' : ChainEpochPB) (rest' : Bytes)
    (hlt : (ChainEpochPB.encodeRaw m).length + rest.length < 2 ^ 64)
    (h : ChainEpochPB.mergeField m tag wt rest depth = .ok (m', rest')) :
    (ChainEpochPB.encodeRaw m').length + rest'.length ≤
      (ChainEpochPB.encodeRaw m).length + rest.length + 1 := by
  unfold ChainEpochPB.mergeField at h
  simp only [ChainEpochPB.encodeRaw, List.length_append] at hlt; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeOptMessage_epochDir_length_le 1#32 wt m.send v rest bs' depth rfl (by omega) hm
    simp only [ChainEpochPB.encodeRaw, List.length_append]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h2 := mergeOptMessage_epochDir_length_le 2#32 wt m.recv v rest bs' depth rfl (by omega) hm
      simp only [ChainEpochPB.encodeRaw, List.length_append]; omega
    · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have hs := skipField_length_le hskip; simp only [ChainEpochPB.encodeRaw, List.length_append]; omega

@[scoped simp] theorem encodeRepeatedMessage_cons {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32)
    (m : M) (ms : List M) :
    Proto.encodeRepeatedMessage encodeRaw tag (m :: ms) =
      Proto.encodeMessage encodeRaw tag m ++ Proto.encodeRepeatedMessage encodeRaw tag ms := rfl

theorem encodeRepeatedMessage_append {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32)
    (ms : List M) (m : M) :
    Proto.encodeRepeatedMessage encodeRaw tag (ms ++ [m]) =
      Proto.encodeRepeatedMessage encodeRaw tag ms ++ Proto.encodeMessage encodeRaw tag m := by
  induction ms with
  | nil => simp [Proto.encodeRepeatedMessage]
  | cons x xs ih => simp only [List.cons_append, encodeRepeatedMessage_cons, ih, List.append_assoc]

theorem mergeRepeatedMessage_chainEpoch_length_le (wt : Proto.WireType)
    (ms ms' : List ChainEpochPB) (rest rest' : Bytes) (depth : Nat)
    (h : Proto.mergeRepeatedMessage ChainEpochPB.mergeField wt ms rest depth = .ok (ms', rest')) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ms').length + rest'.length ≤
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ms).length + rest.length + 1 := by
  unfold Proto.mergeRepeatedMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨e0', after⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm; · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm; split at hm; · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after0⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨e', hloop, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake hloop ⊢
      have hdv_len := decodeVarint_encodeVarint_length_le hdv
      rcases takeExact_length_eq htake with ⟨hsub_len, htake_sum⟩
      have hdef : (ChainEpochPB.encodeRaw (default : ChainEpochPB)).length = 0 := rfl
      have hlt_sub : (ChainEpochPB.encodeRaw (default : ChainEpochPB)).length + sub.length < 2 ^ 64 := by
        rw [hdef, Nat.zero_add, hsub_len]; exact len.isLt
      have he1 := mergeFieldsLoop_weight_le_lt64 ChainEpochPB.mergeField
        (fun e => (ChainEpochPB.encodeRaw e).length) depth'
        (fun m tag wt r m' r' hlt hmf => chainEpoch_mergeField_length_le m tag wt r depth' m' r' hlt hmf)
        sub.length default e' sub hlt_sub hloop
      rw [hdef, Nat.zero_add] at he1
      have hle_len : BitVec.ofNat 64 (ChainEpochPB.encodeRaw e').length ≤ len := by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      have hm_var := encodeVarint_mono hle_len
      have hkey : (Proto.encodeKey 3#32 .lengthDelimited).length = 1 := rfl
      rw [encodeRepeatedMessage_append, List.length_append]
      simp only [Proto.encodeMessage, List.length_append, hkey]; omega

def optWeight {M : Type} (w : M → Nat) : Option M → Nat
  | none => 0
  | some m => w m

@[scoped simp] theorem optWeight_none {M : Type} (w : M → Nat) : optWeight w none = 0 := rfl
@[scoped simp] theorem optWeight_some {M : Type} (w : M → Nat) (m : M) : optWeight w (some m) = w m := rfl

theorem mergeOptMessage_weight_le {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (hdef : w default = 0) (depth : Nat)
    (hstep : ∀ d m tag wt rest m' rest',
      mergeField m tag wt rest d = .ok (m', rest') →
      w m' + rest'.length ≤ w m + rest.length + 1)
    (wt : Proto.WireType) (opt opt' : Option M) (bs after : Bytes)
    (h : Proto.mergeOptMessage mergeField wt opt bs depth = .ok (opt', after)) :
    optWeight w opt' + after.length ≤ optWeight w opt + bs.length := by
  unfold Proto.mergeOptMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨m0', after0⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm; · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm; split at hm; · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after1⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨m', hloop, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake hloop ⊢
      have hdv_lt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq htake with ⟨_, htake_sum⟩
      have hm1 := mergeFieldsLoop_weight_le mergeField w depth' (hstep depth')
        sub.length (opt.getD default) m' sub hloop
      cases opt <;> simp only [Option.getD_none, Option.getD_some, hdef, Nat.zero_add, optWeight] at hm1 ⊢ <;> omega

theorem mergeOptMessage_rest_length_le {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (wt : Proto.WireType) (opt opt' : Option M) (bs after : Bytes) (depth : Nat)
    (h : Proto.mergeOptMessage mergeField wt opt bs depth = .ok (opt', after)) :
    after.length + 1 ≤ bs.length := by
  unfold Proto.mergeOptMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨m', after0⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm; · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm; split at hm; · contradiction
    · rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after1⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨m1, _, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake ⊢
      have hdv_lt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq htake with ⟨_, htake_sum⟩; omega

theorem mergeMessage_weight_le {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (w : M → Nat) (depth : Nat)
    (hstep : ∀ d m tag wt rest m' rest',
      mergeField m tag wt rest d = .ok (m', rest') →
      w m' + rest'.length ≤ w m + rest.length + 1)
    (wt : Proto.WireType) (prev m' : M) (bs after : Bytes)
    (h : Proto.mergeMessage mergeField wt prev bs depth = .ok (m', after)) :
    w m' + after.length ≤ w prev + bs.length := by
  unfold Proto.mergeMessage Proto.checkWireType at h; split at h; · contradiction
  · dsimp only [Bind.bind, Except.bind] at h; split at h; · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok h with ⟨⟨len, rest0⟩, hdv, h⟩
      rcases except_bind_eq_ok h with ⟨⟨sub, after1⟩, htake, h⟩
      rcases except_bind_eq_ok h with ⟨m1, hloop, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      dsimp only at htake hloop ⊢
      have hdv_lt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq htake with ⟨_, htake_sum⟩
      have hm1 := mergeFieldsLoop_weight_le mergeField w depth' (hstep depth') sub.length prev m1 sub hloop
      omega

abbrev linkToPb (link : ChainEpoch) : ChainEpochPB :=
  { send := some link.send.intoPb, recv := some link.recv.intoPb }

def chainWeight (c : ChainPB) : Nat :=
  (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 c.links).length + c.nextRoot.length

def optChainWeight : Option ChainPB → Nat := optWeight chainWeight

theorem chainPB_mergeField_weight_le (d : Nat) (m : ChainPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : ChainPB) (rest' : Bytes)
    (h : ChainPB.mergeField m tag wt rest d = .ok (m', rest')) :
    chainWeight m' + rest'.length ≤ chainWeight m + rest.length + 1 := by
  unfold ChainPB.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have := mergeInt32_length_lt hm; simp only [chainWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeUint64_length_lt hm; simp only [chainWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeRepeatedMessage_chainEpoch_length_le wt m.links v rest bs' d hm
        simp only [chainWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [chainWeight]; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have := mergeUint64_length_lt hm; simp only [chainWeight]; omega
          · split at h
            · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
              have := mergeOptMessage_rest_length_le ChainParamsPB.mergeField wt m.params v rest bs' d hm
              simp only [chainWeight]; omega
            · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
              have := skipField_length_le hs; simp only [chainWeight]; omega

def vnWeight (v : VersionNegotiationPB) : Nat := v.authKey.length
def optVnWeight : Option VersionNegotiationPB → Nat := optWeight vnWeight

theorem vnPB_mergeField_weight_le (d : Nat) (m : VersionNegotiationPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : VersionNegotiationPB) (rest' : Bytes)
    (h : VersionNegotiationPB.mergeField m tag wt rest d = .ok (m', rest')) :
    vnWeight m' + rest'.length ≤ vnWeight m + rest.length + 1 := by
  unfold VersionNegotiationPB.mergeField at h; split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [vnWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have := mergeInt32_length_lt hm; simp only [vnWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have := mergeInt32_length_lt hm; simp only [vnWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := mergeOptMessage_rest_length_le ChainParamsPB.mergeField wt m.chainParams v rest bs' d hm
          simp only [vnWeight]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hs, h⟩; rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have := skipField_length_le hs; simp only [vnWeight]; omega

theorem chainParamsPB_encodeOptMessage_length_le (tag : BitVec 32) (opt : Option ChainParamsPB) :
    (Proto.encodeOptMessage ChainParamsPB.encodeRaw tag opt).length ≤ 66 := by
  cases opt with
  | none => simp [Proto.encodeOptMessage]
  | some p =>
    have hm := encodeMessage_length_le ChainParamsPB.encodeRaw tag p
    simp only [ChainParamsPB.encodeRaw, List.length_append] at hm
    have h1 := encodeUint32Field_length_le 1#32 p.maxJump
    have h2 := encodeUint32Field_length_le 2#32 p.maxOooKeys
    simpa [Proto.encodeOptMessage] using by omega

theorem vnPB_encodeOptMessage_length_le (opt : Option VersionNegotiationPB) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt).length ≤ optVnWeight opt + 154 := by
  cases opt with
  | none => simp [Proto.encodeOptMessage, optVnWeight, optWeight]
  | some v =>
    have hm := encodeMessage_length_le VersionNegotiationPB.encodeRaw 1#32 v
    simp only [VersionNegotiationPB.encodeRaw, List.length_append] at hm
    have h1 := encodeBytesField_length_le 1#32 v.authKey
    have h2 := encodeInt32Field_length_le 2#32 v.direction
    have h3 := encodeInt32Field_length_le 3#32 v.minVersion
    have h4 := chainParamsPB_encodeOptMessage_length_le 4#32 v.chainParams
    simp only [Proto.encodeOptMessage, optVnWeight, optWeight, vnWeight]; omega

theorem chainPB_encodeOptMessage_length_le (c : ChainPB) :
    (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 (some c)).length ≤ chainWeight c + 176 := by
  have hm := encodeMessage_length_le ChainPB.encodeRaw 2#32 c
  simp only [ChainPB.encodeRaw, List.length_append] at hm
  have h1 := encodeInt32Field_length_le 1#32 c.direction
  have h2 := encodeUint64Field_length_le 2#32 c.currentEpoch
  have h4 := encodeBytesField_length_le 4#32 c.nextRoot
  have h5 := encodeUint64Field_length_le 5#32 c.sendEpoch
  have h6 := chainParamsPB_encodeOptMessage_length_le 6#32 c.params
  simp only [Proto.encodeOptMessage, chainWeight]; omega

theorem ced_fromPb_intoPb {pb : EpochDirectionPB} {ced : ChainEpochDirection}
    (h : ChainEpochDirection.fromPb pb = .ok ced) : ced.intoPb = pb := by
  unfold ChainEpochDirection.fromPb at h; split at h; · contradiction
  · injection h with hced; subst hced; cases pb; rfl

theorem chain_linksFromPb_map_eq :
    ∀ (pbs : List ChainEpochPB) (links : List ChainEpoch),
      Chain.linksFromPb pbs = .ok links → links.map linkToPb = pbs
  | [], links, h => by simp [Chain.linksFromPb] at h; subst h; rfl
  | link :: rest, links, h => by
    unfold Chain.linksFromPb at h
    cases hs : link.send with
    | none => simp [hs, Bind.bind, Except.bind] at h
    | some sendPb =>
      rw [hs] at h; dsimp only [Bind.bind, Except.bind] at h
      rcases except_bind_eq_ok h with ⟨send, hsend, h⟩
      cases hr : link.recv with
      | none => simp [hr] at h
      | some recvPb =>
        rw [hr] at h; dsimp only [Bind.bind, Except.bind] at h
        rcases except_bind_eq_ok h with ⟨recv, hrecv, h⟩
        rcases except_bind_eq_ok h with ⟨tail, htail, h⟩
        injection h with hlinks; subst hlinks
        have hs_eq := ced_fromPb_intoPb hsend
        have hr_eq := ced_fromPb_intoPb hrecv
        have ih := chain_linksFromPb_map_eq rest tail htail
        cases link; simp only at hs hr; subst hs hr
        simp [linkToPb, hs_eq, hr_eq, ih]

theorem chain_fromPb_weight_eq {pb : ChainPB} {c : Chain} (h : Chain.fromPb pb = .ok c) :
    chainWeight c.intoPb = chainWeight pb := by
  unfold Chain.fromPb at h
  cases hd : Direction.fromI32? pb.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some dir =>
    cases hl : Chain.linksFromPb pb.links with
    | error _ => simp [hd, hl, Bind.bind, Except.bind] at h
    | ok links =>
      cases hp : pb.params with
      | none => simp [hd, hl, hp, Bind.bind, Except.bind] at h
      | some params =>
        simp only [hd, hl, hp, Bind.bind, Except.bind] at h
        injection h with hc; subst hc
        have hmap := chain_linksFromPb_map_eq pb.links links hl
        simp only [Chain.intoPb, chainWeight]; rw [hmap]

theorem cedForDirection_encodeRaw_le (genr8r : Bytes) (dir : Direction) :
    (EpochDirectionPB.encodeRaw (Chain.cedForDirection genr8r dir).intoPb).length ≤ 54 := by
  cases dir <;> {
    unfold Chain.cedForDirection ChainEpochDirection.new ChainEpochDirection.intoPb
      KeyHistory.new EpochDirectionPB.encodeRaw
    dsimp only
    have h0 : Proto.encodeUint32Field 1#32 0#32 = [] := rfl
    have h3 : Proto.encodeBytesField 3#32 [] = [] := rfl
    rw [h0, h3, List.nil_append, List.append_nil]
    first
    | (have h2 := encodeBytesField_length_le 2#32 ((genr8r.drop 32).take 32)
       have htake : ((genr8r.drop 32).take 32).length ≤ 32 := by simp [List.length_take]
       omega)
    | (have h2 := encodeBytesField_length_le 2#32 ((genr8r.drop 64).take 32)
       have htake : ((genr8r.drop 64).take 32).length ≤ 32 := by simp [List.length_take]
       omega)
  }

theorem newLink_encodeMessage_le (genr8r : Bytes) (dir : Direction) :
    (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32
      (linkToPb { send := Chain.cedForDirection genr8r dir, recv := Chain.cedForDirection genr8r dir.switch })).length ≤ 174 := by
  have hm := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32
    (linkToPb { send := Chain.cedForDirection genr8r dir, recv := Chain.cedForDirection genr8r dir.switch })
  simp only [ChainEpochPB.encodeRaw, linkToPb, Proto.encodeOptMessage, List.length_append] at hm ⊢
  have hs := encodeMessage_length_le EpochDirectionPB.encodeRaw 1#32 (Chain.cedForDirection genr8r dir).intoPb
  have hr := encodeMessage_length_le EpochDirectionPB.encodeRaw 2#32 (Chain.cedForDirection genr8r dir.switch).intoPb
  have hs0 := cedForDirection_encodeRaw_le genr8r dir
  have hr0 := cedForDirection_encodeRaw_le genr8r dir.switch; omega

theorem chain_new_weight_le {hkdf : HkdfFn} {k : Bytes} {dir : Direction} {params : ChainParamsPB} {c : Chain}
    (h : Chain.new hkdf k dir params = .ok c) : chainWeight c.intoPb ≤ 206 := by
  unfold Chain.new at h; injection h with hc; subst hc
  simp only [Chain.intoPb, chainWeight, List.map, Proto.encodeRepeatedMessage, List.foldr, List.append_nil]
  have hlink := newLink_encodeMessage_le (hkdf (List.replicate 32 0#8) k chainStartInfo 96) dir
  dsimp only [linkToPb] at hlink
  have hroot : ((hkdf (List.replicate 32 0#8) k chainStartInfo 96).take 32).length ≤ 32 := by simp [List.length_take]
  omega

theorem chain_addEpoch_weight_le {hkdf : HkdfFn} {c0 c1 : Chain} {es : EpochSecret}
    (h : c0.addEpoch hkdf es = .ok c1) : chainWeight c1.intoPb ≤ chainWeight c0.intoPb + 206 := by
  unfold Chain.addEpoch at h; split at h; · contradiction
  · split at h; · contradiction
    · injection h with hc1; subst hc1
      simp only [Chain.intoPb, chainWeight, List.map_append, List.map]
      rw [encodeRepeatedMessage_append, List.length_append]
      have hlink := newLink_encodeMessage_le (hkdf c0.nextRoot es.secret chainAddEpochInfo 96) c0.dir
      dsimp only [linkToPb] at hlink
      have hroot : ((hkdf c0.nextRoot es.secret chainAddEpochInfo 96).take 32).length ≤ 32 := by simp [List.length_take]
      omega

end Symbolic.Swarm.TRREF.GrowthRecv
