/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import Symbolic.Proofs.Swarm.SHARED.StateSizePure

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

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

theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
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
    unfold Proto.encodeVarintAux
    split
    · split <;> simp
    · split
      · rename_i hnu hv
        exfalso; simp only [BitVec.lt_def, BitVec.le_def] at hnu hv huv; omega
      · simp only [List.length_cons]
        have hshift : u >>> 7 ≤ v >>> 7 := by
          simp only [BitVec.le_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at huv ⊢
          exact Nat.div_le_div_right huv
        have ih := encodeVarintAux_mono fuel hshift
        omega

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

theorem ushiftRight_or_eq (a c : BitVec 64) (n : Nat) :
    (a ||| c) >>> n = (a >>> n) ||| (c >>> n) := by
  ext i; simp only [BitVec.getElem_ushiftRight, BitVec.getElem_or, BitVec.getLsbD_or]

theorem varint_acc_shift_step (idx : Nat) (acc : BitVec 64) (b : BitVec 8)
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

end Symbolic.Swarm.TRREF.GrowthRecvPureB
