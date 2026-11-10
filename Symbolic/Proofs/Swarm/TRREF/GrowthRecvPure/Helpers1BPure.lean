/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1APure
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top -- shake: keep

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Top.StateSize CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

theorem encodeVarintAux_fuel_mono :
    ∀ (fuel : Nat) (v : BitVec 64),
      (Proto.encodeVarintAux fuel v).length ≤ (Proto.encodeVarintAux (fuel + 1) v).length
  | 0, v => by unfold Proto.encodeVarintAux; split <;> simp
  | fuel + 1, v => by
    conv_lhs => unfold Proto.encodeVarintAux
    conv_rhs => unfold Proto.encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have ih := encodeVarintAux_fuel_mono fuel (v >>> 7)
      omega

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
    · have hlen_w : (Proto.encodeVarintAux (fuel + 1) w).length = 1 := by
        simp [Proto.encodeVarintAux, hw]
      omega
    · have hlen_w : (Proto.encodeVarintAux (fuel + 1) w).length =
          (Proto.encodeVarintAux fuel (w >>> 7)).length + 1 := by
        simp [Proto.encodeVarintAux, hw]
      by_cases hu : u < 128#64
      · have hlen_u : (Proto.encodeVarintAux (fuel + 1) u).length = 1 := by
          simp [Proto.encodeVarintAux, hu]
        have hfu : (Proto.encodeVarintAux fuel u).length = 1 := by
          cases fuel with
          | zero => simp [Proto.encodeVarintAux]
          | succ f => simp [Proto.encodeVarintAux, hu]
        by_cases hv : v < 128#64
        · have hlen_v : (Proto.encodeVarintAux (fuel + 1) v).length = 1 := by
            simp [Proto.encodeVarintAux, hv]
          have hw7 : w >>> 7 < 128#64 := by
            have : u.toNat < 128 := by simpa [BitVec.lt_def] using hu
            have : v.toNat < 128 := by simpa [BitVec.lt_def] using hv
            have : (w >>> 7).toNat < 128 := by rw [BitVec.toNat_ushiftRight]; omega
            simpa [BitVec.lt_def] using this
          have hlen7 : (Proto.encodeVarintAux fuel (w >>> 7)).length = 1 := by
            cases fuel with
            | zero => simp [Proto.encodeVarintAux]
            | succ f => simp [Proto.encodeVarintAux, hw7]
          omega
        · have hlen_v : (Proto.encodeVarintAux (fuel + 1) v).length =
              (Proto.encodeVarintAux fuel (v >>> 7)).length + 1 := by
            simp [Proto.encodeVarintAux, hv]
          have hvge : 128 ≤ v.toNat := by simpa [BitVec.lt_def] using hv
          have hshift : (w >>> 7).toNat ≤ u.toNat + (v >>> 7).toNat := by
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]; omega
          have ih := encodeVarintAux_subadd fuel hshift
          omega
      · have hlen_u : (Proto.encodeVarintAux (fuel + 1) u).length =
            (Proto.encodeVarintAux fuel (u >>> 7)).length + 1 := by
          simp [Proto.encodeVarintAux, hu]
        have huge : 128 ≤ u.toNat := by simpa [BitVec.lt_def] using hu
        have hshift : (w >>> 7).toNat ≤ (u >>> 7).toNat + v.toNat := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight]; omega
        have ih := encodeVarintAux_subadd fuel hshift
        omega

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
  unfold Proto.mergeUint32 Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_eq_ok h with ⟨⟨v64, rest0⟩, hdv, h⟩
    dsimp only at h
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have hd := decodeVarint_encodeVarint_length_le hdv
    have hle : (v64.truncate 32).zeroExtend 64 ≤ v64 := by
      simp only [BitVec.le_def, BitVec.toNat_setWidth]
      exact Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)
    have hm := encodeVarint_mono hle
    unfold Proto.encodeUint32Field
    split
    · simp; omega
    · rw [List.length_append, htag]; omega

theorem mergeBytes_encodeBytesField_length_le (tag : BitVec 32) {wt : Proto.WireType} {bs rest v : Bytes}
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (h : Proto.mergeBytes wt bs = .ok (v, rest)) :
    (Proto.encodeBytesField tag v).length + rest.length ≤ bs.length + 1 := by
  unfold Proto.mergeBytes Proto.checkWireType at h
  split at h
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_eq_ok h with ⟨⟨len, rest0⟩, hdv, h⟩
    dsimp only at h
    have hd := decodeVarint_encodeVarint_length_le hdv
    rcases takeExact_length_eq h with ⟨hvlen, hsum⟩
    have hlen_eq : BitVec.ofNat 64 v.length = len := by
      rw [hvlen, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    unfold Proto.encodeBytesField
    split
    · simp; omega
    · unfold Proto.encodeBytesUncond
      rw [List.length_append, List.length_append, htag, hlen_eq]; omega

theorem epochDir_mergeField_length_le (depth : Nat) (m : EpochDirectionPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : EpochDirectionPB) (rest' : Bytes)
    (h : EpochDirectionPB.mergeField m tag wt rest depth = .ok (m', rest')) :
    (EpochDirectionPB.encodeRaw m').length + rest'.length ≤
      (EpochDirectionPB.encodeRaw m).length + rest.length + 1 := by
  unfold EpochDirectionPB.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeUint32_encodeUint32Field_length_le 1#32 rfl hm
    simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h2 := mergeBytes_encodeBytesField_length_le 2#32 rfl hm
      simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h3 := mergeBytes_encodeBytesField_length_le 3#32 rfl hm
        simp only [EpochDirectionPB.encodeRaw, List.length_append] at *; omega
      · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have hs := skipField_length_le hskip; omega

theorem mergeOptMessage_epochDir_length_le (tag : BitVec 32) (wt : Proto.WireType)
    (opt opt' : Option EpochDirectionPB) (rest rest' : Bytes) (depth : Nat)
    (htag : (Proto.encodeKey tag .lengthDelimited).length = 1)
    (hlt : (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt).length + rest.length < 2 ^ 64)
    (h : Proto.mergeOptMessage EpochDirectionPB.mergeField wt opt rest depth = .ok (opt', rest')) :
    (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt').length + rest'.length ≤
      (Proto.encodeOptMessage EpochDirectionPB.encodeRaw tag opt).length + rest.length + 1 := by
  unfold Proto.mergeOptMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨d0', after⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rename_i depth'
      rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after0⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨d', hloop, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake hloop
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
        have hm_var := encodeVarint_subadd hsubadd
        omega

theorem chainEpoch_mergeField_length_le (m : ChainEpochPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (depth : Nat) (m' : ChainEpochPB) (rest' : Bytes)
    (hlt : (ChainEpochPB.encodeRaw m).length + rest.length < 2 ^ 64)
    (h : ChainEpochPB.mergeField m tag wt rest depth = .ok (m', rest')) :
    (ChainEpochPB.encodeRaw m').length + rest'.length ≤
      (ChainEpochPB.encodeRaw m).length + rest.length + 1 := by
  unfold ChainEpochPB.mergeField at h
  simp only [ChainEpochPB.encodeRaw, List.length_append] at hlt
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeOptMessage_epochDir_length_le 1#32 wt m.send v rest bs' depth rfl (by omega) hm
    simp only [ChainEpochPB.encodeRaw, List.length_append]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h2 := mergeOptMessage_epochDir_length_le 2#32 wt m.recv v rest bs' depth rfl (by omega) hm
      simp only [ChainEpochPB.encodeRaw, List.length_append]; omega
    · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have hs := skipField_length_le hskip
      simp only [ChainEpochPB.encodeRaw, List.length_append]; omega

@[scoped simp]
theorem encodeRepeatedMessage_cons {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32)
    (m : M) (ms : List M) :
    Proto.encodeRepeatedMessage encodeRaw tag (m :: ms) =
      Proto.encodeMessage encodeRaw tag m ++ Proto.encodeRepeatedMessage encodeRaw tag ms := rfl

theorem encodeRepeatedMessage_append {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32)
    (ms : List M) (m : M) :
    Proto.encodeRepeatedMessage encodeRaw tag (ms ++ [m]) =
      Proto.encodeRepeatedMessage encodeRaw tag ms ++ Proto.encodeMessage encodeRaw tag m := by
  induction ms with
  | nil => simp [Proto.encodeRepeatedMessage]
  | cons x xs ih =>
    simp only [List.cons_append, encodeRepeatedMessage_cons, ih, List.append_assoc]

theorem mergeRepeatedMessage_chainEpoch_length_le (wt : Proto.WireType)
    (ms ms' : List ChainEpochPB) (rest rest' : Bytes) (depth : Nat)
    (h : Proto.mergeRepeatedMessage ChainEpochPB.mergeField wt ms rest depth = .ok (ms', rest')) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ms').length + rest'.length ≤
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ms).length + rest.length + 1 := by
  unfold Proto.mergeRepeatedMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨e0', after⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
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
  rcases except_bind_eq_ok h with ⟨⟨m0', after0⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
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
      cases opt with
      | none => simp only [Option.getD_none, hdef, Nat.zero_add, optWeight] at hm1 ⊢; omega
      | some m0 => simp only [Option.getD_some, optWeight] at hm1 ⊢; omega

theorem mergeOptMessage_rest_length_le {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (wt : Proto.WireType) (opt opt' : Option M) (bs after : Bytes) (depth : Nat)
    (h : Proto.mergeOptMessage mergeField wt opt bs depth = .ok (opt', after)) :
    after.length + 1 ≤ bs.length := by
  unfold Proto.mergeOptMessage Proto.mergeMessage Proto.checkWireType at h
  rcases except_bind_eq_ok h with ⟨⟨m', after0⟩, hm, h⟩
  rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
  split at hm
  · contradiction
  · dsimp only [Bind.bind, Except.bind] at hm
    split at hm
    · contradiction
    · rcases except_bind_eq_ok hm with ⟨⟨len, rest0⟩, hdv, hm⟩
      rcases except_bind_eq_ok hm with ⟨⟨sub, after1⟩, htake, hm⟩
      rcases except_bind_eq_ok hm with ⟨m1, _, hm⟩
      rcases Prod.mk.inj (Except.ok.inj hm) with ⟨rfl, rfl⟩
      dsimp only at htake ⊢
      have hdv_lt := decodeVarint_length_lt hdv
      rcases takeExact_length_eq htake with ⟨_, htake_sum⟩
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
  unfold ChainPB.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    have h1 := mergeInt32_length_lt hm; simp only [chainWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h1 := mergeUint64_length_lt hm; simp only [chainWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h1 := mergeRepeatedMessage_chainEpoch_length_le wt m.links v rest bs' d hm
        simp only [chainWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
          rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [chainWeight]; omega
        · split at h
          · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
            rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
            have h1 := mergeUint64_length_lt hm; simp only [chainWeight]; omega
          · split at h
            · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
              rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
              have h1 := mergeOptMessage_rest_length_le ChainParamsPB.mergeField wt m.params v rest bs' d hm
              simp only [chainWeight]; omega
            · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
              rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
              have hs := skipField_length_le hskip; simp only [chainWeight]; omega

def vnWeight (v : VersionNegotiationPB) : Nat := v.authKey.length

def optVnWeight : Option VersionNegotiationPB → Nat := optWeight vnWeight

theorem vnPB_mergeField_weight_le (d : Nat) (m : VersionNegotiationPB) (tag : BitVec 32) (wt : Proto.WireType)
    (rest : Bytes) (m' : VersionNegotiationPB) (rest' : Bytes)
    (h : VersionNegotiationPB.mergeField m tag wt rest d = .ok (m', rest')) :
    vnWeight m' + rest'.length ≤ vnWeight m + rest.length + 1 := by
  unfold VersionNegotiationPB.mergeField at h
  split at h
  · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
    rcases mergeBytes_length_le hm with ⟨h1, _⟩; simp only [vnWeight]; omega
  · split at h
    · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
      rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
      have h1 := mergeInt32_length_lt hm; simp only [vnWeight]; omega
    · split at h
      · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
        rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
        have h1 := mergeInt32_length_lt hm; simp only [vnWeight]; omega
      · split at h
        · rcases except_bind_eq_ok h with ⟨⟨v, bs'⟩, hm, h⟩
          rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have h1 := mergeOptMessage_rest_length_le ChainParamsPB.mergeField wt m.chainParams v rest bs' d hm
          simp only [vnWeight]; omega
        · rcases except_bind_eq_ok h with ⟨bs', hskip, h⟩
          rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩
          have hs := skipField_length_le hskip; simp only [vnWeight]; omega

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
  have h2 : (Proto.encodeUint64Field 2#32 c.currentEpoch).length ≤ 22 := by
    unfold Proto.encodeUint64Field; split; · simp
    · rw [List.length_append]; have := encodeKey_length_le 2#32 .varint; have := encodeVarint_length_le c.currentEpoch; omega
  have h4 := encodeBytesField_length_le 4#32 c.nextRoot
  have h5 : (Proto.encodeUint64Field 5#32 c.sendEpoch).length ≤ 22 := by
    unfold Proto.encodeUint64Field; split; · simp
    · rw [List.length_append]; have := encodeKey_length_le 5#32 .varint; have := encodeVarint_length_le c.sendEpoch; omega
  have h6 := chainParamsPB_encodeOptMessage_length_le 6#32 c.params
  simp only [Proto.encodeOptMessage, chainWeight]; omega

end Symbolic.Swarm.TRREF.GrowthRecvPureB
