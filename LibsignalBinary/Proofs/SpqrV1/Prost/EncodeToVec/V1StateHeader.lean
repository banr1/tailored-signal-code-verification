/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
import ProofLib.SepLogic.WPp

/-!
# Phase 2d Header & Jump-Table Dispatch (`+1740 .. +1896`, `0x6d6dc .. 0x6d778`)

Proves `Option` niche-cap / remainder splits for `V1State` variants, symbolic execution of the
`st.inner` / `v1.innerState` header checks (`+1740 .. +1880`), and the `.rodata` half-word
jump-table dispatch macro (`+1880 .. +1896`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Self-Contained `Option` Cap / Rest Splits for `V1State` Variants -/

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  have h1 : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  rw [bne_iff_ne, ne_eq, ← beq_iff_eq, cap_add_two_beq_zero_false h]
  decide

theorem cap_xor_top_ult_11_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ((cap ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  have hlt : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem optCt1SentRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem optCt1SentRest_disc_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 2#64 == 0#64) = false ∧
      (optCt1SentCap g opt + 2#64 != 0#64) = true ∧
      ((optCt1SentCap g opt ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  cases opt with
  | none => simp [optCt1SentCap, noneCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap,
      cap_xor_top_ult_11_false hcap⟩

def optEkSentCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.EkSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optEkSentRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optEkSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCap g opt) ∗ optEkSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentPBPinnedAt, ekSentPBPinnedAt, unchunked3PinnedAt,
      optEkSentCap, optEkSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentRest A g p opt ∗ R) :
    (optEkSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCap, arm64_norm]
  | some u =>
    simp only [optEkSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optPolyEncCap (g : PolynomialEncoderPBGhost) : Option PolynomialEncoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

def optPolyEncRest (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64) :
    Option PolynomialEncoder → SepProp
  | none => memRegion (p + 8#64) 48
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
      ((p + 48#64) ↦₃₂ pb.idx) ∗
      memRegion (p + 52#64) 4

theorem optPolynomialEncoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialEncoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyEncCap g opt) ∗ optPolyEncRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialEncoderPBPinnedAt, polynomialEncoderPBPinnedAt,
      optPolyEncCap, optPolyEncRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyEncRest_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyEncRest A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyEncCap, arm64_norm]
  | some pb =>
    simp only [optPolyEncRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         vecVecU8PinnedAt A g.polys (p + 24#64) pb.polys ∗
         ((p + 48#64) ↦₃₂ pb.idx) ∗ memRegion (p + 52#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optPolyDecCap (g : PolynomialDecoderPBGhost) : Option PolynomialDecoder → BitVec 64
  | none => noneCap
  | some _ => g.pts.cap

def optPolyDecRest (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64) :
    Option PolynomialDecoder → SepProp
  | none => memRegion (p + 8#64) 32
  | some pb =>
    ((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
      ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗
      ((p + 28#64) ↦₃₂ pb.polys) ∗
      ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗
      memRegion (p + 33#64) 7

theorem optPolynomialDecoderPBPinnedAt_eq (A : RustAlloc) (g : PolynomialDecoderPBGhost) (p : BitVec 64)
    (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBPinnedAt A g p opt =
      (p ↦₆₄ optPolyDecCap g opt) ∗ optPolyDecRest A g p opt := by
  cases opt with
  | none => rfl
  | some pb =>
    simp only [optPolynomialDecoderPBPinnedAt, polynomialDecoderPBPinnedAt,
      optPolyDecCap, optPolyDecRest, vecVecU8PinnedAt_eq_header_buf A g.pts p, sepConj_assoc]

theorem optPolyDecRest_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoder} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolyDecRest A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optPolyDecCap, arm64_norm]
  | some pb =>
    simp only [optPolyDecRest] at hm
    have hbuf : m ⊨ vecVecU8Buf A g.pts.cap g.pts.ptr pb.pts ∗
        (((p + 8#64) ↦₆₄ g.pts.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         ((p + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((p + 28#64) ↦₃₂ pb.polys) ∗
         ((p + 32#64) ↦₈ boolByte pb.isComplete) ∗ memRegion (p + 33#64) 7 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap24⟩ := vecVecU8Buf_bounds hbuf
    have hcap : g.pts.cap.toNat < 2 ^ 63 := by omega
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optUnchunked2Cap (g : Unchunked2PBGhost) : Option (Option AuthenticatorPB) → BitVec 64
  | none => noneCap2
  | some auth => optAuthCap g auth

def optUnchunked2Rest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64) :
    Option (BitVec 64 × Option AuthenticatorPB) → SepProp
  | none => memRegion (p + 8#64) 48
  | some (epoch, auth) =>
    optAuthPayload A g p auth ∗ ((p + 48#64) ↦₆₄ epoch)

theorem optUnchunked2Rest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option (BitVec 64 × Option AuthenticatorPB)} {R : SepProp} {m : Memory}
    (hm : m ⊨ optUnchunked2Rest A g p opt ∗ R) :
    (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 == 0#64) = !opt.isSome ∧
      (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optUnchunked2Cap, noneCap2, arm64_norm]
  | some pair =>
    rcases pair with ⟨epoch, auth⟩
    cases auth with
    | none =>
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨by decide, by decide⟩
    | some a =>
      simp only [optUnchunked2Rest, optAuthPayload] at hm
      have hbuf : m ⊨ vecU8Buf A g.rootKey.cap g.rootKey.ptr a.rootKey ∗
          (((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 a.rootKey.length) ∗
           ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
           ((p + 40#64) ↦₆₄ BitVec.ofNat 64 a.macKey.length) ∗
           vecU8Buf A g.macKey.cap g.macKey.ptr a.macKey ∗
           ((p + 48#64) ↦₆₄ epoch) ∗ R) := by
        convert hm using 1; ac_rfl
      have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap⟩

def optKeysUnsampledCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.KeysUnsampled) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optKeysUnsampledRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optKeysUnsampledPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBPinnedAt A g p opt =
      (p ↦₆₄ optKeysUnsampledCap g opt) ∗ optKeysUnsampledRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optKeysUnsampledPBPinnedAt, keysUnsampledPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optKeysUnsampledCap, optKeysUnsampledRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optKeysUnsampledRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledRest A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optKeysUnsampledCap] using h

def optNoHeaderReceivedCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.NoHeaderReceived) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optNoHeaderReceivedRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optNoHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optNoHeaderReceivedCap g opt) ∗ optNoHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optNoHeaderReceivedCap, optNoHeaderReceivedRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optNoHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedRest A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optNoHeaderReceivedCap] using h

def optCt2SentCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.Ct2Sent) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optCt2SentRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optCt2SentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBPinnedAt A g p opt =
      (p ↦₆₄ optCt2SentCap g opt) ∗ optCt2SentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt2SentPBPinnedAt, ct2SentPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optCt2SentCap, optCt2SentRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optCt2SentRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentRest A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optCt2SentCap] using h

def optHeaderReceivedCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.HeaderReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optHeaderReceivedRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderReceivedCap g opt) ∗ optHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderReceivedPBPinnedAt, headerReceivedPBPinnedAt, unchunked3PinnedAt,
      optHeaderReceivedCap, optHeaderReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedRest A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderReceivedCap, arm64_norm]
  | some u =>
    simp only [optHeaderReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optHeaderSentCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.HeaderSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optHeaderSentRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optHeaderSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderSentCap g opt) ∗ optHeaderSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderSentPBPinnedAt, headerSentPBPinnedAt, unchunked4PinnedAt,
      optHeaderSentCap, optHeaderSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderSentRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentRest A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderSentCap, arm64_norm]
  | some u =>
    simp only [optHeaderSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optEkSentCt1ReceivedCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.EkSentCt1Received → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optEkSentCt1ReceivedRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optEkSentCt1ReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCt1ReceivedCap g opt) ∗ optEkSentCt1ReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentCt1ReceivedPBPinnedAt, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt,
      optEkSentCt1ReceivedCap, optEkSentCt1ReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentCt1ReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedRest A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCt1ReceivedCap, arm64_norm]
  | some u =>
    simp only [optEkSentCt1ReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

def optCt1SentEkReceivedCap (g : Unchunked5PBGhost) : Option V1State.Unchunked.Ct1SentEkReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optCt1SentEkReceivedRest (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => memRegion (p + 8#64) 120
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
      vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
      ((p + 0x78#64) ↦₆₄ u.epoch)

theorem optCt1SentEkReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optCt1SentEkReceivedCap g opt) ∗ optCt1SentEkReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt1SentEkReceivedPBPinnedAt, ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt,
      optCt1SentEkReceivedCap, optCt1SentEkReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optCt1SentEkReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedRest A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentEkReceivedCap, arm64_norm]
  | some u =>
    simp only [optCt1SentEkReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem optKeysUnsampledPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledPBPinnedAt A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optKeysUnsampledPBPinnedAt_eq, sepConj_assoc] at hm
  exact optKeysUnsampledRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optNoHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optNoHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optNoHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt2SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentPBPinnedAt A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optCt2SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt2SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderSentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentPBPinnedAt A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderSentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderSentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optEkSentCt1ReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedPBPinnedAt A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optEkSentCt1ReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optEkSentCt1ReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentEkReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedPBPinnedAt A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentEkReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentEkReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentPBPinnedAt A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialEncoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialEncoderPBPinnedAt A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialEncoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyEncRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialDecoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialDecoderPBPinnedAt A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialDecoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyDecRest_cap_bounds (Satisfies.of_sep_right hm)

theorem encodeInner_v1_eq (v1 : V1State) :
    PqRatchetState.Inner.encode (.v1 v1) =
      ([0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ++
        V1State.encodeRaw v1 := by
  dsimp only [PqRatchetState.Inner.encode, Proto.encodeMessage]
  rw [show Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] from rfl,
    ← v1StatePBEncodedLen_eq_proto, V1State.encodedLen, List.append_assoc]

/-- Bundles the `ADRP X9` (`+1872`, `0x6d760`) and `ADD X9, X9, #loOff` (`+1876`, `0x6d764`)
instructions and their resolved `.rodata` jump-table base address `b + 0xa1480#64`. -/
def HasEncodeToVecJumpTableAddr (b : BitVec 64) (ext : String → Option (State → State))
    (entry roBase : BitVec 64) : Prop :=
  ∃ (pageOff : BitVec 64) (loOff : BitVec 12),
    (spqrProgAtExt b ext).fetch (entry + 1872#64) =
      some (.adr true .x9 pageOff) ∧
    (spqrProgAtExt b ext).fetch (entry + 1876#64) =
      some (.addSubImm .W64 .ADD .x9 .x9 loOff false) ∧
    ((entry + 1872#64) &&& 0xfffffffffffff000#64) + pageOff + loOff.zeroExtend 64 = roBase

theorem hasEncodeToVecJumpTableAddr (b : BitVec 64) (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64) :
    HasEncodeToVecJumpTableAddr b ext
      ((spqrProgAtExt b ext).fnAddr spqrEncodeToVecName)
      (b + bv% (ls_bytes% "0000d50046009c001400ee00fd00b50025012d001601")) := by
  refine ⟨_, _,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 1872)
      libsignalSessionCode_fnOff_0x67c18 (by decide) spqrEncodeToVecBin_decode_0x68368,
    libsignalSessionCode_fetch_fnAddr (b := b) (H := Rust.withPanics ext) (k := 1876)
      libsignalSessionCode_fnOff_0x67c18 (by decide) spqrEncodeToVecBin_decode_0x6836c,
    ?_⟩
  rw [spqrProgAtExt, Program.fnAddr_rebase, spqrEncodeToVec_fnOff]
  dsimp [BitVec.zeroExtend]
  clear *- hb
  bv_kernel

theorem v1StateInnerCap_add_two_bounds {A : RustAlloc} {g : V1StatePBGhost} {p : BitVec 64}
    {is : V1State.InnerState} {R : SepProp} {m : Memory}
    (hm : m ⊨ v1StateInnerPBPinnedAt A g p is ∗ R) :
    (v1StateInnerCap g is + 2#64 == 0#64) = false ∧
      (v1StateInnerCap g is + 2#64 != 0#64) = true := by
  cases is with
  | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
  | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
  | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
    dsimp only [v1StateInnerCap]
    exact ⟨by decide, by decide⟩
  | ct1Sampled v =>
    cases huc : v.uc with
    | none =>
      dsimp only [v1StateInnerCap]
      rw [huc]
      dsimp only [optCt1SentCap]
      exact ⟨by decide, by decide⟩
    | some u =>
      rw [v1StateInnerPBPinnedAt_eq, sepConj_assoc] at hm
      have hrest := Satisfies.of_sep_right hm
      simp only [v1StateInnerRest, huc, optCt1SentRest] at hrest
      have hbuf : m ⊨ EncodedLen.vecU8Buf A g.b.gCt1Sampled.uc.f3.cap g.b.gCt1Sampled.uc.f3.ptr u.hdr ∗
          (((p + 8#64) ↦₆₄ g.b.gCt1Sampled.uc.f3.ptr) ∗
           ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
           vecU8At A (p + 0x18#64) g.b.gCt1Sampled.uc.f4.cap g.b.gCt1Sampled.uc.f4.ptr u.es ∗
           vecU8At A (p + 0x30#64) g.b.gCt1Sampled.uc.f5.cap g.b.gCt1Sampled.uc.f5.ptr u.ct1 ∗
           optAuthenticatorPBPinnedAt A g.b.gCt1Sampled.uc.auth (p + 0x48#64) u.auth ∗
           ((p + 0x78#64) ↦₆₄ u.epoch) ∗
           optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (p + 128#64) v.sendingCt1 ∗
           optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (p + 184#64) v.receivingEk ∗ R) := by
        convert hrest using 1; ac_rfl
      have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
      simp only [v1StateInnerCap, huc, optCt1SentCap]
      have hne : g.b.gCt1Sampled.uc.f3.cap + 2#64 ≠ 0#64 := by bv_omega
      exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Step `+1740 .. +1808` (`0x6d6dc .. 0x6d720`) when `st.inner = none` (`x28 = noneCap3`). -/
theorem step_encodeToVec_inner_none
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap3) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1740 1748
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv)

/-- Step `+1740 .. +1800` (`0x6d6dc .. 0x6d718`) when `st.inner = some (.v1 v1)`:
writes outer tag `0x1a#8`, calls `V1State::encoded_len [local#2]` (`0x67df8`), and calls
`encode_varint` (`0x4d710`). -/
theorem step_encodeToVec_inner_some_hdr {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hv1Len : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709530600#64)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))))
    (hvarint : subroutine_ok (spqrProgAtExt b ext) (entry + 18446744073709422336#64)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (v1 : V1State) (bs : List (BitVec 8))
    (hv1_len : v1StatePBEncodedLen v1 < 2 ^ 64)
    (hfit : bs.length + 1 +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)))
    (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1800#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)) →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((v1StatePBPinnedAt A g (a + 128#64) v1 ∗
          ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
          vecU8At A (sp - 120#64) cap ptr
            ((bs ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1740 1800
  examples_hide_fetches; subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 == 0#64) = false ∧
      (optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 != 0#64) = true)
    (fun R' hm => by
      have hm' : s.mem ⊨ optPqRatchetInnerPBPinnedAt A g (a + 128#64) (some (.v1 v1)) ∗
          (((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        dsimp only [optPqRatchetInnerPBPinnedAt]; convert hm using 1; ac_rfl
      exact optPqRatchetInnerPBPinnedAt_cap_bounds hm')
    fun ⟨hw_beq3, hw_bne3⟩ => ?_
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709530600#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine step_etv_v1State_encLen_call hres b A ext hv1Len
    (a + 128#64) sp (entry + 1792#64) g v1 hv1_len
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm, hx20, hx21, hx28] at hm20 hm21 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := entry + 18446744073709422336#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine step_etv_encode_varint_call b A ext hvarint
    (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) (sp - 120#64) cap ptr sp (entry + 1800#64)
    (bs ++ [0x1a#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
    (F := v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      ((b + bv% (ls_xref% 0x62a38 0x62a3c)) ↦ᵣ v1StateJumpTableBytes) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨_, hm2_20, hm2_21, _, _, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩
  simp only [arm64_norm, hm20, hm21, hm27, hm28, hmfp] at hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `+1800 .. +1808` (`0x6d718 .. 0x6d720`) when `v1.innerState = none` (`x28 = noneCap2`). -/
theorem step_encodeToVec_inner_v1_none
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap2) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1800 1808
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 1808#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv)

/-- Step `+1800 .. +1880` (`0x6d718 .. 0x6d768`) when `v1.innerState = some is`:
branches to `+1856`, computes jump-table index in `x8`, and loads `.rodata` jump-table base
address `roBase` (`b + 0xa1480#64`) into `x9`. -/
theorem step_encodeToVec_inner_to_1880
    (b : BitVec 64) (ext : String → Option (State → State))
    {entry roBase : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (hjt : HasEncodeToVecJumpTableAddr b ext entry roBase)
    {s0 s : State}
    (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = w) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = entry + 1880#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = roBase →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = w →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 1800 1808
  etv_fetches b (Rust.withPanics ext) hfn 1856 1872
  rcases hjt with ⟨pageOff, loOff, hf1872, hf1876, hro⟩
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs (mid := entry + 1880#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, ← BitVec.add_assoc, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv)

/-- Execute the `.rodata` half-word jump table dispatch at `+1880 .. +1896` (`0x6d768 .. 0x6d778`)
from `entry + 1880#64` to `entry + off`. -/
macro "step_etv_jump_to " entry:term:max off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    dsimp only [encodeToVecJumpTableBytes8At]
    apply SepWPp.of_sepWP_cs (mid := $entry + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])))

end CryptoVerification.SpqrV1.Prost.EncodeToVec
