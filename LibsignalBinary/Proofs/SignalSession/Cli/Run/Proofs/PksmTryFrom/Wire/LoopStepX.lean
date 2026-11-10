/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArms
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKey
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32Arms
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArm

/-!
# `PreKeySignalMessage::try_from`: Protobuf Field-Merge Dispatch and Decode Loop

Combines the 8-way tag dispatch, `int32::merge`, `bytes::merge`, and `skip_field` arms into
`mergePreKeyField_cps`, single-iteration `preKeyStep_wp`, and fuel-inducted `preKeyDecodeLoop_ok` /
`preKeyDecodeLoopF4_ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

theorem L1_IS5Wire_LoopStep : True := trivial

/-! ## 1. Pure model lemmas -/

/-- `Pksm.mergeProtoField` returns a suffix of its input (analog of `Wire.mergeField_suffix`). -/
theorem mergePreKeyField_suffix {m m' : ProtoPreKeySignalMessage} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)} (h : Pksm.mergeProtoField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold Pksm.mergeProtoField at h
  split at h
  case h_1 | h_5 | h_6 | h_7 =>
    obtain ⟨⟨v, r⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact mergeUint32_suffix hm
  case h_2 | h_3 | h_4 | h_8 =>
    obtain ⟨⟨v, r⟩, hm, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    obtain ⟨k, hk, hr, -⟩ := mergeBytes_suffix hm
    exact ⟨k, hk, hr⟩
  case h_9 =>
    obtain ⟨r, hs, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact skipField_suffix hs

/-- Fuel monotonicity: any two fuels `≥ bs.length` give the same `Pksm.decodeProtoLoop` result. -/
theorem decodePreKeyLoop_fuel_mono :
    ∀ (fuel fuel' : Nat) (m : ProtoPreKeySignalMessage) (bs : List (BitVec 8)),
      bs.length ≤ fuel → bs.length ≤ fuel' →
      Pksm.decodeProtoLoop fuel m bs = Pksm.decodeProtoLoop fuel' m bs
  | _, _, _, [], _, _ => by simp [Pksm.decodeProtoLoop]
  | 0, _, _, _ :: _, h, _ => by simp at h
  | _ + 1, 0, _, _ :: _, _, h => by simp at h
  | fuel + 1, fuel' + 1, m, b0 :: bs1, h, h' => by
    simp only [Pksm.decodeProtoLoop]
    cases hdk : decodeKey (b0 :: bs1) with
    | none => rfl
    | some p =>
      obtain ⟨⟨tag, wt⟩, rest⟩ := p
      obtain ⟨k, hk1, hkl, hr, -, -⟩ := Wire.decodeKey_suffix hdk
      dsimp only
      cases hmf : Pksm.mergeProtoField m tag wt rest with
      | none => rfl
      | some q =>
        obtain ⟨m', rest'⟩ := q
        obtain ⟨k2, hk2, hr2⟩ := mergePreKeyField_suffix hmf
        dsimp only
        have hlen : rest'.length ≤ bs1.length := by
          rw [hr2, hr, List.length_drop, List.length_drop]
          simp only [List.length_cons]
          omega
        simp only [List.length_cons] at h h'
        exact decodePreKeyLoop_fuel_mono fuel fuel' m' rest' (by omega) (by omega)

/-! ## 2. `mergePreKeyField_cps`: dispatch `+0x170` → arms → `+0x0e4` / `+0x460` -/

/-- Full `PreKeySignalMessage::merge_field` dispatch at `+0x170` (analog of `mergeField_cps`):
tags 1/5/6/7 (int32), 2/3/4/8 (bytes), `≥ 9` (`skip_field`), continuing at `+0x0e4` on
`some (m', rest)` or exiting at `+0x460` on `none`.-/
theorem mergePreKeyField_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hint32 : Prost.Int32MergeOkExtX img A ext)
    (hskip : Prost.SkipFieldOkExtX img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x170#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (m' : ProtoPreKeySignalMessage) (rest : List (BitVec 8)) (s1 : State),
      Pksm.mergeProtoField m tag wt bs = some (m', rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m')
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : Pksm.mergeProtoField m tag wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  refine dispatchPK_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hF hsym htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hF1 hsym1 htr1 => ?_)
  · subst htag
    exact mergePreKeyId_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with preKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeBaseKey_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with baseKey := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeIdentityKey_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with identityKey := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeMessage_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with message := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeRegId_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with registrationId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeSignedPreKeyId_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with signedPreKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeKyberPreKeyId_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with kyberPreKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeKyberCiphertext_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with kyberCiphertext := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_cpsPK hskip hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt
      hsp1 hF1 hsym1 htr1 hlen
      (fun rest s2 hs => hcont m rest s2 (by simp [Pksm.mergeProtoField, recursionLimit, hs]))
      (fun hs => hnone (by simp [Pksm.mergeProtoField, recursionLimit, hs]))

/-! ## 3. `preKeyStep_wp`: one iteration `+0x0f4` → `+0x460` -/

/-- One iteration of the decode loop from `+0x0f4` on `b0 :: bs1`, given the `+0x0e4` loop
hypothesis `ih` at `fuel` (analog of `decodeLoop_f0_step_wp`).-/
theorem preKeyStep_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hSlow : PksmDecodeVarintSlowOk img A ext)
    (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    (hint32 : Prost.Int32MergeOkExtX img A ext)
    (hskip : Prost.SkipFieldOkExtX img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {fuel : Nat} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 32 →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (tryFromQp s0))
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64)
    (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 32) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0) := by
  refine decodeKeyPK_cpsX hFrom hSlow hvarint hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [Pksm.decodeProtoLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := Wire.decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by
    rw [hrest1_eq, List.length_drop]
  have hlen1 : rest1.length < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega) hlen
  refine SepWPp.advance_cursorPK ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine mergePreKeyField_cps hPush hint32 hskip hbytes hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt
    hsp1 hF1 hsym1 htr1 hlen1
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 => ?_)
    (fun hmf_none => by simp [Pksm.decodeProtoLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := mergePreKeyField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by
    rw [hrest2_eq, List.length_drop]
  refine SepWPp.advance_cursorPK ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1) = Pksm.decodeProtoLoop fuel m' rest2 := by
    simp [Pksm.decodeProtoLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 (by omega) (Nat.lt_of_le_of_lt (by omega) hlen1)

/-! ## 4. Fuel induction -/

/-- Full decode loop from `+0x0e4` to `+0x460` for any `fuel ≥ bs.length`.-/
theorem preKeyDecodeLoop_e4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hSlow : PksmDecodeVarintSlowOk img A ext)
    (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    (hint32 : Prost.Int32MergeOkExtX img A ext)
    (hskip : Prost.SkipFieldOkExtX img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} :
    ∀ (fuel : Nat) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 32 →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_wpX hpc hrun hregs hsp hF hsym htr rfl
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_wpX hpc hrun hregs hsp hF hsym htr rfl
    | cons b0 bs1 =>
      refine loopCheckPK_e4_cons_cpsX hpc hrun hregs hsp hF hsym htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hF1 hsym1 htr1
      exact preKeyStep_wp hFrom hPush hSlow hvarint hint32 hskip hbytes
        (preKeyDecodeLoop_e4 hFrom hPush hSlow hvarint hint32 hskip hbytes fuel)
        hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hF1 hsym1 htr1 hfuel hlen

private theorem sepWPp_to_proofLib {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    ProofLib.SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, _⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- `PreKeyDecodeLoopOk` from callee contracts. -/
theorem preKeyDecodeLoop_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hSlow : PksmDecodeVarintSlowOk img A ext)
    (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    (hint32 : Prost.Int32MergeOkExtX img A ext)
    (hskip : Prost.SkipFieldOkExtX img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext) :
    PreKeyDecodeLoopOk img A ext := by
  intro s0 sp' sret len ptr0 vb fuel s ptr bs m hpc hrun hregs hsp hF hsym htr hfuel hlen
  exact sepWPp_to_proofLib (preKeyDecodeLoop_e4 hFrom hPush hSlow hvarint hint32 hskip hbytes fuel
    hpc hrun hregs hsp hF hsym htr hfuel hlen)

/-- `PreKeyDecodeLoopF4Ok`. -/
theorem preKeyDecodeLoopF4_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : PksmDecodeErrorFromOk img A ext)
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hSlow : PksmDecodeVarintSlowOk img A ext)
    (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    (hint32 : Prost.Int32MergeOkExtX img A ext)
    (hskip : Prost.SkipFieldOkExtX img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext) :
    PreKeyDecodeLoopF4Ok img A ext := by
  intro s0 sp' sret len ptr0 vb fuel s ptr b0 bs1 m hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr
    hfuel hlen
  exact sepWPp_to_proofLib (preKeyStep_wp hFrom hPush hSlow hvarint hint32 hskip hbytes
    (preKeyDecodeLoop_e4 hFrom hPush hSlow hvarint hint32 hskip hbytes fuel)
    hpc hrun hregs hx28 hx26 hx2 hsp hF hsym htr hfuel hlen)

/-- Convenience wrapper discharging `PreKeyDecodeLoopOk` from `PksmCallees`. -/
theorem preKeyDecodeLoop_of_callees_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext) :
    PreKeyDecodeLoopOk img A ext :=
  preKeyDecodeLoop_ok hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
    hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge

/-- Convenience wrapper discharging `PreKeyDecodeLoopF4Ok` from `PksmCallees`. -/
theorem preKeyDecodeLoopF4_of_callees_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : PksmCallees img A ext) :
    PreKeyDecodeLoopF4Ok img A ext :=
  preKeyDecodeLoopF4_ok hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
    hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
