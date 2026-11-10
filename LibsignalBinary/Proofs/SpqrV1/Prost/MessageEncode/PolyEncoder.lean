/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<PolynomialEncoder, Vec<u8>> [local#2]` (`0x526d4`)

Separation Logic `subroutine_ok` proofs for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]`
  at `0x526d4` (`59` insns, `236` bytes)
Also re-exports `[local#1]` from `PolyEncoder1.lean`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

def IsPe2EntryProg (prog : Program)
    (entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64) : Prop :=
  (∃ (b : BitVec 64) (ext : String → Option (State → State)),
    prog = tripleRatchetProgAtExt b ext ∧
    (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name = entry ∧
    encLenTarget = entry + 82712#64 ∧
    encVarintTarget = entry + 18446744073709531196#64 ∧
    encRepTarget = entry + 18446744073709529452#64 ∧
    doReserveTarget = entry + 2508#64) ∨
  (∃ (lsmpl : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_316 H ∧ entry = (blkPl_316).base ∧
    encLenTarget = (blkPl_401).base ∧
    encVarintTarget = (blkPl_292).base ∧
    encRepTarget = (blkPl_289).base ∧
    doReserveTarget = (blkPl_320).base)

private theorem isPolyEncoderEncodeEntryProg_of_pe2 {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (h : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget) :
    IsPolyEncoderEncodeEntryProg prog entry := by
  rcases h with ⟨b, ext, rfl, hfn, _, _, _, _⟩ | ⟨lsmpl, H, rfl, rfl, _, _, _, _⟩
  · exact Or.inl ⟨b, ext, rfl, Or.inr hfn⟩
  · exact Or.inr (Or.inr ⟨lsmpl, H, rfl, rfl⟩)

private theorem pe2_fetch_add {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {ins : Instr}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) = some ins)
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, ext, rfl, rfl, _, _, _, _⟩ | ⟨lsmpl, H, rfl, rfl, _, _, _, _⟩
  · exact h1 b ext
  · exact @hp2 lsmpl H

private theorem pe2_fetch_bl_encLen {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) =
        some (.bl (82712 - BitVec.ofNat 64 k)))
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_316).ρ polynomialEncoderEncodedLenLocal2Name - (blkPl_316).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (encLenTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, rfl, _, _, _⟩ | ⟨inst, H, rfl, rfl, rfl, _, _, _⟩
  · rw [show ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 82712#64 -
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k)) =
      82712#64 - BitVec.ofNat 64 k by bv_omega]
    exact h1 b ext
  · letI := inst
    have h := @hp2 inst H
    simp only [polynomialEncoderEncodedLenLocal2Name, blkPl_316_ρ, ls_resolve_blk_401] at h
    have heq : lsmpl.base 401 - (blkPl_316).base - BitVec.ofNat 64 k =
        (blkPl_401).base - ((blkPl_316).base + BitVec.ofNat 64 k) := by
      change (blkPl_401).base - (blkPl_316).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pe2_fetch_bl_varint {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) =
        some (.bl (18446744073709531196 - BitVec.ofNat 64 k)))
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_316).ρ encodeVarint4Name - (blkPl_316).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (encVarintTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, _, rfl, _, _⟩ | ⟨inst, H, rfl, rfl, _, rfl, _, _⟩
  · rw [show ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709531196#64 -
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k)) =
      18446744073709531196#64 - BitVec.ofNat 64 k by bv_omega]
    exact h1 b ext
  · letI := inst
    have h := @hp2 inst H
    simp only [encodeVarint4Name, blkPl_316_ρ, ls_resolve_blk_292] at h
    have heq : lsmpl.base 292 - (blkPl_316).base - BitVec.ofNat 64 k =
        (blkPl_292).base - ((blkPl_316).base + BitVec.ofNat 64 k) := by
      change (blkPl_292).base - (blkPl_316).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pe2_fetch_bl_rep {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) =
        some (.bl (18446744073709529452 - BitVec.ofNat 64 k)))
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_316).ρ encodeRepeated2Name - (blkPl_316).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (encRepTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, _, _, rfl, _⟩ | ⟨inst, H, rfl, rfl, _, _, rfl, _⟩
  · rw [show ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64 -
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k)) =
      18446744073709529452#64 - BitVec.ofNat 64 k by bv_omega]
    exact h1 b ext
  · letI := inst
    have h := @hp2 inst H
    simp only [encodeRepeated2Name, blkPl_316_ρ, ls_resolve_blk_289] at h
    have heq : lsmpl.base 289 - (blkPl_316).base - BitVec.ofNat 64 k =
        (blkPl_289).base - ((blkPl_316).base + BitVec.ofNat 64 k) := by
      change (blkPl_289).base - (blkPl_316).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pe2_fetch_b_rep {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) =
        some (.b (18446744073709529452 - BitVec.ofNat 64 k)))
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) =
        some (.b ((blkPl_316).ρ encodeRepeated2Name - (blkPl_316).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.b (encRepTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, _, _, rfl, _⟩ | ⟨inst, H, rfl, rfl, _, _, rfl, _⟩
  · rw [show ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64 -
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k)) =
      18446744073709529452#64 - BitVec.ofNat 64 k by bv_omega]
    exact h1 b ext
  · letI := inst
    have h := @hp2 inst H
    simp only [encodeRepeated2Name, blkPl_316_ρ, ls_resolve_blk_289] at h
    have heq : lsmpl.base 289 - (blkPl_316).base - BitVec.ofNat 64 k =
        (blkPl_289).base - ((blkPl_316).base + BitVec.ofNat 64 k) := by
      change (blkPl_289).base - (blkPl_316).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pe2_fetch_bl_reserve {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat}
    (h1 : ∀ (b : BitVec 64) (ext : String → Option (State → State)),
      (tripleRatchetProgAtExt b ext).fetch
        ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k) =
        some (.bl (2508 - BitVec.ofNat 64 k)))
    (hp2 : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_316 H).fetch ((blkPl_316).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_316).ρ doReserve7Name - (blkPl_316).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (doReserveTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, _, _, _, rfl⟩ | ⟨inst, H, rfl, rfl, _, _, _, rfl⟩
  · rw [show ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 2508#64 -
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + BitVec.ofNat 64 k)) =
      2508#64 - BitVec.ofNat 64 k by bv_omega]
    exact h1 b ext
  · letI := inst
    have h := @hp2 inst H
    simp only [doReserve7Name, blkPl_316_ρ, ls_resolve_blk_320] at h
    have heq : lsmpl.base 320 - (blkPl_316).base - BitVec.ofNat 64 k =
        (blkPl_320).base - ((blkPl_316).base + BitVec.ofNat 64 k) := by
      change (blkPl_320).base - (blkPl_316).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

open Lean Elab Tactic in
elab "pe2_fetches_prog " hfn:ident kStart:num kEnd:num : tactic => do
  let off := 0x4d2dc
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d2dc
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kHex := String.ofList (Nat.toDigits 16 k)
    let lsFetch := mkIdent (`CryptoVerification |>.str s!"blkPC_316_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 64 then
      evalTactic (← `(tactic|
        have := pe2_fetch_bl_encLen $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 72 || k == 124 then
      evalTactic (← `(tactic|
        have := pe2_fetch_bl_varint $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 140 then
      evalTactic (← `(tactic|
        have := pe2_fetch_bl_rep $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 168 then
      evalTactic (← `(tactic|
        have := pe2_fetch_b_rep $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 188 || k == 220 then
      evalTactic (← `(tactic|
        have := pe2_fetch_bl_reserve $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else
      evalTactic (← `(tactic|
        have := pe2_fetch_add $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))

private theorem step_reserve_20_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog
      doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 20#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA)
    (hx1 : s.readReg64 .x1 = v) (hx19 : s.readReg64 .x19 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 40#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pe2_fetches_prog hfn2 20 40
  pe2_fetches_prog hfn2 172 200
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs_placed (mid := doReserveTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve7_call_placed hres A hdoReserve v curCap curPtr sp
      (entry + 192#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = encA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 40#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 40#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_reserve_84_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog
      doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 84#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 100#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.idx.zeroExtend 64 → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pe2_fetches_prog hfn2 84 100
  pe2_fetches_prog hfn2 200 236
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · apply SepWPp.of_sepWP_cs_placed (mid := doReserveTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve7_call_placed hres A hdoReserve v curCap curPtr sp
      (entry + 224#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = encA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = pb.idx.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 100#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv1)
        (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega) (fun h => absurd h (by omega)))
  · have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := Bool.eq_false_iff.mpr hcap
    have hlt0 : curBs.length < curCap.toNat := lt_cap_toNat_of_beq_false hcap_le hcap_f
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 100#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_hdr_2 {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencLen : subroutine_ok prog
      encLenTarget (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok prog
      encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog
      doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat ∨
      bs0.length + (polyEncoderHeaderBytes pb).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = entry + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A encA g ptsElems polysElems ∗
          vecU8At A v cap1 ptr1 (bs0 ++ polyEncoderHeaderBytes pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg prog entry := isPolyEncoderEncodeEntryProg_of_pe2 hfn2
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  refine step_polyEncoder_prologue_placed hres hfn encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1
  refine step_reserve_20_2 hres128 A hfn2 hdoReserve encA v cap0 ptr0 sp bs0 (by omega)
    hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx19_1 hcs1
    (F := Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
  refine step_polyEncoder_push_hdr_tag_placed A hfn encA v cap01 ptr01 sp bs0 hlt01
    hpc2 hrun2 hsp2 htr2 hx1_2 hx19_2 hx20_2 hcs2
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  pe2_fetches_prog hfn2 64 68
  pe2_fetches_prog hfn2 72 76
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := encLenTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyEncLen_call_placed hres128 A hencLen encA sp (entry + 68#64) g pb hlen_lt
    (F := vecU8At A v cap01 ptr01 (bs0 ++ [0x12#8]) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyEncoder_mov_x1_x19_68_placed hfn
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) encA v sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ [0x12#8]).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ≤ cap01.toNat ∨
      (bs0 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]
    rcases hfit_hdr with h | h
    · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
    · right; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) v cap01 ptr01 sp (entry + 76#64)
    (bs0 ++ [0x12#8]) hfit_len
    (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      polyEncoderRestAt A encA g ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 hge1 hpres1
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyEncoderHeaderBytes bs0 pb]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 cap1 ptr1 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 (Nat.le_trans hge01 hge1) ?_)
  intro hle
  obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
  exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)

private theorem step_idx_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencVarint : subroutine_ok prog
      encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog
      doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (encA v curCap curPtr sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_idx : curBs.length + (Proto.encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 1#32 pb.idx).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 76#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.idx) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg prog entry := isPolyEncoderEncodeEntryProg_of_pe2 hfn2
  refine step_polyEncoder_check_idx_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    refine step_reserve_84_2 hres A hfn2 hdoReserve encA v curCap curPtr sp curBs pb (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F) (by ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
    refine step_polyEncoder_push_idx_tag_placed A hfn encA v cap01 ptr01 sp curBs pb hlt01
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    pe2_fetches_prog hfn2 124 128
    examples_hide_fetches
    apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_idx with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.idx.zeroExtend 64) v cap01 ptr01 sp (entry + 128#64) (curBs ++ [0x08#8]) hfit_v
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_idx_of_ne_zero curBs pb hidx]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_)
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · simp only [hidx, ↓reduceIte] at hpc1
    rw [← bs_append_idx_of_zero curBs pb hidx]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_pts_polys_2 {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencRep : subroutine_ok prog
      encRepTarget (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (encA v curCap curPtr sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 58)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys_lt : pb.polys.length < 2 ^ 58)
    (hfit_pts : curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat ∨
      curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length + 10 < 2 ^ 62)
    (hfit_polys : ∀ nextCap : BitVec 64,
      (curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat → nextCap = curCap) →
      (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length ≤ nextCap.toNat ∨
      (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length +
        (Varint.encodeRepeatedBytes 3 pb.polys).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        vecU8At A v nextCap nextPtr
          ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg prog entry := isPolyEncoderEncodeEntryProg_of_pe2 hfn2
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hpolys_len : polysElems.length = pb.polys.length := by rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_pts_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  pe2_fetches_prog hfn2 140 144
  pe2_fetches_prog hfn2 168 172
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := encRepTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated_call_placed A hencRep 2 g.pts.ptr v curCap curPtr sp
    (entry + 144#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact hfit_pts)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.polys.ptr polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq] at hpres2 ⊢
  refine step_polyEncoder_prep_polys_epilogue_placed hfn encA v sp sv3 g pb ptsElems polysElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v cap2 ptr2 (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hw0_3 hx1_3 hx2_3 hx3_3 hcc3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := encRepTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  have hfit_p3 := hfit_polys cap2 (fun h => (hpres2 h).1)
  exact step_msg48_encode_repeated_tailcall_placed
    (s := s3.setPC encRepTarget)
    hres A hencRep 3 g.polys.ptr v cap2 ptr2 sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems
    (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) (by decide) (by decide) (by omega)
    (by rw [hpolys_eq]; exact hfit_p3)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun3)
    ((State.sp_setPC _ _).trans hsp3)
    halign
    ((State.trace_setPC _ _).trans htr3)
    ((State.readReg64_setPC _ _ _).trans hlr3)
    (by dsimp only [State.readReg32] at hw0_3 ⊢; rw [State.readReg64_setPC]; exact hw0_3)
    ((State.readReg64_setPC _ _ _).trans hx1_3)
    (by rw [State.readReg64_setPC, hpolys_len]; exact hx2_3)
    ((State.readReg64_setPC _ _ _).trans hx3_3)
    (calleeSavedPreserved_setPC_placed _ hcc3)
    (msgEnc48CalleeSavedPlaced_setPC _ hcs3 hinv3)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl)
    (fun sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf hge3 hpres3 => by
      rw [hpolys_eq] at hpres3 ⊢
      have hq := hnext sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf (Nat.le_trans hge2 hge3) (by
        intro hle
        obtain ⟨rfl, rfl⟩ := hpres2 (by omega)
        exact hpres3 (by rw [List.length_append]; omega))
      have hEq :
          ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
            vecU8At A v nextCap nextPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
          ((repeatedBytesSliceAt g.polys.ptr polysElems ∗
            vecU8At A v nextCap nextPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
            (((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
              ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)) := by
        dsimp only [polyEncoderElemsAt]; ac_rfl
      rwa [← hEq])

theorem polyEncoder2_gen_ok_prog {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {A : RustAlloc}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPe2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {x : EncodePolyEncoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok prog encLenTarget
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok prog encVarintTarget
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok prog encRepTarget
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoR : subroutine_ok prog doReserveTarget
      (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (hpc : s0.pc = entry)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp prog (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyEncoderPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hpts58, hpolys58, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyEncoderMsg_len_split x.enc
  have hlen_le_msg := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by
    rcases hfit with h | h <;> omega
  have hfit_hdr : x.bs.length + (polyEncoderHeaderBytes x.enc).length ≤ x.cap.toNat ∨
      x.bs.length + (polyEncoderHeaderBytes x.enc).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_hdr_2 hres A hfn2 hencLen hencV hdoR x.encA x.v x.cap x.ptr s0.sp x.g x.enc x.bs
    hlen_lt hfit_hdr (F := emp) rfl hpc hrun rfl halign rfl hx0 hx1 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 cap1 ptr1 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1
  have hfit_idx : (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (Proto.encodeUint32Field 1#32 x.enc.idx).length ≤ cap1.toNat ∨
      (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (Proto.encodeUint32Field 1#32 x.enc.idx).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine step_idx_2 hres128 A hfn2 hencV hdoR x.encA x.v cap1 ptr1 s0.sp x.g x.enc
    ptsElems polysElems (x.bs ++ polyEncoderHeaderBytes x.enc) hfit_idx
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  let bs_idx := (x.bs ++ polyEncoderHeaderBytes x.enc) ++ Proto.encodeUint32Field 1#32 x.enc.idx
  have hfit_pts : bs_idx.length + (Varint.encodeRepeatedBytes 2 x.enc.pts).length ≤ cap2.toNat ∨
      bs_idx.length + (Varint.encodeRepeatedBytes 2 x.enc.pts).length + 10 < 2 ^ 62 := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [List.length_append]; omega)
      omega
    · right; omega
  have hfit_polys : ∀ nextCap : BitVec 64,
      (bs_idx.length + (Varint.encodeRepeatedBytes 2 x.enc.pts).length ≤ cap2.toNat → nextCap = cap2) →
      (bs_idx ++ Varint.encodeRepeatedBytes 2 x.enc.pts).length +
        (Varint.encodeRepeatedBytes 3 x.enc.polys).length ≤ nextCap.toNat ∨
      (bs_idx ++ Varint.encodeRepeatedBytes 2 x.enc.pts).length +
        (Varint.encodeRepeatedBytes 3 x.enc.polys).length + 10 < 2 ^ 62 := by
    intro nextCap hpres_pts
    dsimp [bs_idx]; rw [List.length_append, List.length_append, List.length_append]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [List.length_append]; omega)
      have hnc := hpres_pts (by dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega)
      subst hnc; omega
    · right; omega
  refine step_pts_polys_2 hres A hfn2 hencR x.encA x.v cap2 ptr2 s0.sp sv3 x.g x.enc
    ptsElems polysElems bs_idx hpts_eq hpts58 hpolys_eq hpolys58 hfit_pts hfit_polys
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗ emp) (by dsimp [bs_idx]; ac_rfl) ?_
  intro sf cap3 ptr3 hpcf hrunf hspf htrf hccf hcsf hge3 hpres3
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hge_all : x.cap.toNat ≤ cap3.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 hge3)
  have hpres_all : x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
      cap3 = x.cap ∧ ptr3 = x.ptr := by
    intro hle
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by rw [List.length_append]; omega)
    exact hpres3 (by dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega)
  have hm_pack : sf.mem ⊨ (polyEncoderElemsAt x.encA x.g x.enc ptsElems polysElems ∗
      polyEncoderRestAt A x.encA x.g ptsElems polysElems) ∗
      (vecU8At A x.v cap3 ptr3 (x.bs ++ encodePolyEncoderMsg x.enc) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyEncoderMsg x.bs x.enc]
    convert hm using 1; dsimp [bs_idx]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.encA x.enc _ sf.mem).mpr
    ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_pack⟩
  dsimp only [encodePolyEncoderPinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  rw [sepConj_left_comm (Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc)]
  simp only [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap3, ptr3, ?_⟩
  have hpure : (x.cap.toNat ≤ cap3.toNat ∧
      (x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat →
        cap3 = x.cap ∧ ptr3 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj]
  convert hm_pinned using 1; ac_rfl

theorem polyEncoder2_gen_ok_ext {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodePolyEncoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 82712#64)
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709531196#64)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64)
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 2508#64)
      (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderPinnedSpec A).onPanic x s0 sf ∗ R)) :=
  polyEncoder2_gen_ok_prog hres (Or.inl ⟨b, ext, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    hencLen hencV hencR hdoR hpc hrun hpre hsp_align

theorem encode_polyEncoder_2_pinned_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncodePolyEncoder2PinnedOkExt b A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 82712#64)
      (polynomialEncoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyEncoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyEncLenElemsOut_of_pinned (polynomialEncoderEncodedLen_local2_pinned_ok_ext b A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709531196#64)
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [encodePolyEncoder2_encodeVarint4_fnAddr_eq]; exact encode_varint4_fit_ok_ext hA
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64)
      (encodeRepeatedSpecOf doReserveStack A) := by
    rw [encodePolyEncoder2_encodeRepeated2_fnAddr_eq]; exact encode_repeated_2_ok_ext hA
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyEncoder2Name + 2508#64)
      (doReserveSpecOf doReserveStack A) := by
    rw [encodePolyEncoder2_doReserve7_fnAddr_eq]; exact do_reserve_7_ok_ext hA
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencV0)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencR0)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hdoR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncodePolyEncoder2OkExt b A ext :=
  polyEncoder_unpinned_of_pinned (encode_polyEncoder_2_pinned_ok_ext hA)

theorem encode_polyEncoder_2_pinned_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncodePolyEncoder2PinnedOkX img A ext := by
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name + 82712#64)
      (polynomialEncoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyEncoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyEncLenElemsOut_of_pinned (polynomialEncoderEncodedLen_local2_pinned_ok_ext img.base A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name + 18446744073709531196#64)
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyEncoder2_encodeVarint4_fnAddr_eq]
    exact encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name + 18446744073709529452#64)
      ((encodeRepeatedSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyEncoder2_encodeRepeated2_fnAddr_eq]
    exact encode_repeated_2_ok_ext_x hA
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyEncoder2Name + 2508#64)
      ((doReserveSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyEncoder2_doReserve7_fnAddr_eq]; exact hdoReserve
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencL0)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hencV0)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hencR0)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hdoR0)
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncodePolyEncoder2OkX img A ext :=
  polyEncoder_unpinned_of_pinned_x (encode_polyEncoder_2_pinned_ok_ext_x hA)

theorem encode_polyEncoder_2_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsPe2EntryProg (lsProg_316 H) (blkPl_316).base
      (blkPl_401).base (blkPl_292).base (blkPl_289).base (blkPl_320).base :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_repeated_2_placed_ok h_panic hshim halloc hrealloc hmc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderSpec A)) :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_polyEncoder_2_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderPinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsPe2EntryProg (lsProg_316 H) (blkPl_316).base
      (blkPl_401).base (blkPl_292).base (blkPl_289).base (blkPl_320).base :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := polyEncoder2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local2_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_repeated_2_placed_ok_x h_panic hshim halloc hrealloc hmc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_2_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_316 H) (blkPl_316).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderSpecX A)) :=
  polyEncoder_unpinned_of_pinned_placed_x
    (encode_polyEncoder_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end CryptoVerification.SpqrV1.Prost.MessageEncode
