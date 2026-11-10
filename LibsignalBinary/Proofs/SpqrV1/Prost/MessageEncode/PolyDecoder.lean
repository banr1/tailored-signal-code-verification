/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ProtoReprCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<PolynomialDecoder, Vec<u8>> [local#2]` (`0x52544`)

Separation Logic `subroutine_ok` proofs for:
- `prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]`
  at `0x52544` (`100` insns, `400` bytes)

Also re-exports `[local#1]` (`0x37520`) from `PolyDecoder1.lean`.
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
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local arm64_norm]
private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega

def IsPd2EntryProg (prog : Program)
    (entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧
    entry = (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name ∧
    encLenTarget = entry + 94640#64 ∧
    encVarintTarget = entry + 18446744073709531596#64 ∧
    encRepTarget = entry + 18446744073709529852#64 ∧
    doReserveTarget = entry + 2908#64) ∨
  (∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_315 H ∧ entry = (blkPl_315).base ∧
    encLenTarget = (blkPl_413).base ∧
    encVarintTarget = (blkPl_292).base ∧
    encRepTarget = (blkPl_289).base ∧
    doReserveTarget = (blkPl_320).base)

theorem IsPd2EntryProg.toEntry {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget) :
    IsPolyDecoderEncodeEntryProg prog entry := by
  rcases hfn2 with ⟨b, ext, rfl, rfl, _, _, _, _⟩ | ⟨_, H, rfl, rfl, _, _, _, _⟩
  · exact Or.inl ⟨b, ext, rfl, Or.inr rfl⟩
  · exact Or.inr ⟨‹_›, H, Or.inr ⟨rfl, rfl⟩⟩

private theorem pd2_fetch_add {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {ins : Instr}
    (h_ext : ∀ b abs, (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some ins)
    (h_365 : ∀ [LibsignalPlacement] H,
      (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, abs, rfl, rfl, _, _, _, _⟩ | ⟨_, H, rfl, rfl, _, _, _, _⟩; exact h_ext b abs; exact h_365 H

private theorem pd2_fetch_bl_encLen {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {off : BitVec 64}
    (h_ext : ∀ b abs, (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some (.bl off))
    (hoff : BitVec.ofNat 64 k + off = 94640#64)
    (h_365 : ∀ [LibsignalPlacement] H, (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_315).ρ polynomialDecoderEncodedLenLocal2Name - (blkPl_315).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (.bl (encLenTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, abs, rfl, rfl, rfl, _, _, _⟩ | ⟨_, H, rfl, rfl, rfl, _, _, _⟩
  · have h := h_ext b abs
    have heq : off = (tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + 94640#64 -
        ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) := by rw [← hoff]; bv_omega
    rwa [heq] at h
  · have h := h_365 H; simp only [polynomialDecoderEncodedLenLocal2Name, blkPl_315_ρ, ls_resolve_blk_413] at h
    have heq : lsmpl.base 413 - (blkPl_315).base - BitVec.ofNat 64 k =
        (blkPl_413).base - ((blkPl_315).base + BitVec.ofNat 64 k) := by
      change (blkPl_413).base - (blkPl_315).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pd2_fetch_bl_encVarint {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {off : BitVec 64}
    (h_ext : ∀ b abs, (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some (.bl off))
    (hoff : BitVec.ofNat 64 k + off = 18446744073709531596#64)
    (h_365 : ∀ [LibsignalPlacement] H, (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_315).ρ encodeVarint4Name - (blkPl_315).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (.bl (encVarintTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, abs, rfl, rfl, _, rfl, _, _⟩ | ⟨_, H, rfl, rfl, _, rfl, _, _⟩
  · have h := h_ext b abs
    have heq : off = (tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + 18446744073709531596#64 -
        ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) := by rw [← hoff]; bv_omega
    rwa [heq] at h
  · have h := h_365 H; simp only [encodeVarint4Name, blkPl_315_ρ, ls_resolve_blk_292] at h
    have heq : lsmpl.base 292 - (blkPl_315).base - BitVec.ofNat 64 k =
        (blkPl_292).base - ((blkPl_315).base + BitVec.ofNat 64 k) := by
      change (blkPl_292).base - (blkPl_315).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pd2_fetch_bl_encRep {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {off : BitVec 64}
    (h_ext : ∀ b abs, (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some (.bl off))
    (hoff : BitVec.ofNat 64 k + off = 18446744073709529852#64)
    (h_365 : ∀ [LibsignalPlacement] H, (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_315).ρ encodeRepeated2Name - (blkPl_315).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (.bl (encRepTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, abs, rfl, rfl, _, _, rfl, _⟩ | ⟨_, H, rfl, rfl, _, _, rfl, _⟩
  · have h := h_ext b abs
    have heq : off = (tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + 18446744073709529852#64 -
        ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) := by rw [← hoff]; bv_omega
    rwa [heq] at h
  · have h := h_365 H; simp only [encodeRepeated2Name, blkPl_315_ρ, ls_resolve_blk_289] at h
    have heq : lsmpl.base 289 - (blkPl_315).base - BitVec.ofNat 64 k =
        (blkPl_289).base - ((blkPl_315).base + BitVec.ofNat 64 k) := by
      change (blkPl_289).base - (blkPl_315).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

private theorem pd2_fetch_bl_doReserve {prog : Program}
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {k : Nat} {off : BitVec 64}
    (h_ext : ∀ b abs, (tripleRatchetProgAtExt b abs).fetch
      ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) = some (.bl off))
    (hoff : BitVec.ofNat 64 k + off = 2908#64)
    (h_365 : ∀ [LibsignalPlacement] H, (lsProg_315 H).fetch ((blkPl_315).base + BitVec.ofNat 64 k) =
        some (.bl ((blkPl_315).ρ doReserve7Name - (blkPl_315).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (.bl (doReserveTarget - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, abs, rfl, rfl, _, _, _, rfl⟩ | ⟨_, H, rfl, rfl, _, _, _, rfl⟩
  · have h := h_ext b abs
    have heq : off = (tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + 2908#64 -
        ((tripleRatchetProgAtExt b abs).fnAddr encodePolyDecoder2Name + BitVec.ofNat 64 k) := by rw [← hoff]; bv_omega
    rwa [heq] at h
  · have h := h_365 H; simp only [doReserve7Name, blkPl_315_ρ, ls_resolve_blk_320] at h
    have heq : lsmpl.base 320 - (blkPl_315).base - BitVec.ofNat 64 k =
        (blkPl_320).base - ((blkPl_315).base + BitVec.ofNat 64 k) := by
      change (blkPl_320).base - (blkPl_315).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

open Lean Elab Tactic in
elab "pd2_fetches " hfn:ident kStart:num kEnd:num : tactic => do
  let off := 0x4d14c
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d14c
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kHex := String.ofList (Nat.toDigits 16 k)
    let p := mkIdent (`CryptoVerification |>.str s!"blkPC_315_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 44 then
      evalTactic (← `(tactic|
        have := pd2_fetch_bl_encLen $hfn (k := $kq)
          (fun b abs => $fetchAdd (b := b) (H := Rust.withPanics abs) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $p (blkPl_315).base H)))
    else if k == 36 || k == 52 || k == 104 || k == 156 then
      evalTactic (← `(tactic|
        have := pd2_fetch_bl_encVarint $hfn (k := $kq)
          (fun b abs => $fetchAdd (b := b) (H := Rust.withPanics abs) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $p (blkPl_315).base H)))
    else if k == 172 then
      evalTactic (← `(tactic|
        have := pd2_fetch_bl_encRep $hfn (k := $kq)
          (fun b abs => $fetchAdd (b := b) (H := Rust.withPanics abs) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $p (blkPl_315).base H)))
    else if k == 284 || k == 320 || k == 352 || k == 388 then
      evalTactic (← `(tactic|
        have := pd2_fetch_bl_doReserve $hfn (k := $kq)
          (fun b abs => $fetchAdd (b := b) (H := Rust.withPanics abs) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $p (blkPl_315).base H)))
    else
      evalTactic (← `(tactic|
        have := pd2_fetch_add $hfn (k := $kq)
          (fun b abs => $fetchAdd (b := b) (H := Rust.withPanics abs) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $p (blkPl_315).base H)))

private theorem step_reserve_64_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 64#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 80#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.ptsNeeded.zeroExtend 64 → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd2_fetches hfn2 64 80; pd2_fetches hfn2 264 300
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
      (entry + 288#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = pb.ptsNeeded.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 80#64); wp_steps
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
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 80#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_reserve_116_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialDecoder)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 116#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = pb.polys.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 132#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = pb.polys.zeroExtend 64 → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd2_fetches hfn2 116 132; pd2_fetches hfn2 300 336
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
      (entry + 324#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = pb.polys.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 132#64); wp_steps
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
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 132#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_reserve_188_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 204#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x8 = nextCap →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd2_fetches hfn2 188 204; pd2_fetches hfn2 336 368
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
      (entry + 356#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 204#64); wp_steps
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
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 204#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (by simp only [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) hinv0)
        hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_reserve_228_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 .x8 = curCap) (hx9 : s.readReg64 .x9 = curPtr)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hz : s.pstate = subsPState64 curCap (BitVec.ofNat 64 curBs.length)) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 232#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x9 = nextPtr → sm.readReg64 .x10 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr curBs ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  pd2_fetches hfn2 228 232; pd2_fetches hfn2 368 400
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F) (by ac_rfl) fun hcap_le _ _ => ?_
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq : curCap.toNat = curBs.length :=
      cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hcap_bv : curCap = BitVec.ofNat 64 curBs.length := eq_of_beq hcap
    apply SepWPp.of_sepWP_cs_placed (mid := doReserveTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    refine step_msg48rep_do_reserve7_call_placed hres A hdoReserve v curCap curPtr sp
      (entry + 392#64) curBs 1 hbound1 (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv0)
      (by ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = decA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v newCap1 newPtr1 curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 232#64); wp_steps
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
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 232#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
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
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencLen : subroutine_ok prog encLenTarget (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok prog encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (decA v cap0 ptr0 sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialDecoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat ∨
      bs0.length + (polyDecoderHeaderBytes tag pb).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = decA) (hx2 : s.readReg64 .x2 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      sm.pc = entry + 56#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (polyDecoderHeaderBytes tag pb).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp prog ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          polyDecoderRestAt A decA g ptsElems ∗
          vecU8At A v cap1 ptr1 (bs0 ++ polyDecoderHeaderBytes tag pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyDecoderEncodeEntryProg prog entry := hfn2.toEntry
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge_key, hge2⟩ := polyDecoderHeaderBytes_len_bounds tag pb
  refine step_polyDecoder_prologue_placed hres hfn tag decA v sp hhs0 hpc hrun hsp halign htr
    hw0 hx1 hx2 hcs
    (F := Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hcs1
  pd2_fetches hfn2 36 40; pd2_fetches hfn2 44 48; pd2_fetches hfn2 52 56
  examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hfit_key : bs0.length +
      (LibsignalProtoCodec.encodeVarint (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat ∨
      bs0.length + 10 < 2 ^ 62 := by
    rw [encodeVarint_polyDecoder_tag_eq_proto]
    rcases hfit_hdr with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) v cap0 ptr0 sp (entry + 40#64)
    bs0 hfit_key
    (F := Poly.protoPolynomialDecoderPinnedAt A g decA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01
  rw [encodeVarint_polyDecoder_tag_eq_proto] at hpres01 ⊢
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x0_x20_40_placed hfn decA v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := encLenTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyDecLen_call_placed hres128 A hencLen decA sp (entry + 48#64) g pb hlen_lt
    (F := vecU8At A v cap01 ptr01 (bs0 ++ Proto.encodeKey tag .lengthDelimited) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems hpts_eq hpts_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyDecoder_mov_x1_x19_48_placed hfn decA v
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb))).length ≤ cap01.toNat ∨
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit_hdr with h | h
    · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
    · right; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen pb)) v cap01 ptr01 sp (entry + 56#64)
    (bs0 ++ Proto.encodeKey tag .lengthDelimited) hfit_len
    (F := polyDecoderElemsAt decA g pb ptsElems ∗
      polyDecoderRestAt A decA g ptsElems ∗
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
  have hx20_6 : s6.readReg64 .x20 = decA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyDecoderHeaderBytes bs0 tag pb]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 (Nat.le_trans hge01 hge1) ?_)
  intro hle
  obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
  exact hpres1 (by rw [List.length_append]; omega)

private theorem step_ptsNeeded_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencVarint : subroutine_ok prog encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pn : curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 56#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 108#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 1#32 pb.ptsNeeded).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.ptsNeeded) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyDecoderEncodeEntryProg prog entry := hfn2.toEntry
  refine step_polyDecoder_check_ptsNeeded_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpn : (pb.ptsNeeded == 0#32)
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pn, hge2_pn⟩ := ptsNeeded_field_len_of_ne_zero pb hpn
    refine step_reserve_64_2 hres A hfn2 hdoReserve decA v curCap curPtr sp curBs pb (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F) (by ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
    refine step_polyDecoder_push_ptsNeeded_tag_placed A hfn decA v cap01 ptr01 sp curBs pb hlt01
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    pd2_fetches hfn2 104 108; examples_hide_fetches
    apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_pn with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.ptsNeeded.zeroExtend 64) v cap01 ptr01 sp (entry + 108#64) (curBs ++ [0x08#8]) hfit_v
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_ptsNeeded_of_ne_zero curBs pb hpn]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_)
    intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · simp only [hpn, ↓reduceIte] at hpc1
    rw [← bs_append_ptsNeeded_of_zero curBs pb hpn]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_polys_2 {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencVarint : subroutine_ok prog encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_pl : curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat ∨
      curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 108#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = entry + 160#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = decA → MsgEnc48CalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Proto.encodeUint32Field 2#32 pb.polys).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((polyDecoderElemsAt decA g pb ptsElems ∗
          vecU8At A v nextCap nextPtr (curBs ++ Proto.encodeUint32Field 2#32 pb.polys) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyDecoderEncodeEntryProg prog entry := hfn2.toEntry
  refine step_polyDecoder_check_polys_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hpl : (pb.polys == 0#32)
  · simp only [hpl, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_pl, hge2_pl⟩ := polys_field_len_of_ne_zero pb hpl
    refine step_reserve_116_2 hres A hfn2 hdoReserve decA v curCap curPtr sp curBs pb (by omega)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F) (by ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01
    refine step_polyDecoder_push_polys_tag_placed A hfn decA v cap01 ptr01 sp curBs pb hlt01
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    pd2_fetches hfn2 156 160; examples_hide_fetches
    apply SepWPp.of_sepWP_cs_placed (mid := encVarintTarget); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x10#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.polys.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x10#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_pl with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.polys.zeroExtend 64) v cap01 ptr01 sp (entry + 160#64) (curBs ++ [0x10#8]) hfit_v
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = decA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_polys_of_ne_zero curBs pb hpl]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_)
    intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
    exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)
  · simp only [hpl, ↓reduceIte] at hpc1
    rw [← bs_append_polys_of_zero curBs pb hpl]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 curCap curPtr hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_pts_isComplete_2 {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} (A : RustAlloc)
    {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {s0 s : State}
    (hencRep : subroutine_ok prog encRepTarget (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (decA v curCap curPtr sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialDecoderGhost)
    (pb : ProtoPolynomialDecoder)
    (ptsElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 58)
    (hfit_pts : curBs.length + (Varint.encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat ∨
      curBs.length + (Varint.encodeRepeatedBytes 3 pb.pts).length + 10 < 2 ^ 62)
    (hfit_ic : ∀ nextCap : BitVec 64,
      (curBs.length + (Varint.encodeRepeatedBytes 3 pb.pts).length ≤ curCap.toNat → nextCap = curCap) →
      (curBs ++ Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length ≤ nextCap.toNat ∨
      (curBs ++ Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length + 10 < 2 ^ 62)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = decA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyDecoderElemsAt decA g pb ptsElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (Varint.encodeRepeatedBytes 3 pb.pts).length +
        (Proto.encodeBoolField 4#32 pb.isComplete).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      Q sf ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At A v nextCap nextPtr
          ((curBs ++ Varint.encodeRepeatedBytes 3 pb.pts) ++ Proto.encodeBoolField 4#32 pb.isComplete) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyDecoderEncodeEntryProg prog entry := hfn2.toEntry
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  refine step_polyDecoder_prep_pts_placed hfn decA v sp g pb ptsElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  pd2_fetches hfn2 172 176; examples_hide_fetches
  apply SepWPp.of_sepWP_cs_placed (mid := encRepTarget); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated_call_placed A hencRep 3 g.pts.ptr v curCap curPtr sp
    (entry + 176#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact hfit_pts)
    (F := ((decA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((decA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((decA + 24#64) ↦₃₂ pb.ptsNeeded) ∗ ((decA + 28#64) ↦₃₂ pb.polys) ∗
      ((decA + 32#64) ↦₈ boolByte pb.isComplete) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by rw [hpts_len]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyDecoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = decA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq] at hpres2 ⊢
  let bs_pts := curBs ++ Varint.encodeRepeatedBytes 3 pb.pts
  refine step_polyDecoder_check_isComplete_placed hres hfn decA v sp sv3 g pb ptsElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v cap2 ptr2 bs_pts ∗ A.pool ∗ F)
    (by dsimp only [polyDecoderElemsAt, bs_pts]; ac_rfl) ?_ ?_
  · intro hc sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf cap2 ptr2 hpcf hrunf hspf htrf hccf hcsf hge2 (fun hle => by
      rw [hc, protoEncodeBoolField_4_false, List.length_nil] at hle; exact hpres2 (by omega))
    rw [hc, bs_append_boolField_4_false bs_pts] at hq
    have hEq : ((polyDecoderElemsAt decA g pb ptsElems ∗ vecU8At A v cap2 ptr2 bs_pts ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((polyDecoderElemsAt decA g pb ptsElems ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (vecU8At A v cap2 ptr2 bs_pts ∗ A.pool ∗ F)) := by ac_rfl
    rwa [← hEq]
  · intro hc s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3
    have hfit_ic2 := hfit_ic cap2 (fun h => (hpres2 h).1)
    have hlen_ic : (Proto.encodeBoolField 4#32 pb.isComplete).length = 2 := by
      rw [hc, protoEncodeBoolField_4_true]; rfl
    have hbs_pts_len : bs_pts.length = (curBs ++ Varint.encodeRepeatedBytes 3 pb.pts).length := rfl
    refine step_reserve_188_2 hres128 A hfn2 hdoReserve decA v cap2 ptr2 sp bs_pts
      (by rcases hfit_ic2 with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ msgEnc48SavedFrame sp (s0.readReg64 .fp)
        (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F) (by ac_rfl) ?_
    intro s4 cap3 ptr3 hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4 hlt3 hge3 hpres3
    refine step_polyDecoder_push_isComplete_tag_placed A hfn decA v cap3 ptr3 sp bs_pts hlt3
      hpc4 hrun4 hsp4 htr4 hx1_4 hx8_4 hx19_4 hx20_4 hcs4
      (F := A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyDecoderElemsAt decA g pb ptsElems ∗ msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F) (by ac_rfl) ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
    have hfit_val : (bs_pts ++ [0x20#8]).length + 1 ≤ cap3.toNat ∨ (bs_pts ++ [0x20#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_ic2 with h | h
      · left; obtain ⟨rfl, _⟩ := hpres3 (by omega); omega
      · right; omega
    refine step_reserve_228_2 hres128 A hfn2 hdoReserve decA v cap3 ptr3 sp (bs_pts ++ [0x20#8]) hfit_val
      hpc5 hrun5 hsp5 halign htr5 hx8_5 hx9_5 hx10_5 hx19_5 hx20_5 hz5 hcs5
      (F := polyDecoderElemsAt decA g pb ptsElems ∗ msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F) (by ac_rfl) ?_
    intro s6 cap4 ptr4 hpc6 hrun6 hsp6 htr6 hx9_6 hx10_6 hx19_6 _ hcs6 hlt4 hge4 hpres4
    refine step_polyDecoder_push_isComplete_val_epilogue_placed hres A hfn v cap4 ptr4 sp sv3
      (bs_pts ++ [0x20#8]) hlt4 hpc6 hrun6 hsp6 halign htr6 hx9_6 hx10_6 hx19_6 hcs6
      (F := A.pool ∗ polyDecoderElemsAt decA g pb ptsElems ∗ F) (by ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hcsf
    have hq := hnext sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf
      (Nat.le_trans hge2 (Nat.le_trans hge3 hge4)) (fun hle => by
        obtain ⟨rfl, rfl⟩ := hpres2 (by omega)
        obtain ⟨rfl, rfl⟩ := hpres3 (by dsimp [bs_pts]; rw [List.length_append]; omega)
        exact hpres4 (by dsimp [bs_pts]; rw [List.length_append, List.length_append, List.length_singleton]; omega))
    rw [hc, ← bs_append_boolField_4_true bs_pts] at hq
    have hEq : ((polyDecoderElemsAt decA g pb ptsElems ∗
        vecU8At A v cap4 ptr4 ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
        ((vecU8At A v cap4 ptr4 ((bs_pts ++ [0x20#8]) ++ [0x01#8]) ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
          (A.pool ∗ polyDecoderElemsAt decA g pb ptsElems ∗ F)) := by ac_rfl
    rwa [← hEq]

theorem polyDecoder2_gen_ok_prog {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {prog : Program} {A : RustAlloc} {entry encLenTarget encVarintTarget encRepTarget doReserveTarget : BitVec 64}
    (hfn2 : IsPd2EntryProg prog entry encLenTarget encVarintTarget encRepTarget doReserveTarget)
    {x : EncodePolyDecoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok prog encLenTarget (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok prog encVarintTarget (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok prog encRepTarget (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoR : subroutine_ok prog doReserveTarget (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).pre x s0 ∗ R) (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp prog (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyDecoderPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hpts58, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyDecoderMsg_len_split x.tag x.dec
  have hlen_le_msg := polynomialDecoderPBEncodedLen_le_msg_len x.tag x.dec
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialDecoderPBEncodedLen x.dec < 2 ^ 64 := by rcases hfit with h | h <;> omega
  have hfit_hdr : x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length ≤ x.cap.toNat ∨
      x.bs.length + (polyDecoderHeaderBytes x.tag x.dec).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_hdr_2 hres A hfn2 hencLen hencV x.tag x.decA x.v x.cap x.ptr s0.sp x.g x.dec x.bs
    hlen_lt hfit_hdr (F := emp) rfl hpc hrun rfl halign rfl hw0 hx1 hx2 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 cap1 ptr1 ptsElems hpts_eq hpts_lt hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1
  let bs_hdr := x.bs ++ polyDecoderHeaderBytes x.tag x.dec
  have hfit_pn : bs_hdr.length + (Proto.encodeUint32Field 1#32 x.dec.ptsNeeded).length ≤ cap1.toNat ∨
      bs_hdr.length + (Proto.encodeUint32Field 1#32 x.dec.ptsNeeded).length + 10 < 2 ^ 62 := by
    dsimp [bs_hdr]; rw [List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine step_ptsNeeded_2 hres128 A hfn2 hencV hdoR x.decA x.v cap1 ptr1 s0.sp x.g x.dec
    ptsElems bs_hdr hfit_pn hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
      (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by dsimp [bs_hdr]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  let bs_pn := bs_hdr ++ Proto.encodeUint32Field 1#32 x.dec.ptsNeeded
  have hfit_pl : bs_pn.length + (Proto.encodeUint32Field 2#32 x.dec.polys).length ≤ cap2.toNat ∨
      bs_pn.length + (Proto.encodeUint32Field 2#32 x.dec.polys).length + 10 < 2 ^ 62 := by
    dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega); omega
    · right; omega
  refine step_polys_2 hres128 A hfn2 hencV hdoR x.decA x.v cap2 ptr2 s0.sp x.g x.dec
    ptsElems bs_pn hfit_pl hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ msgEnc48SavedFrame s0.sp (s0.readReg64 .fp)
      (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp) rfl ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3
  let bs_pl := bs_pn ++ Proto.encodeUint32Field 2#32 x.dec.polys
  have hfit_pts : bs_pl.length + (Varint.encodeRepeatedBytes 3 x.dec.pts).length ≤ cap3.toNat ∨
      bs_pl.length + (Varint.encodeRepeatedBytes 3 x.dec.pts).length + 10 < 2 ^ 62 := by
    dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega); omega
    · right; omega
  have hfit_ic : ∀ nextCap : BitVec 64,
      (bs_pl.length + (Varint.encodeRepeatedBytes 3 x.dec.pts).length ≤ cap3.toNat → nextCap = cap3) →
      (bs_pl ++ Varint.encodeRepeatedBytes 3 x.dec.pts).length +
        (Proto.encodeBoolField 4#32 x.dec.isComplete).length ≤ nextCap.toNat ∨
      (bs_pl ++ Varint.encodeRepeatedBytes 3 x.dec.pts).length +
        (Proto.encodeBoolField 4#32 x.dec.isComplete).length + 10 < 2 ^ 62 := by
    intro nextCap hpres_pts; dsimp [bs_pl, bs_pn, bs_hdr]
    rw [List.length_append, List.length_append, List.length_append, List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
      obtain ⟨rfl, _⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega)
      have hnc := hpres_pts (by dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]; omega)
      subst hnc; omega
    · right; omega
  refine step_pts_isComplete_2 hres A hfn2 hencR hdoR x.decA x.v cap3 ptr3 s0.sp sv3 x.g x.dec
    ptsElems bs_pl hpts_eq hpts58 hfit_pts hfit_ic hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := polyDecoderRestAt A x.decA x.g ptsElems ∗ emp) (by dsimp [bs_pl]; ac_rfl) ?_
  intro sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf hge4 hpres4
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hge_all : x.cap.toNat ≤ cap4.toNat := Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all : x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat →
      cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hle; obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by dsimp [bs_hdr]; rw [List.length_append]; omega)
    obtain ⟨rfl, rfl⟩ := hpres3 (by dsimp [bs_pn, bs_hdr]; rw [List.length_append, List.length_append]; omega)
    exact hpres4 (by dsimp [bs_pl, bs_pn, bs_hdr]; rw [List.length_append, List.length_append, List.length_append]; omega)
  have hm_pack : sf.mem ⊨ (polyDecoderElemsAt x.decA x.g x.dec ptsElems ∗
      polyDecoderRestAt A x.decA x.g ptsElems) ∗
      (vecU8At A x.v cap4 ptr4 (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyDecoderMsg x.bs x.tag x.dec]
    convert hm using 1; dsimp [bs_pl, bs_pn, bs_hdr]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialDecoderPinnedAt_iff A x.g x.decA x.dec _ sf.mem).mpr
    ⟨ptsElems, hpts_eq, hpts_lt, hm_pack⟩
  dsimp only [encodePolyDecoderPinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  rw [sepConj_left_comm (Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec)]
  simp only [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap4, ptr4, ?_⟩
  have hpure : (x.cap.toNat ≤ cap4.toNat ∧
      (x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat → cap4 = x.cap ∧ ptr4 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj]; convert hm_pinned using 1; ac_rfl

theorem polyDecoder2_gen_ok_ext {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodePolyDecoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 94640#64)
      (withMsgEnc48CSPlaced s0 (polynomialDecoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709531596#64)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709529852#64)
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A)))
    (hdoR : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 2908#64)
      (withMsgEnc48CSPlaced s0 (doReserveSpecOf resStack A)))
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).pre x s0 ∗ R) (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyDecoderPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyDecoderPinnedSpec A).onPanic x s0 sf ∗ R)) :=
  polyDecoder2_gen_ok_prog hres (Or.inl ⟨b, ext, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    hencLen hencV hencR hdoR hpc hrun hpre hsp_align

theorem encode_polyDecoder_2_pinned_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncodePolyDecoder2PinnedOkExt b A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 94640#64) (polynomialDecoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyDecoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyDecLenElemsOut_of_pinned (polynomialDecoderEncodedLen_local2_pinned_ok_ext b A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709531596#64) (encodeVarintFitSpecOf doReserveStack A) := by
    rw [encodePolyDecoder2_encodeVarint4_fnAddr_eq]; exact encode_varint4_fit_ok_ext hA
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 18446744073709529852#64) (encodeRepeatedSpecOf doReserveStack A) := by
    rw [encodePolyDecoder2_encodeRepeated2_fnAddr_eq]; exact encode_repeated_2_ok_ext hA
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodePolyDecoder2Name + 2908#64) (doReserveSpecOf doReserveStack A) := by
    rw [encodePolyDecoder2_doReserve7_fnAddr_eq]; exact do_reserve_7_ok_ext hA
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencL0) (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencV0)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencR0) (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hdoR0) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_2_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) : EncodePolyDecoder2OkExt b A ext :=
  polyDecoder_unpinned_of_pinned (encode_polyDecoder_2_pinned_ok_ext hA)

theorem encode_polyDecoder_2_pinned_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncodePolyDecoder2PinnedOkX img A ext := by
  have hdoReserve := do_reserve_7_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have hencL0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name + 94640#64) (polynomialDecoderEncodedLenElemsOutSpec A) := by
    rw [encodePolyDecoder2_encodedLen2_fnAddr_eq]
    exact subroutine_ok_polyDecLenElemsOut_of_pinned (polynomialDecoderEncodedLen_local2_pinned_ok_ext img.base A ext)
  have hencV0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name + 18446744073709531596#64) ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyDecoder2_encodeVarint4_fnAddr_eq]; exact encodeVarint4_fit_ok_ext_x img A ext hdoReserve
  have hencR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name + 18446744073709529852#64) ((encodeRepeatedSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyDecoder2_encodeRepeated2_fnAddr_eq]; exact encode_repeated_2_ok_ext_x hA
  have hdoR0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodePolyDecoder2Name + 2908#64) ((doReserveSpecOf doReserveStackX A).inImage img) := by
    rw [encodePolyDecoder2_doReserve7_fnAddr_eq]; exact hdoReserve
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_gen_ok_ext (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_ext s0 hencL0) (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hencV0)
    (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hencR0) (subroutine_ok_withMsgEnc48CSPlaced_x img s0 hinv0 hdoR0) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_2_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) : EncodePolyDecoder2OkX img A ext :=
  polyDecoder_unpinned_of_pinned_x (encode_polyDecoder_2_pinned_ok_ext_x hA)

theorem encode_polyDecoder_2_pinned_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsPd2EntryProg (lsProg_315 H) (blkPl_315).base (blkPl_413).base (blkPl_292).base (blkPl_289).base (blkPl_320).base :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded_dec (subroutine_ok_polyDecLenElemsOut_of_pinned (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_repeated_2_placed_ok h_panic hshim halloc hrealloc hmc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok h_panic hshim halloc hrealloc)) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_2_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base (withLsCodeLoaded lsmpl (encodePolyDecoderSpec A)) :=
  polyDecoder_unpinned_of_pinned_placed_x (encode_polyDecoder_2_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_polyDecoder_2_pinned_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base (withLsCodeLoaded lsmpl (encodePolyDecoderPinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn2 : IsPd2EntryProg (lsProg_315 H) (blkPl_315).base (blkPl_413).base (blkPl_292).base (blkPl_289).base (blkPl_320).base :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := polyDecoder2_gen_ok_prog (by decide) hfn2
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded_dec (subroutine_ok_polyDecLenElemsOut_of_pinned (polynomialDecoderEncodedLen_local2_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (encode_repeated_2_placed_ok_x h_panic hshim halloc hrealloc hmc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0 (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc)) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyDecoder_2_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A)) (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_315 H) (blkPl_315).base (withLsCodeLoaded lsmpl (encodePolyDecoderSpecX A)) :=
  polyDecoder_unpinned_of_pinned_placed_x (encode_polyDecoder_2_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end CryptoVerification.SpqrV1.Prost.MessageEncode
