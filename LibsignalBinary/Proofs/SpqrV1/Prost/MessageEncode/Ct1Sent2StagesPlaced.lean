/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Stages 1–5 of `unchunked::Ct1Sent::encode [local#2]` (`Block 319`)

Proves relocatable `[LibsignalPlacement]` stage steppers on `lsProg_319` for Stages 1–5
(outer header, `epoch`, `auth`, `hdr`, and `es`) of `unchunked::Ct1Sent::encode [local#2]`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 hwVarintLen_eq_ofNat_varintLen_norm
   hwVarintLen_bvShift_eq_ofNat_varintLen_norm ule_self_64 ult_self_64
   ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.literalFetch false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega
private theorem bv_bl_off_eq (a d k : BitVec 64) : d - k = a + d - (a + k) := by bv_omega

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSavedPlaced.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

def IsCt1Enc2EntryProg (prog : Program) (entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧ entry = (tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name ∧
    encLen_pc = entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#2]") ∧
    varint_pc = entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]") ∧
    auth_pc = entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]") ∧
    reserve_pc = entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") ∧
    memcpy_pc = entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "memcpy")) ∨
  (∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_319 H ∧ entry = (blkPl_319).base ∧ encLen_pc = (blkPl_408).base ∧ varint_pc = (blkPl_292).base ∧
    auth_pc = lsmpl.base 314 ∧ reserve_pc = (blkPl_320).base ∧ memcpy_pc = lsρ lsMemcpySym)

theorem ct1_enc2_fetch_entry_placed {prog : Program} {entry p1 p2 p3 p4 p5 : BitVec 64} {instr : Instr}
    (hfn : IsCt1Enc2EntryProg prog entry p1 p2 p3 p4 p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name) = some instr)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + 0#64) = some instr) :
    prog.fetch entry = some instr := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, -, -, -⟩ | ⟨inst, H, rfl, rfl, -, -, -, -, -⟩; exact hext b ext
  letI := inst; have h := @hpl inst H; rwa [BitVec.add_zero] at h

theorem ct1_enc2_fetch_add_placed {prog : Program} {entry p1 p2 p3 p4 p5 : BitVec 64} {k : Nat} {instr : Instr}
    (hfn : IsCt1Enc2EntryProg prog entry p1 p2 p3 p4 p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some instr)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) = some instr) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some instr := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, -, -, -⟩ | ⟨_, H, rfl, rfl, -, -, -, -, -⟩; exact hext b ext; exact hpl H

theorem ct1_enc2_fetch_bl_encLen_placed {prog : Program} {entry encLen_pc p2 p3 p4 p5 : BitVec 64} {k : Nat} {off : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc p2 p3 p4 p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#2]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) =
      some (Instr.bl ((blkPl_319).ρ "<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent as prost::message::Message>::encoded_len [local#2]" - (blkPl_319).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (encLen_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, rfl, -, -, -, -⟩ | ⟨inst, H, rfl, rfl, rfl, -, -, -, -⟩
  · have hf := hext b ext; rw [hoff, bv_bl_off_eq] at hf; exact hf
  · letI := inst; have h := @hpl inst H; simp only [blkPl_319_ρ, ls_resolve_blk_408] at h
    rw [show lsmpl.base 408 - (blkPl_319).base - BitVec.ofNat 64 k = (blkPl_408).base - ((blkPl_319).base + BitVec.ofNat 64 k) by change (blkPl_408).base - (blkPl_319).base - BitVec.ofNat 64 k = _; bv_omega] at h; exact h

theorem ct1_enc2_fetch_bl_varint_placed {prog : Program} {entry p1 varint_pc p3 p4 p5 : BitVec 64} {k : Nat} {off : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog entry p1 varint_pc p3 p4 p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) =
      some (Instr.bl ((blkPl_319).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" - (blkPl_319).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (varint_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, rfl, -, -, -⟩ | ⟨inst, H, rfl, rfl, -, rfl, -, -, -⟩
  · have hf := hext b ext; rw [hoff, bv_bl_off_eq] at hf; exact hf
  · letI := inst; have h := @hpl inst H; simp only [blkPl_319_ρ, ls_resolve_blk_292] at h
    rw [show lsmpl.base 292 - (blkPl_319).base - BitVec.ofNat 64 k = (blkPl_292).base - ((blkPl_319).base + BitVec.ofNat 64 k) by change (blkPl_292).base - (blkPl_319).base - BitVec.ofNat 64 k = _; bv_omega] at h; exact h

theorem ct1_enc2_fetch_bl_auth_placed {prog : Program} {entry p1 p2 auth_pc p4 p5 : BitVec 64} {k : Nat} {off : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog entry p1 p2 auth_pc p4 p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (2 ^ 64 - ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) =
      some (Instr.bl ((blkPl_319).ρ "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#2]" - (blkPl_319).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (auth_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, rfl, -, -⟩ | ⟨inst, H, rfl, rfl, -, -, rfl, -, -⟩
  · have hf := hext b ext; rw [hoff, bv_bl_off_eq] at hf; exact hf
  · letI := inst; have h := @hpl inst H; simp only [blkPl_319_ρ, ls_resolve_blk_314] at h
    rw [show lsmpl.base 314 - (blkPl_319).base - BitVec.ofNat 64 k = lsmpl.base 314 - ((blkPl_319).base + BitVec.ofNat 64 k) by bv_omega] at h; exact h

theorem ct1_enc2_fetch_bl_reserve_placed {prog : Program} {entry p1 p2 p3 reserve_pc p5 : BitVec 64} {k : Nat} {off : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog entry p1 p2 p3 reserve_pc p5)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) =
      some (Instr.bl ((blkPl_319).ρ "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]" - (blkPl_319).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (reserve_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, -, rfl, -⟩ | ⟨inst, H, rfl, rfl, -, -, -, rfl, -⟩
  · have hf := hext b ext; rw [hoff, bv_bl_off_eq] at hf; exact hf
  · letI := inst; have h := @hpl inst H; simp only [blkPl_319_ρ, ls_resolve_blk_320] at h
    rw [show lsmpl.base 320 - (blkPl_319).base - BitVec.ofNat 64 k = (blkPl_320).base - ((blkPl_319).base + BitVec.ofNat 64 k) by change (blkPl_320).base - (blkPl_319).base - BitVec.ofNat 64 k = _; bv_omega] at h; exact h

theorem ct1_enc2_fetch_bl_memcpy_placed {prog : Program} {entry p1 p2 p3 p4 memcpy_pc : BitVec 64} {k : Nat} {off : BitVec 64}
    (hfn : IsCt1Enc2EntryProg prog entry p1 p2 p3 p4 memcpy_pc)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch ((tripleRatchetProgAtExt b ext).fnAddr ct1SentEncode2Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]" "memcpy") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)), (lsProg_319 H).fetch ((blkPl_319).base + BitVec.ofNat 64 k) =
      some (Instr.bl ((blkPl_319).ρ "memcpy" - (blkPl_319).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (memcpy_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, -, -, rfl⟩ | ⟨inst, H, rfl, rfl, -, -, -, -, rfl⟩
  · have hf := hext b ext; rw [hoff, bv_bl_off_eq] at hf; exact hf
  · letI := inst; have h := @hpl inst H
    rw [show (blkPl_319).ρ "memcpy" - (blkPl_319).base - BitVec.ofNat 64 k = lsρ lsMemcpySym - ((blkPl_319).base + BitVec.ofNat 64 k) by change lsρ lsMemcpySym - (blkPl_319).base - BitVec.ofNat 64 k = _; bv_omega] at h; exact h

open Lean Meta Elab Tactic ProofLib in
/-- Fetch instructions in `[kStart, kEnd)` for `encode<Ct1Sent> [local#2]`. -/
elab "ct1_enc2_fetches_range_placed " hfn:term:max kStart:num kEnd:num : tactic => do
  let off := 0x4d93c
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1SentEncode2_fnOff
  let fEntry := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_entry_placed
  let fAdd := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_add_placed
  let fEncLen := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_bl_encLen_placed
  let fVarint := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_bl_varint_placed
  let fAuth := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_bl_auth_placed
  let fReserve := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_bl_reserve_placed
  let fMemcpy := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ct1_enc2_fetch_bl_memcpy_placed
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (Name.str `CryptoVerification.SpqrV1.Prost.MessageEncode
      ("libsignalSessionBin_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k))))
    let kHex := String.ofList (Nat.toDigits 16 k)
    let lsFetch := mkIdent (`CryptoVerification |>.str s!"blkPC_319_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fEntry $hfn (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff (by decide) $dec) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 68 then
      evalTactic (← `(tactic| have := $fEncLen (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 76 || k == 128 || k == 212 || k == 320 || k == 428 then
      evalTactic (← `(tactic| have := $fVarint (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 152 then
      evalTactic (← `(tactic| have := $fAuth (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 516 || k == 548 || k == 580 || k == 612 || k == 636 || k == 684 || k == 716 || k == 740 || k == 788 || k == 820 || k == 844 then
      evalTactic (← `(tactic| have := $fReserve (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 252 || k == 360 || k == 468 then
      evalTactic (← `(tactic| have := $fMemcpy (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else
      evalTactic (← `(tactic| have := $fAdd (k := $kq) $hfn (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec) (fun [LibsignalPlacement] H => $lsFetch _ H)))

/-! ## 1. Stage 1: Outer Header -/

private theorem step_hdr_from_44_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (g : Unchunked5PBGhost) (msgA v curCap curPtr sp : BitVec 64) (bs0 : List (BitVec 8)) (m : V1State.Unchunked.Ct1Sent)
    (hlt : bs0.length < curCap.toNat) (hlen_fit : ct1SentPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ curCap.toNat ∨ bs0.length + 1 + 10 < 2 ^ 64 - 2 ^ 62)
    (hfit' : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ curCap.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗ vecU8At A v curCap curPtr bs0 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = entry + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ curCap.toNat → cap1 = curCap ∧ ptr1 = curPtr) →
      SepWPp prog ret sm ((ct1SentPBPinnedAt A g msgA m ∗ vecU8At A v cap1 ptr1 (bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 44 80
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr bs0 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := encLen_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_ct1Sent_encoded_len_call_placed hres A hencLen g msgA sp (entry + 72#64) m hlen_fit
    (F := vecU8At A v curCap curPtr (bs0 ++ [0x0a#8]) ∗ A.pool ∗ F)
    an an an halign an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs0 0x0a#8 hlt]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv2
  have hhdr_eq : (bs0 ++ [0x0a#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length =
      bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length := by
    simp only [msgHeaderBytes, List.length_append, List.length_singleton]; omega
  have hvarint_fit : (bs0 ++ [0x0a#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen m))).length ≤ curCap.toNat ∨
      (bs0 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
    rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit'
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 (ct1SentPBEncodedLen m)) v curCap curPtr sp (entry + 80#64)
    (bs0 ++ [0x0a#8]) hvarint_fit (F := ct1SentPBPinnedAt A g msgA m ∗ F)
    an an an halign an an an an (cs_step hcs1 hinv2) (by ac_rfl) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge1 hpres1
  rw [hhdr_eq] at hpres1
  refine SepWPp.weaken_pre (by rw [bs_append_msgHeaderBytes bs0 (ct1SentPBEncodedLen m)]; exact Entails.of_eq (by ac_rfl))
    (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 (by rw [hcs12.1]; simp only [arm64_norm, *]) (by rw [hcs12.2.1]; simp only [arm64_norm, *]) hcs2 hge1 hpres1)

theorem step_ct1_hdr_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ct1SentEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (g : Unchunked5PBGhost) (msgA v cap0 ptr0 sp : BitVec 64) (bs0 : List (BitVec 8)) (m : V1State.Unchunked.Ct1Sent)
    (hcap_le : bs0.length ≤ cap0.toNat) (hlen_fit : ct1SentPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat ∨ bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = msgA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (ct1SentPBPinnedAt A g msgA m ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (unchunkedMsgEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 sv3 : BitVec 64),
      sm.pc = entry + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp prog ret sm
        ((ct1SentPBPinnedAt A g msgA m ∗ vecU8At A v cap1 ptr1 (bs0 ++ msgHeaderBytes (ct1SentPBEncodedLen m)) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
          ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep44 := step_hdr_from_44_2_placed hres A hfn hencLen henc
  ct1_enc2_fetches_range_placed hfn 0 44
  ct1_enc2_fetches_range_placed hfn 500 528
  examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := msgHeaderBytes_len_bounds (ct1SentPBEncodedLen m)
  rw [stackAt_unchunkedMsgEncode hres sp, vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0, vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  let S := ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
    ((sp - 48#64) ↦₆₄ s.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
    ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
    have hcap_eq : cap0.toNat = bs0.length := cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := reserveCap_one_bounds hcap_eq (by omega)
    refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap0 ptr0 sp
      (entry + 520#64) bs0 1 hbound1 (F := ct1SentPBPinnedAt A g msgA m ∗ S ∗ F)
      an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      an an an (cs_step hcs hinv0)
      (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs0, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 44#64); wp_steps; apply SepWP.done an an; intro hinv1
    exact hstep44 g msgA v newCap1 newPtr1 sp bs0 m hlt1 hlen_fit (Or.inr (by omega)) (Or.inr (by omega)) (F := S ∗ F)
      an an an halign an an an (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
      (cs_step hcs1 hinv1) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 _ =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 sv3 hpcm hrunm hspm htrm hx19m hx20m hcsm
            (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega))))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat := lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit44 : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    have hfit44' : bs0.length + (msgHeaderBytes (ct1SentPBEncodedLen m)).length ≤ cap0.toNat ∨ bs0.length + 1 + 10 < 2 ^ 64 - 2 ^ 62 := by
      rcases hfit44 with h | h; exact Or.inl h; exact Or.inr (by omega)
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 44#64); wp_steps; apply SepWP.done an an; intro hinv0
    exact hstep44 g msgA v cap0 ptr0 sp bs0 m hlt0 hlen_fit hfit44' hfit44 (F := S ∗ F)
      an an an halign an an an an (cs_step hcs hinv0)
      (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1 =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 sv3 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1))

/-! ## 2. Stage 2: Field 1 — `epoch: u64` -/

private theorem step_epoch_from_104_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (msgA v curCap curPtr epoch sp : BitVec 64) (bs1 : List (BitVec 8))
    (hep : (epoch == 0#64) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat ∨ bs1.length + 1 + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 104#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = epoch)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp prog ret sm ((vecU8At A v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 104 132
  examples_hide_fetches; subst hP
  have hep_ne : epoch ≠ 0#64 := beq_eq_false_iff_ne.mp hep
  have hep_len := u64Field1Bytes_len_of_ne_zero hep_ne
  rw [vecU8At_open_one A v curCap curPtr bs1 hlt]; simp only [sepExists_sepConj_left]; refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hlen_eq : (bs1 ++ [0x08#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length = bs1.length + (u64Field1Bytes epoch).length := by
    rw [List.length_append, List.length_singleton, hep_len]; omega
  have hvarint_fit : (bs1 ++ [0x08#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length ≤ curCap.toNat ∨ (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
    rw [hlen_eq, List.length_append, List.length_singleton]; exact hfit
  refine step_unchunked_encode_varint_call_placed hres A henc epoch v curCap curPtr sp (entry + 132#64)
    (bs1 ++ [0x08#8]) hvarint_fit (F := F) an an an halign an an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs1 0x08#8 hlt]) ?_
  intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge2 hpres2
  rw [hlen_eq] at hpres2
  refine SepWPp.weaken_pre (by rw [bs_append_u64Field1Bytes_of_ne_zero hep_ne bs1]; exact Entails.of_eq (by ac_rfl))
    (hnext s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 (by rw [hcs01.1]; simp only [arm64_norm, *]) (by rw [hcs01.2.1]; simp only [arm64_norm, *]) hcs1 hge2 hpres2)

theorem step_ct1_epoch_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (msgA v cap1 ptr1 epoch sp : BitVec 64) (bs1 : List (BitVec 8))
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨ bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 80#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (((msgA + 0x78#64) ↦₆₄ epoch) ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp prog ret sm ((((msgA + 0x78#64) ↦₆₄ epoch) ∗ vecU8At A v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep104 := step_epoch_from_104_2_placed hres A hfn henc
  ct1_enc2_fetches_range_placed hfn 80 104
  ct1_enc2_fetches_range_placed hfn 528 564
  examples_hide_fetches; subst hP
  by_cases hep : epoch == 0#64
  · apply SepWPp.of_sepWP_cs_placed (mid := entry + 132#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [← bs_append_u64Field1Bytes_of_zero (beq_iff_eq.mp hep) bs1]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))
  · have hep_f : (epoch == 0#64) = false := Bool.eq_false_iff.mpr hep
    have hep_len := u64Field1Bytes_len_of_ne_zero (beq_eq_false_iff_ne.mp hep_f)
    have hep_bds := Varint.encodeVarint_length_bounds epoch
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F) (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap1.toNat = bs1.length := cap_toNat_eq_of_beq hcap1 (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit2 : bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap1 ptr1 sp
        (entry + 552#64) bs1 1 hbound1 (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        an an an (cs_step hcs hinv0) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 104#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep104 msgA v newCap1 newPtr1 epoch sp bs1 hep_f hlt1 (Or.inr (by omega))
        (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F)
        an an an halign an (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        an an (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ =>
          SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega))))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat := lt_cap_toNat_of_beq_false hcap1_f hcap1_le (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit104 : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨ bs1.length + 1 + 10 < 2 ^ 62 := by
        rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 104#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep104 msgA v cap1 ptr1 epoch sp bs1 hep_f hlt1 hfit104
        (F := ((msgA + 0x78#64) ↦₆₄ epoch) ∗ F) an an an halign an an an an an (cs_step hcs hinv0)
        (by rw [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 =>
          SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2))

/-! ## 3. Stage 3: Field 2 — `auth: Option<Authenticator>` -/

theorem step_ct1_auth_2_placed {resStack : Nat}
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (hauthEnc : subroutine_ok prog auth_pc (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A)))
    (gAuth : AuthenticatorPBGhost) (msgA v cap2 ptr2 sp : BitVec 64)
    (bs2 : List (BitVec 8)) (optAuth : Option AuthenticatorPB)
    (hfit : bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat ∨ bs2.length + (optAuthField2Bytes optAuth).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 132#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (optAuthenticatorPBPinnedAt A gAuth (msgA + 0x48#64) optAuth ∗ vecU8At A v cap2 ptr2 bs2 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = entry + 156#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      SepWPp prog ret sm ((optAuthenticatorPBPinnedAt A gAuth (msgA + 0x48#64) optAuth ∗ vecU8At A v cap3 ptr3 (bs2 ++ optAuthField2Bytes optAuth) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 132 156
  examples_hide_fetches; subst hP
  cases optAuth with
  | none =>
    rw [optAuthenticatorPBPinnedAt]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 156#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [optAuthenticatorPBPinnedAt, ← bs_append_optAuthField2Bytes_none bs2]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap2 ptr2 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))
  | some auth =>
    rw [optAuthenticatorPBPinnedAt, authenticatorPBPinnedAt]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x48#64)
      (cap := gAuth.rootKey.cap) (ptr := gAuth.rootKey.ptr) (bs := auth.rootKey)
      (F := vecU8At A (msgA + 0x48#64 + 24#64) gAuth.macKey.cap gAuth.macKey.ptr auth.macKey ∗
        vecU8At A v cap2 ptr2 bs2 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F) (by ac_rfl) fun _ hrkCap_lt _ => ?_
    have hcap_beq := EncodedLen.cap_add_one_beq_zero_false hrkCap_lt
    have hcap_bne := EncodedLen.cap_add_one_bne_zero_true hrkCap_lt
    rw [vecU8At_eq_header_sep_buf A (msgA + 0x48#64) gAuth.rootKey.cap gAuth.rootKey.ptr auth.rootKey, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := auth_pc); wp_steps; apply SepWP.done an an; intro hinv0
    refine step_unchunked_auth_encode_call_placed A hauthEnc (msgA + 0x48#64) gAuth auth v cap2 ptr2 sp (entry + 156#64) bs2 hfit (F := F)
      an an an halign an an an an (cs_step hcs hinv0)
      (by rw [authenticatorPBPinnedAt, vecU8At_eq_header_sep_buf A (msgA + 0x48#64), vecHeader]; try ac_rfl) ?_
    intro s1 cap3 ptr3 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge3 hpres3
    refine SepWPp.weaken_pre (by rw [optAuthenticatorPBPinnedAt, bs_append_optAuthField2Bytes_some]; exact Entails.of_eq (by ac_rfl))
      (hnext s1 cap3 ptr3 hpc1 hrun1 hsp1 htr1 (by rw [hcs01.1]; simp only [arm64_norm, *]) (by rw [hcs01.2.1]; simp only [arm64_norm, *]) hcs1 hge3 hpres3)

/-! ## 4. Stage 4: Field 3 — `hdr: Vec<u8>` -/

private theorem step_hdrf_from_236_2_placed
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr) (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 236 264
  examples_hide_fetches; subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne; have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid) (F := vecU8At A msgA dkCap dkPtr dk ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk) (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos, vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_unchunked_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp (entry + 256#64) dk
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗ memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length) (curCap.toNat - bs_mid.length - dk.length) ∗
      (vecHeader msgA dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗ ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
        memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗ A.live dkPtr dkCap.toNat 1) ∗ F)
    an an an halign an an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 264#64); wp_steps; apply SepWP.done an an; intro hinv2
  refine SepWPp.weaken_pre ?_ (hnext _ an an an an an an (cs_step hcs1 hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil, vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  exact Entails.of_eq (by ac_rfl)

private theorem step_hdrf_from_184_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat ∨ bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat → cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp prog ret sm ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep236 := step_hdrf_from_236_2_placed A hfn hmemcpy
  ct1_enc2_fetches_range_placed hfn 184 236
  ct1_enc2_fetches_range_placed hfn 592 636
  examples_hide_fetches; subst hP
  have hdk_len := bytesField3_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A v curCap curPtr bs3 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hvarint_fit : (bs3 ++ [0x1a#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨ (bs3 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 dk.length) v curCap curPtr sp (entry + 216#64)
    (bs3 ++ [0x1a#8]) hvarint_fit (F := vecU8At A msgA dkCap dkPtr dk ∗ F)
    an an an halign an an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs3 0x1a#8 hlt]; ac_rfl) ?_
  intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
  let bs_mid := (bs3 ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)
  have hbs_mid_len : bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 3#32 dk).length := by
    dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid) (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ vecU8At A msgA dkCap dkPtr dk ∗ F)
    (by dsimp [bs_mid]; ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap_mid ptr_mid bs_mid, vecHeader]
  have hdk_lt63 : dk.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap_mid.toNat < bs_mid.length + dk.length
  · have hfit_dk : bs_mid.length + dk.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = true := (elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mpr hneed
    obtain ⟨hnot_ult, hle_res, hge_res, hbound_dk⟩ := elem_len_after_reserve_not_ult hfit_dk hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv2
    refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap_mid ptr_mid sp (entry + 616#64) bs_mid dk.length hbound_dk (F := vecU8At A msgA dkCap dkPtr dk ∗ F)
      an an an halign an an an
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      an an (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
    change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap_res ptr_res bs_mid, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 236#64); wp_steps; apply SepWP.done an an; intro hinv3
    exact hstep236 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs3 hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm => SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField3_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl)) (hnext sm cap_res ptr_res hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge_mid hge_res) (fun h => absurd h (by omega))))
  · have hle_fast : bs_mid.length + dk.length ≤ cap_mid.toNat := by omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = false := Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mp h)
    have hpres_all : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
      intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 236#64); wp_steps; apply SepWP.done an an; intro hinv2
    exact hstep236 msgA v cap_mid ptr_mid dkCap dkPtr sp bs_mid dk hdk_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs2 hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm => SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField3_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl)) (hnext sm cap_mid ptr_mid hpcm hrunm hspm htrm hx19m hx20m hcsm hge_mid hpres_all))

theorem step_ct1_hdrf_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat ∨ bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = entry + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat → cap4 = cap3 ∧ ptr4 = ptr3) →
      SepWPp prog ret sm ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep184 := step_hdrf_from_184_2_placed hres A hfn henc hdoReserve hmemcpy
  ct1_enc2_fetches_range_placed hfn 156 184
  ct1_enc2_fetches_range_placed hfn 564 592
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk) (F := vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField3_len_of_ne_empty hdk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap3) (ptr := ptr3) (bs := bs3) (F := vecU8At A msgA dkCap dkPtr dk ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs3, vecHeader, vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap3.toNat = bs3.length := cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap3 ptr3 sp (entry + 584#64) bs3 1 hbound1 (F := vecU8At A msgA dkCap dkPtr dk ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        an an an (cs_step hcs hinv0) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs3, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 184#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep184 msgA v newCap1 newPtr1 dkCap dkPtr sp bs3 dk hdk hlt1 (Or.inr hfit2) (F := F)
        an an an halign an an an
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ => hnext sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat := lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 184#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep184 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk hdk hlt3 hfit (F := F)
        an an an halign an an an an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · rw [vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 264#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [← bs_append_bytesFieldTagged_of_empty 3#32 hdk bs3,
        vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap3 ptr3 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## 5. Stage 5: Field 4 — `es: Vec<u8>` -/

private theorem step_es_from_344_2_placed
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr) (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm ((vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ct1_enc2_fetches_range_placed hfn 344 372
  examples_hide_fetches; subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne; have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid) (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := dkCap) (ptr := dkPtr) (bs := dk) (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos, vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_unchunked_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp (entry + 364#64) dk
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗ memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length) (curCap.toNat - bs_mid.length - dk.length) ∗
      (vecHeader (msgA + 0x18#64) dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗ ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
        memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗ A.live dkPtr dkCap.toNat 1) ∗ F)
    an an an halign an an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 372#64); wp_steps; apply SepWP.done an an; intro hinv2
  refine SepWPp.weaken_pre ?_ (hnext _ an an an an an an (cs_step hcs1 hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil, vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) dkCap dkPtr dk hdk_ne_nil hdk_le]
  exact Entails.of_eq (by ac_rfl)

private theorem step_es_from_292_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat ∨ bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat → cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp prog ret sm ((vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep344 := step_es_from_344_2_placed A hfn hmemcpy
  ct1_enc2_fetches_range_placed hfn 292 344
  ct1_enc2_fetches_range_placed hfn 696 740
  examples_hide_fetches; subst hP
  have hdk_len := bytesField4_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A v curCap curPtr bs3 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hvarint_fit : (bs3 ++ [0x22#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨ (bs3 ++ [0x22#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 dk.length) v curCap curPtr sp (entry + 324#64)
    (bs3 ++ [0x22#8]) hvarint_fit (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
    an an an halign an an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs3 0x22#8 hlt]; ac_rfl) ?_
  intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
  let bs_mid := (bs3 ++ [0x22#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)
  have hbs_mid_len : bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 4#32 dk).length := by
    dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid) (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
    (by dsimp [bs_mid]; ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap_mid ptr_mid bs_mid, vecHeader]
  have hdk_lt63 : dk.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap_mid.toNat < bs_mid.length + dk.length
  · have hfit_dk : bs_mid.length + dk.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = true := (elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mpr hneed
    obtain ⟨hnot_ult, hle_res, hge_res, hbound_dk⟩ := elem_len_after_reserve_not_ult hfit_dk hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv2
    refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap_mid ptr_mid sp (entry + 720#64) bs_mid dk.length hbound_dk (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
      an an an halign an an an
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      an an (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
    change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap_res ptr_res bs_mid, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 344#64); wp_steps; apply SepWP.done an an; intro hinv3
    exact hstep344 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs3 hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm => SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField4_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl)) (hnext sm cap_res ptr_res hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge_mid hge_res) (fun h => absurd h (by omega))))
  · have hle_fast : bs_mid.length + dk.length ≤ cap_mid.toNat := by omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = false := Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mp h)
    have hpres_all : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
      intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 344#64); wp_steps; apply SepWP.done an an; intro hinv2
    exact hstep344 msgA v cap_mid ptr_mid dkCap dkPtr sp bs_mid dk hdk_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs2 hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm => SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField4_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl)) (hnext sm cap_mid ptr_mid hpcm hrunm hspm htrm hx19m hx20m hcsm hge_mid hpres_all))

theorem step_ct1_es_2_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsCt1Enc2EntryProg prog entry encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hfit : bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat ∨ bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop} (hpc : s.pc = entry + 264#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = entry + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 4#32 dk).length ≤ cap3.toNat → cap4 = cap3 ∧ ptr4 = ptr3) →
      SepWPp prog ret sm ((vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 4#32 dk) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep292 := step_es_from_292_2_placed hres A hfn henc hdoReserve hmemcpy
  ct1_enc2_fetches_range_placed hfn 264 292
  ct1_enc2_fetches_range_placed hfn 668 696
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := dkCap) (ptr := dkPtr) (bs := dk) (F := vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField4_len_of_ne_empty hdk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap3) (ptr := ptr3) (bs := bs3) (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs3, vecHeader, vecU8At_eq_header_sep_buf A (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap3.toNat = bs3.length := cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 4#32 dk).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve7_call_placed hres A hdoReserve v cap3 ptr3 sp (entry + 688#64) bs3 1 hbound1 (F := vecU8At A (msgA + 0x18#64) dkCap dkPtr dk ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        an an an (cs_step hcs hinv0) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs3, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 292#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep292 msgA v newCap1 newPtr1 dkCap dkPtr sp bs3 dk hdk hlt1 (Or.inr hfit2) (F := F)
        an an an halign an an an
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ => hnext sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat := lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 292#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep292 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk hdk hlt3 hfit (F := F)
        an an an halign an an an an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · rw [vecU8At_eq_header_sep_buf A (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 372#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [← bs_append_bytesFieldTagged_of_empty 4#32 hdk bs3,
        vecU8At_eq_header_sep_buf A (msgA + 0x18#64) dkCap dkPtr dk, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap3 ptr3 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))


end CryptoVerification.SpqrV1.Prost.MessageEncode
