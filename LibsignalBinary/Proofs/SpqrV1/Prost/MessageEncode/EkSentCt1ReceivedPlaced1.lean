/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodePlaced1
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Proof of `encode<EkSentCt1Received> [local#1]` (Block 155)

Relocatable per-block verification of the first monomorphization
`prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#1]`
(Block 155, calling `EkSentCt1Received::encoded_len [local#1]` in Block 192,
`encode_varint [local#2]` in Block 148, `encode<Authenticator> [local#1]` in Block 151,
`do_reserve_and_handle [local#2]` in Block 157, and `memcpy`).
-/

@[expose] public section

set_option autoImplicit false

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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem bv_pc_add_sub_cancel_ek1 (a b : BitVec 64) : a + (b - a) = b := by bv_omega

local macro "an" : term => `(by simp only [arm64_norm, *])
local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(UnchunkedEncodeCalleeSavedPlaced.step $hcs (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) $hinv)

def IsEkEnc1PlacedProg (prog : Program) (fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64) : Prop :=
  ∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_155 H ∧ fnBase = (blkPl_155).base ∧ encLen_pc = (blkPl_192).base ∧
    varint_pc = (blkPl_148).base ∧ auth_pc = lsmpl.base 151 ∧
    reserve_pc = (blkPl_157).base ∧ memcpy_pc = lsρ lsMemcpySym

private theorem ek_enc1_fetch_entry_placed {prog : Program} {fnBase p1 p2 p3 p4 p5 : BitVec 64} {instr : Instr}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 p2 p3 p4 p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + 0#64) = some instr) :
    prog.fetch fnBase = some instr := by
  rcases hfn with ⟨inst, H, rfl, rfl, -, -, -, -, -⟩
  letI := inst; have h := @hpl inst H; rwa [BitVec.add_zero] at h

private theorem ek_enc1_fetch_add_placed {prog : Program} {fnBase p1 p2 p3 p4 p5 : BitVec 64} {k : Nat} {instr : Instr}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 p2 p3 p4 p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) = some instr) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some instr := by
  rcases hfn with ⟨_, H, rfl, rfl, -, -, -, -, -⟩; exact hpl H

private theorem ek_enc1_fetch_bl_encLen_placed {prog : Program} {fnBase encLen_pc p2 p3 p4 p5 : BitVec 64} {k : Nat}
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc p2 p3 p4 p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_155).ρ "<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received as prost::message::Message>::encoded_len [local#1]" - (blkPl_155).base - BitVec.ofNat 64 k))) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some (Instr.bl (encLen_pc - (fnBase + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨inst, H, rfl, rfl, rfl, -, -, -, -⟩
  letI := inst; have h := @hpl inst H; simp only [blkPl_155_ρ, ls_resolve_blk_192] at h
  rw [show lsmpl.base 192 - (blkPl_155).base - BitVec.ofNat 64 k =
      (blkPl_192).base - ((blkPl_155).base + BitVec.ofNat 64 k) by
    change (blkPl_192).base - (blkPl_155).base - BitVec.ofNat 64 k = _; bv_omega] at h
  exact h

private theorem ek_enc1_fetch_bl_varint_placed {prog : Program} {fnBase p1 varint_pc p3 p4 p5 : BitVec 64} {k : Nat}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 varint_pc p3 p4 p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_155).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" - (blkPl_155).base - BitVec.ofNat 64 k))) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some (Instr.bl (varint_pc - (fnBase + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨inst, H, rfl, rfl, -, rfl, -, -, -⟩
  letI := inst; have h := @hpl inst H; simp only [blkPl_155_ρ, ls_resolve_blk_148] at h
  rw [show lsmpl.base 148 - (blkPl_155).base - BitVec.ofNat 64 k =
      (blkPl_148).base - ((blkPl_155).base + BitVec.ofNat 64 k) by
    change (blkPl_148).base - (blkPl_155).base - BitVec.ofNat 64 k = _; bv_omega] at h
  exact h

private theorem ek_enc1_fetch_bl_auth_placed {prog : Program} {fnBase p1 p2 auth_pc p4 p5 : BitVec 64} {k : Nat}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 p2 auth_pc p4 p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_155).ρ "prost::encoding::message::encode::<spqr::proto::pq_ratchet::Authenticator, alloc::vec::Vec<u8>> [local#1]" - (blkPl_155).base - BitVec.ofNat 64 k))) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some (Instr.bl (auth_pc - (fnBase + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨inst, H, rfl, rfl, -, -, rfl, -, -⟩
  letI := inst; have h := @hpl inst H; simp only [blkPl_155_ρ, ls_resolve_blk_151] at h
  rw [show lsmpl.base 151 - (blkPl_155).base - BitVec.ofNat 64 k =
      lsmpl.base 151 - ((blkPl_155).base + BitVec.ofNat 64 k) by bv_omega] at h
  exact h

private theorem ek_enc1_fetch_bl_reserve_placed {prog : Program} {fnBase p1 p2 p3 reserve_pc p5 : BitVec 64} {k : Nat}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 p2 p3 reserve_pc p5)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_155).ρ "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]" - (blkPl_155).base - BitVec.ofNat 64 k))) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some (Instr.bl (reserve_pc - (fnBase + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨inst, H, rfl, rfl, -, -, -, rfl, -⟩
  letI := inst; have h := @hpl inst H; simp only [blkPl_155_ρ, ls_resolve_blk_157] at h
  rw [show lsmpl.base 157 - (blkPl_155).base - BitVec.ofNat 64 k =
      (blkPl_157).base - ((blkPl_155).base + BitVec.ofNat 64 k) by
    change (blkPl_157).base - (blkPl_155).base - BitVec.ofNat 64 k = _; bv_omega] at h
  exact h

private theorem ek_enc1_fetch_bl_memcpy_placed {prog : Program} {fnBase p1 p2 p3 p4 memcpy_pc : BitVec 64} {k : Nat}
    (hfn : IsEkEnc1PlacedProg prog fnBase p1 p2 p3 p4 memcpy_pc)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_155 H).fetch ((blkPl_155).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_155).ρ "memcpy" - (blkPl_155).base - BitVec.ofNat 64 k))) :
    prog.fetch (fnBase + BitVec.ofNat 64 k) = some (Instr.bl (memcpy_pc - (fnBase + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨inst, H, rfl, rfl, -, -, -, -, rfl⟩
  letI := inst; have h := @hpl inst H
  rw [show (blkPl_155).ρ "memcpy" - (blkPl_155).base - BitVec.ofNat 64 k =
      lsρ lsMemcpySym - ((blkPl_155).base + BitVec.ofNat 64 k) by
    change lsρ lsMemcpySym - (blkPl_155).base - BitVec.ofNat 64 k = _; bv_omega] at h
  exact h

open Lean Meta Elab Tactic ProofLib in
/-- Fetch instructions in `[kStart, kEnd)` for `encode<EkSentCt1Received> [local#1]` (Block 155). -/
elab "ek_enc1_fetches_range_placed " hfn:term:max kStart:num kEnd:num : tactic => do
  let fEntry := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_entry_placed
  let fAdd := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_add_placed
  let fEncLen := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_bl_encLen_placed
  let fVarint := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_bl_varint_placed
  let fAuth := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_bl_auth_placed
  let fReserve := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_bl_reserve_placed
  let fMemcpy := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ek_enc1_fetch_bl_memcpy_placed
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let kHex := String.ofList (Nat.toDigits 16 k)
    let lsFetch := mkIdent (`CryptoVerification |>.str s!"blkPC_155_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| have := $fEntry $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 68 then
      evalTactic (← `(tactic| have := $fEncLen (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 76 || k == 128 || k == 212 || k == 320 then
      evalTactic (← `(tactic| have := $fVarint (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 152 then
      evalTactic (← `(tactic| have := $fAuth (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 400 || k == 424 || k == 448 || k == 472 || k == 508 || k == 528 || k == 552 || k == 588 then
      evalTactic (← `(tactic| have := $fReserve (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 252 || k == 360 then
      evalTactic (← `(tactic| have := $fMemcpy (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else
      evalTactic (← `(tactic| have := $fAdd (k := $kq) $hfn (fun [LibsignalPlacement] H => $lsFetch _ H)))

/-! ## 1. Stage 1: Outer Header -/

private theorem step_ek_hdr_from_44_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (g : Unchunked4PBGhost) (msgA v curCap curPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.EkSentCt1Received)
    (hlt : bs0.length < curCap.toNat) (hlen_fit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ curCap.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 44#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs0.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v curCap curPtr bs0 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = fnBase + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ curCap.toNat → cap1 = curCap ∧ ptr1 = curPtr) →
      SepWPp prog ret sm ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
        vecU8At A v cap1 ptr1 (bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ∗
        A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 44 80; examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr bs0 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := encLen_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_ekSentCt1Received_encoded_len_call_placed hres A hencLen g msgA sp (fnBase + 72#64) m hlen_fit
    (F := vecU8At A v curCap curPtr (bs0 ++ [0x0a#8]) ∗ A.pool ∗ F) an an an halign an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs0 0x0a#8 hlt]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv2
  have hhdr_eq : (bs0 ++ [0x0a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length =
      bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length := by
    simp only [msgHeaderBytes, List.length_append, List.length_singleton]; omega
  have hvarint_fit : (bs0 ++ [0x0a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m))).length ≤ curCap.toNat ∨
      (bs0 ++ [0x0a#8]).length + 10 < 2 ^ 62 := by
    rw [hhdr_eq, List.length_append, List.length_singleton]; exact hfit
  refine step_unchunked_encode_varint_call_placed hres A henc
    (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen m)) v curCap curPtr sp (fnBase + 80#64)
    (bs0 ++ [0x0a#8]) hvarint_fit (F := ekSentCt1ReceivedPBPinnedAt A g msgA m ∗ F)
    an an an halign an an an an (cs_step hcs1 hinv2) (by ac_rfl) ?_
  intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge1 hpres1; rw [hhdr_eq] at hpres1
  refine SepWPp.weaken_pre (by rw [bs_append_msgHeaderBytes bs0 (ekSentCt1ReceivedPBEncodedLen m)]; exact Entails.of_eq (by ac_rfl))
    (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2
      (by rw [hcs12.1]; simp only [arm64_norm, *]) (by rw [hcs12.2.1]; simp only [arm64_norm, *]) hcs2 hge1 hpres1)

theorem step_ek_hdr_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (g : Unchunked4PBGhost) (msgA v cap0 ptr0 sp : BitVec 64)
    (bs0 : List (BitVec 8)) (m : V1State.Unchunked.EkSentCt1Received)
    (hcap_le : bs0.length ≤ cap0.toNat) (hlen_fit : ekSentCt1ReceivedPBEncodedLen m < 2 ^ 64)
    (hfit : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat ∨
      bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase) (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = msgA) (hx1 : s.readReg64 .x1 = v)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (unchunkedMsgEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 sv3 : BitVec 64),
      sm.pc = fnBase + 80#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp prog ret sm ((ekSentCt1ReceivedPBPinnedAt A g msgA m ∗
        vecU8At A v cap1 ptr1 (bs0 ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)) ∗
        A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
        ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep44 := step_ek_hdr_from_44_1_placed hres A hfn hencLen henc
  ek_enc1_fetches_range_placed hfn 0 44; ek_enc1_fetches_range_placed hfn 392 412; examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  have hhdr_bds := msgHeaderBytes_len_bounds (ekSentCt1ReceivedPBEncodedLen m)
  rw [stackAt_unchunkedMsgEncode hres sp, vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0, vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 => SepWPp.exists_elim fun sv2 =>
    SepWPp.exists_elim fun sv3 => SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  let S := ((sp - 64#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .lr) ∗
    ((sp - 48#64) ↦₆₄ s.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
    ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
    ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)
  by_cases hcap0 : cap0 == BitVec.ofNat 64 bs0.length
  · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
    have hcap_eq : cap0.toNat = bs0.length :=
      CryptoVerification.SpqrV1.Auth.cap_toNat_eq_of_beq hcap0 (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit2 : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
    obtain ⟨hbound1, hlt1, hge0⟩ := CryptoVerification.SpqrV1.Auth.reserveCap_one_bounds hcap_eq (by omega)
    refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap0 ptr0 sp
      (fnBase + 404#64) bs0 1 hbound1 (F := ekSentCt1ReceivedPBPinnedAt A g msgA m ∗ S ∗ F)
      an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (by simp only [arm64_norm]) (cs_step hcs hinv0) (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl) ?_
    intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
    let newCap1 := BitVec.ofNat 64 (reserveCap cap0.toNat bs0.length 1)
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs0, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 44#64); wp_steps; apply SepWP.done an an; intro hinv1
    exact hstep44 g msgA v newCap1 newPtr1 sp bs0 m hlt1 hlen_fit (Or.inr (by omega)) (F := S ∗ F)
      an an an halign an an an (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
      (cs_step hcs1 hinv1) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 _ =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 sv3 hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge0 hge1) (fun h => absurd h (by omega))))
  · have hcap0_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := Bool.eq_false_iff.mpr hcap0
    have hlt0 : bs0.length < cap0.toNat :=
      CryptoVerification.SpqrV1.Auth.lt_cap_toNat_of_beq_false hcap0_f hcap_le (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt cap0))
    have hfit44 : bs0.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen m)).length ≤ cap0.toNat ∨ bs0.length + 1 + 10 < 2 ^ 62 := by
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 44#64); wp_steps; apply SepWP.done an an; intro hinv0
    exact hstep44 g msgA v cap0 ptr0 sp bs0 m hlt0 hlen_fit hfit44 (F := S ∗ F)
      an an an halign an an an an (cs_step hcs hinv0) (by dsimp [S]; rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl)
      (fun sm cap1 ptr1 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1 =>
        SepWPp.weaken_pre (Entails.of_eq (by dsimp [S]; ac_rfl))
          (hnext sm cap1 ptr1 sv3 hpcm hrunm hspm htrm hx19m hx20m hcsm hge1 hpres1))

/-! ## 2. Stage 2: Field 1 — `epoch: u64` -/

private theorem step_ek_epoch_from_104_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (msgA v curCap curPtr epoch sp : BitVec 64) (bs1 : List (BitVec 8))
    (hep : (epoch == 0#64) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat ∨ bs1.length + 1 + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 104#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = epoch) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = fnBase + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp prog ret sm ((vecU8At A v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
        A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 104 132; examples_hide_fetches; subst hP
  have hep_ne : epoch ≠ 0#64 := beq_eq_false_iff_ne.mp hep
  have hep_len := u64Field1Bytes_len_of_ne_zero hep_ne
  rw [vecU8At_open_one A v curCap curPtr bs1 hlt]; simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hlen_eq : (bs1 ++ [0x08#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length =
      bs1.length + (u64Field1Bytes epoch).length := by rw [List.length_append, List.length_singleton, hep_len]; omega
  have hvarint_fit : (bs1 ++ [0x08#8]).length + (CryptoVerification.LibsignalProtoCodec.encodeVarint epoch).length ≤ curCap.toNat ∨
      (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by rw [hlen_eq, List.length_append, List.length_singleton]; exact hfit
  refine step_unchunked_encode_varint_call_placed hres A henc epoch v curCap curPtr sp (fnBase + 132#64)
    (bs1 ++ [0x08#8]) hvarint_fit (F := F) an an an halign an an an an (cs_step hcs hinv1)
    (by rw [← vecU8At_close_one A v curCap curPtr bs1 0x08#8 hlt]) ?_
  intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge2 hpres2; rw [hlen_eq] at hpres2
  refine SepWPp.weaken_pre (by rw [bs_append_u64Field1Bytes_of_ne_zero hep_ne bs1]; exact Entails.of_eq (by ac_rfl))
    (hnext s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1
      (by rw [hcs01.1]; simp only [arm64_norm, *]) (by rw [hcs01.2.1]; simp only [arm64_norm, *]) hcs1 hge2 hpres2)

theorem step_ek_epoch_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (msgA v cap1 ptr1 epoch sp : BitVec 64) (bs1 : List (BitVec 8))
    (hfit : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨ bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 80#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (((msgA + 0x60#64) ↦₆₄ epoch) ∗
      vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = fnBase + 132#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA → UnchunkedEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp prog ret sm ((((msgA + 0x60#64) ↦₆₄ epoch) ∗ vecU8At A v cap2 ptr2 (bs1 ++ u64Field1Bytes epoch) ∗
        A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep104 := step_ek_epoch_from_104_1_placed hres A hfn henc
  ek_enc1_fetches_range_placed hfn 80 104; ek_enc1_fetches_range_placed hfn 412 440; examples_hide_fetches; subst hP
  by_cases hep : epoch == 0#64
  · apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 132#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre (by rw [← bs_append_u64Field1Bytes_of_zero (beq_iff_eq.mp hep) bs1]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))
  · have hep_f : (epoch == 0#64) = false := Bool.eq_false_iff.mpr hep
    have hep_len := u64Field1Bytes_len_of_ne_zero (beq_eq_false_iff_ne.mp hep_f)
    have hep_bds := Varint.encodeVarint_length_bounds epoch
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap1.toNat = bs1.length :=
        CryptoVerification.SpqrV1.Auth.cap_toNat_eq_of_beq hcap1 (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit2 : bs1.length + (u64Field1Bytes epoch).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := CryptoVerification.SpqrV1.Auth.reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap1 ptr1 sp
        (fnBase + 428#64) bs1 1 hbound1 (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (cs_step hcs hinv0) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 104#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep104 msgA v newCap1 newPtr1 epoch sp bs1 hep_f hlt1 (Or.inr (by omega))
        (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F) an an an halign an
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        an an (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ =>
          SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
            (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega))))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat :=
        CryptoVerification.SpqrV1.Auth.lt_cap_toNat_of_beq_false hcap1_f hcap1_le (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1))
      have hfit104 : bs1.length + (u64Field1Bytes epoch).length ≤ cap1.toNat ∨ bs1.length + 1 + 10 < 2 ^ 62 := by
        rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 104#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep104 msgA v cap1 ptr1 epoch sp bs1 hep_f hlt1 hfit104 (F := ((msgA + 0x60#64) ↦₆₄ epoch) ∗ F)
        an an an halign an an an an an (cs_step hcs hinv0) (by rw [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2 =>
          SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 hpres2))

/-! ## 3. Stage 3: Field 2 — `auth: Option<Authenticator>` -/

theorem step_ek_auth_1_placed {resStack : Nat}
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (hauthEnc : subroutine_ok prog auth_pc (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A)))
    (gAuth : AuthenticatorPBGhost) (msgA v cap2 ptr2 sp : BitVec 64)
    (bs2 : List (BitVec 8)) (optAuth : Option AuthenticatorPB)
    (hfit : bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat ∨
      bs2.length + (optAuthField2Bytes optAuth).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 132#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (optAuthenticatorPBPinnedAt A gAuth (msgA + 0x30#64) optAuth ∗
      vecU8At A v cap2 ptr2 bs2 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = fnBase + 156#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (optAuthField2Bytes optAuth).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      SepWPp prog ret sm
        ((optAuthenticatorPBPinnedAt A gAuth (msgA + 0x30#64) optAuth ∗
          vecU8At A v cap3 ptr3 (bs2 ++ optAuthField2Bytes optAuth) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 132 156
  examples_hide_fetches; subst hP
  cases optAuth with
  | none =>
    rw [optAuthenticatorPBPinnedAt]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 156#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre
      (by rw [optAuthenticatorPBPinnedAt, ← bs_append_optAuthField2Bytes_none bs2]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap2 ptr2 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))
  | some auth =>
    rw [optAuthenticatorPBPinnedAt, authenticatorPBPinnedAt]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x30#64)
      (cap := gAuth.rootKey.cap) (ptr := gAuth.rootKey.ptr) (bs := auth.rootKey)
      (F := vecU8At A (msgA + 0x30#64 + 24#64) gAuth.macKey.cap gAuth.macKey.ptr auth.macKey ∗
        vecU8At A v cap2 ptr2 bs2 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun _ hrkCap_lt _ => ?_
    have hcap_beq := EncodedLen.cap_add_one_beq_zero_false hrkCap_lt
    have hcap_bne := EncodedLen.cap_add_one_bne_zero_true hrkCap_lt
    rw [vecU8At_eq_header_sep_buf A (msgA + 0x30#64) gAuth.rootKey.cap gAuth.rootKey.ptr auth.rootKey, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := auth_pc); wp_steps; apply SepWP.done an an; intro hinv0
    refine step_unchunked_auth_encode_call_placed A hauthEnc
      (msgA + 0x30#64) gAuth auth v cap2 ptr2 sp (fnBase + 156#64) bs2 hfit (F := F)
      an an an halign an an an an (cs_step hcs hinv0)
      (by rw [authenticatorPBPinnedAt, vecU8At_eq_header_sep_buf A (msgA + 0x30#64), vecHeader]; try ac_rfl) ?_
    intro s1 cap3 ptr3 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hge3 hpres3
    refine SepWPp.weaken_pre
      (by rw [optAuthenticatorPBPinnedAt, bs_append_optAuthField2Bytes_some]; exact Entails.of_eq (by ac_rfl))
      (hnext s1 cap3 ptr3 hpc1 hrun1 hsp1 htr1
        (by rw [hcs01.1]; simp only [arm64_norm, *]) (by rw [hcs01.2.1]; simp only [arm64_norm, *])
        hcs1 hge3 hpres3)

/-! ## 4. Stage 4: Field 3 — `dk: Vec<u8>` -/

private theorem step_ek_dk_from_236_1_placed
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs_mid dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hle : bs_mid.length + dk.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = fnBase + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A msgA dkCap dkPtr dk ∗ vecU8At A v curCap curPtr (bs_mid ++ dk)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 236 264
  examples_hide_fetches; subst hP
  have hdk_ne_nil : dk ≠ [] := List.isEmpty_eq_false_iff.mp hdk_ne
  have hdk_pos : 0 < dk.length := List.length_pos_of_ne_nil hdk_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A msgA dkCap dkPtr dk ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by ac_rfl) fun hdk_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid dk.length hle hcap_lt hptr_ne hdk_pos,
    vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_unchunked_memcpy_call_placed hmemcpy
    (curPtr + BitVec.ofNat 64 bs_mid.length) dkPtr sp (fnBase + 256#64) dk
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 dk.length)
        (curCap.toNat - bs_mid.length - dk.length) ∗
      (vecHeader msgA dkCap dkPtr (BitVec.ofNat 64 dk.length) ∗
        ⌜dkPtr ≠ 0 ∧ dk.length ≤ dkCap.toNat ∧ dkCap.toNat < 2 ^ 63⌝ ∗
        memRegion (dkPtr + BitVec.ofNat 64 dk.length) (dkCap.toNat - dk.length) ∗
        A.live dkPtr dkCap.toNat 1) ∗ F)
    an an an halign an an an an
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = msgA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 264#64); wp_steps; apply SepWP.done an an; intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ an an an an an an (cs_step hcs1 hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs_mid dk hle hcap_lt hptr_ne hdk_ne_nil,
    vecU8At_expose_src_of_ne_nil_placed A msgA dkCap dkPtr dk hdk_ne_nil hdk_le]
  exact Entails.of_eq (by ac_rfl)

private theorem step_ek_dk_from_184_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hdk_ne : dk.isEmpty = false) (hlt : bs3.length < curCap.toNat)
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs3.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 dk.length) (hx22 : s.readReg64 .x22 = dkPtr)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗
      vecU8At A v curCap curPtr bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = fnBase + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat → cap4 = curCap ∧ ptr4 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A msgA dkCap dkPtr dk ∗
          vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep236 := step_ek_dk_from_236_1_placed A hfn hmemcpy
  ek_enc1_fetches_range_placed hfn 184 236; ek_enc1_fetches_range_placed hfn 460 496; examples_hide_fetches; subst hP
  have hdk_len := bytesField3_len_of_ne_empty hdk_ne
  rw [vecU8At_open_one A v curCap curPtr bs3 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hvarint_fit : (bs3 ++ [0x1a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)).length ≤ curCap.toNat ∨
      (bs3 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 dk.length) v curCap curPtr sp (fnBase + 216#64)
    (bs3 ++ [0x1a#8]) hvarint_fit (F := vecU8At A msgA dkCap dkPtr dk ∗ F)
    an an an halign an an an an (cs_step hcs hinv1) (by rw [← vecU8At_close_one A v curCap curPtr bs3 0x1a#8 hlt]; ac_rfl) ?_
  intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
  let bs_mid := (bs3 ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 dk.length)
  have hbs_mid_len : bs_mid.length + dk.length = bs3.length + (bytesFieldTagged 3#32 dk).length := by
    dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hdk_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = msgA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = dkPtr := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid)
    (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ vecU8At A msgA dkCap dkPtr dk ∗ F)
    (by dsimp [bs_mid]; ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap_mid ptr_mid bs_mid, vecHeader]
  have hdk_lt63 : dk.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap_mid.toNat < bs_mid.length + dk.length
  · have hfit_dk : bs_mid.length + dk.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = true :=
      (elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mpr hneed
    obtain ⟨hnot_ult, hle_res, hge_res, hbound_dk⟩ := elem_len_after_reserve_not_ult hfit_dk hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv2
    refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap_mid ptr_mid sp
      (fnBase + 476#64) bs_mid dk.length hbound_dk (F := vecU8At A msgA dkCap dkPtr dk ∗ F) an an an halign an an an
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length dk.length)
    change (BitVec.ofNat 64 dk.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = msgA := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 dk.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = dkPtr := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap_res ptr_res bs_mid, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 236#64); wp_steps; apply SepWP.done an an; intro hinv3
    exact hstep236 msgA v cap_res ptr_res dkCap dkPtr sp bs_mid dk hdk_ne hle_res
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs3 hinv3) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField3_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_res ptr_res hpcm hrunm hspm htrm hx19m hx20m hcsm (Nat.le_trans hge_mid hge_res) (fun h => absurd h (by omega))))
  · have hle_fast : bs_mid.length + dk.length ≤ cap_mid.toNat := by omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 dk.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hdk_lt63).mp h)
    have hpres_all : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
      intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 236#64); wp_steps; apply SepWP.done an an; intro hinv2
    exact hstep236 msgA v cap_mid ptr_mid dkCap dkPtr sp bs_mid dk hdk_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an an (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField3_of_ne_empty hdk_ne bs3]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_mid ptr_mid hpcm hrunm hspm htrm hx19m hx20m hcsm hge_mid hpres_all))

theorem step_ek_dk_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v cap3 ptr3 dkCap dkPtr sp : BitVec 64) (bs3 dk : List (BitVec 8))
    (hfit : bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A msgA dkCap dkPtr dk ∗
      vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = fnBase + 264#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = msgA →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → cap3.toNat ≤ cap4.toNat →
      (bs3.length + (bytesFieldTagged 3#32 dk).length ≤ cap3.toNat → cap4 = cap3 ∧ ptr4 = ptr3) →
      SepWPp prog ret sm
        ((vecU8At A msgA dkCap dkPtr dk ∗
          vecU8At A v cap4 ptr4 (bs3 ++ bytesFieldTagged 3#32 dk) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep184 := step_ek_dk_from_184_1_placed hres A hfn henc hdoReserve hmemcpy
  ek_enc1_fetches_range_placed hfn 156 184
  ek_enc1_fetches_range_placed hfn 440 460
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA) (cap := dkCap) (ptr := dkPtr) (bs := dk)
    (F := vecU8At A v cap3 ptr3 bs3 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by ac_rfl) fun hdk_le hdk_cap_lt _ => ?_
  have ⟨hdk_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := dk) (by omega)
  cases hdk : dk.isEmpty
  · have hdk_len := bytesField3_len_of_ne_empty hdk
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap3) (ptr := ptr3) (bs := bs3)
      (F := vecU8At A msgA dkCap dkPtr dk ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap3_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs3, vecHeader,
      vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]
    by_cases hcap3 : cap3 == BitVec.ofNat 64 bs3.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap3.toNat = bs3.length :=
        CryptoVerification.SpqrV1.Auth.cap_toNat_eq_of_beq hcap3 (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      have hfit2 : bs3.length + (bytesFieldTagged 3#32 dk).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := CryptoVerification.SpqrV1.Auth.reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap3 ptr3 sp
        (fnBase + 452#64) bs3 1 hbound1 (F := vecU8At A msgA dkCap dkPtr dk ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap3.toNat bs3.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs3, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 184#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep184 msgA v newCap1 newPtr1 dkCap dkPtr sp bs3 dk hdk hlt1 (Or.inr hfit2) (F := F)
        an an an halign an an an
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm hge2 _ =>
          hnext sm cap4 ptr4 hpcm hrunm hspm htrm hx19m hx20m hcsm
            (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap3_f : (cap3 == BitVec.ofNat 64 bs3.length) = false := Bool.eq_false_iff.mpr hcap3
      have hlt3 : bs3.length < cap3.toNat :=
        CryptoVerification.SpqrV1.Auth.lt_cap_toNat_of_beq_false hcap3_f hcap3_le (Nat.lt_of_le_of_lt hcap3_le (BitVec.isLt cap3))
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 184#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep184 msgA v cap3 ptr3 dkCap dkPtr sp bs3 dk hdk hlt3 hfit (F := F)
        an an an halign an an an an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · rw [vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 264#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre
      (by rw [← bs_append_bytesFieldTagged_of_empty 3#32 hdk bs3,
        vecU8At_eq_header_sep_buf A msgA dkCap dkPtr dk, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap3 ptr3 an an an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## 5. Stage 5: Field 4 — `ct1: Vec<u8>` -/

private theorem step_ek_ct1_from_344_1_placed
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs_mid ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hle : bs_mid.length + ct1.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr bs_mid) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ vecU8At A v curCap curPtr (bs_mid ++ ct1)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 344 372
  examples_hide_fetches; subst hP
  have hct1_ne_nil : ct1 ≠ [] := List.isEmpty_eq_false_iff.mp hct1_ne
  have hct1_pos : 0 < ct1.length := List.length_pos_of_ne_nil hct1_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs_mid)
    (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v curCap curPtr bs_mid ∗ F) (by ac_rfl) fun hct1_le _ _ => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs_mid ct1.length hle hcap_lt hptr_ne hct1_pos,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps; apply SepWP.done an an; intro hinv1
  refine step_unchunked_memcpy_call_placed hmemcpy
    (curPtr + BitVec.ofNat 64 bs_mid.length) ct1Ptr sp (fnBase + 364#64) ct1
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs_mid.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs_mid) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs_mid.length + BitVec.ofNat 64 ct1.length)
        (curCap.toNat - bs_mid.length - ct1.length) ∗
      (vecHeader (msgA + 0x18#64) ct1Cap ct1Ptr (BitVec.ofNat 64 ct1.length) ∗
        ⌜ct1Ptr ≠ 0 ∧ ct1.length ≤ ct1Cap.toNat ∧ ct1Cap.toNat < 2 ^ 63⌝ ∗
        memRegion (ct1Ptr + BitVec.ofNat 64 ct1.length) (ct1Cap.toNat - ct1.length) ∗
        A.live ct1Ptr ct1Cap.toNat 1) ∗ F)
    an an an halign an an an an
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (cs_step hcs hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs_mid.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 372#64); wp_steps; apply SepWP.done an an; intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ an an an an (cs_step hcs1 hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs_mid ct1 hle hcap_lt hptr_ne hct1_ne_nil,
    vecU8At_expose_src_of_ne_nil_placed A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 hct1_ne_nil hct1_le]
  exact Entails.of_eq (by ac_rfl)

private theorem step_ek_ct1_from_292_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v curCap curPtr ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8))
    (hct1_ne : ct1.isEmpty = false) (hlt : bs4.length < curCap.toNat)
    (hfit : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = ct1Ptr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ct1.length)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A v curCap curPtr bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat → cap5 = curCap ∧ ptr5 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 ct1) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep344 := step_ek_ct1_from_344_1_placed A hfn hmemcpy
  ek_enc1_fetches_range_placed hfn 292 344; ek_enc1_fetches_range_placed hfn 540 576; examples_hide_fetches; subst hP
  have hct1_len := bytesField4_len_of_ne_empty hct1_ne
  rw [vecU8At_open_one A v curCap curPtr bs4 hlt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun oldByte => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps; apply SepWP.done an an; intro hinv1
  have hvarint_fit : (bs4 ++ [0x22#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 ct1.length)).length ≤ curCap.toNat ∨
      (bs4 ++ [0x22#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_unchunked_encode_varint_call_placed hres A henc (BitVec.ofNat 64 ct1.length) v curCap curPtr sp (fnBase + 324#64)
    (bs4 ++ [0x22#8]) hvarint_fit (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
    an an an halign an an an an (cs_step hcs hinv1) (by rw [← vecU8At_close_one A v curCap curPtr bs4 0x22#8 hlt]; ac_rfl) ?_
  intro s2 cap_mid ptr_mid hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge_mid hpres_mid
  let bs_mid := (bs4 ++ [0x22#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 ct1.length)
  have hbs_mid_len : bs_mid.length + ct1.length = bs4.length + (bytesFieldTagged 4#32 ct1).length := by
    dsimp [bs_mid]; rw [List.length_append, List.length_append, List.length_singleton, hct1_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = ct1Ptr := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap_mid) (ptr := ptr_mid) (bs := bs_mid)
    (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
    (by dsimp [bs_mid]; ac_rfl) fun hle_mid hcap_mid_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap_mid ptr_mid bs_mid, vecHeader]
  have hct1_lt63 : ct1.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap_mid.toNat < bs_mid.length + ct1.length
  · have hfit_ct1 : bs_mid.length + ct1.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = true :=
      (elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mpr hneed
    obtain ⟨hnot_ult, hle_res, hge_res, hbound_ct1⟩ := elem_len_after_reserve_not_ult hfit_ct1 hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv2
    refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap_mid ptr_mid sp
      (fnBase + 556#64) bs_mid ct1.length hbound_ct1 (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F) an an an halign an an an
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr_res hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap_res := BitVec.ofNat 64 (reserveCap cap_mid.toNat bs_mid.length ct1.length)
    change (BitVec.ofNat 64 ct1.length).ule (cap_res - BitVec.ofNat 64 bs_mid.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = ct1Ptr := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = BitVec.ofNat 64 ct1.length := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap_res ptr_res bs_mid, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 344#64); wp_steps; apply SepWP.done an an; intro hinv3
    exact hstep344 msgA v cap_res ptr_res ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_res
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an (cs_step hcs3 hinv3) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField4_of_ne_empty hct1_ne bs4]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_res ptr_res hpcm hrunm hspm htrm hcsm (Nat.le_trans hge_mid hge_res) (fun h => absurd h (by omega))))
  · have hle_fast : bs_mid.length + ct1.length ≤ cap_mid.toNat := by omega
    have hhi : (cap_mid - BitVec.ofNat 64 bs_mid.length).ult (BitVec.ofNat 64 ct1.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle_mid hcap_mid_lt hct1_lt63).mp h)
    have hpres_all : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ curCap.toNat → cap_mid = curCap ∧ ptr_mid = curPtr := by
      intro hfit_cap; apply hpres_mid; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 344#64); wp_steps; apply SepWP.done an an; intro hinv2
    exact hstep344 msgA v cap_mid ptr_mid ct1Cap ct1Ptr sp bs_mid ct1 hct1_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      an an an halign an an an an an (cs_step hcs2 hinv2) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre (by dsimp [bs_mid]; rw [bs_append_bytesField4_of_ne_empty hct1_ne bs4]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap_mid ptr_mid hpcm hrunm hspm htrm hcsm hge_mid hpres_all))

theorem step_ek_ct1_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64} (A : RustAlloc)
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (msgA v cap4 ptr4 ct1Cap ct1Ptr sp : BitVec 64) (bs4 ct1 : List (BitVec 8))
    (hfit : bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 264#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = msgA)
    (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
      vecU8At A v cap4 ptr4 bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = fnBase + 372#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      UnchunkedEncodeCalleeSavedPlaced s0 sm → cap4.toNat ≤ cap5.toNat →
      (bs4.length + (bytesFieldTagged 4#32 ct1).length ≤ cap4.toNat → cap5 = cap4 ∧ ptr5 = ptr4) →
      SepWPp prog ret sm
        ((vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗
          vecU8At A v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 ct1) ∗
          A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  have hstep292 := step_ek_ct1_from_292_1_placed hres A hfn henc hdoReserve hmemcpy
  ek_enc1_fetches_range_placed hfn 264 292
  ek_enc1_fetches_range_placed hfn 520 540
  examples_hide_fetches; subst hP
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := msgA + 0x18#64) (cap := ct1Cap) (ptr := ct1Ptr) (bs := ct1)
    (F := vecU8At A v cap4 ptr4 bs4 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
    (by ac_rfl) fun hct1_le hct1_cap_lt _ => ?_
  have ⟨hct1_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := ct1) (by omega)
  cases hct1 : ct1.isEmpty
  · have hct1_len := bytesField4_len_of_ne_empty hct1
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap4) (ptr := ptr4) (bs := bs4)
      (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ A.pool ∗ stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗ F)
      (by ac_rfl) fun hcap4_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap4 ptr4 bs4, vecHeader,
      vecU8At_eq_header_sep_buf A (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]
    by_cases hcap4 : cap4 == BitVec.ofNat 64 bs4.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps; apply SepWP.done an an; intro hinv0
      have hcap_eq : cap4.toNat = bs4.length :=
        CryptoVerification.SpqrV1.Auth.cap_toNat_eq_of_beq hcap4 (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      have hfit2 : bs4.length + (bytesFieldTagged 4#32 ct1).length + 10 < 2 ^ 62 := by
        rcases hfit with h | h <;> omega
      obtain ⟨hbound1, hlt1, hge1⟩ := CryptoVerification.SpqrV1.Auth.reserveCap_one_bounds hcap_eq (by omega)
      refine step_unchunked_do_reserve2_call_placed hres A hdoReserve v cap4 ptr4 sp
        (fnBase + 532#64) bs4 1 hbound1 (F := vecU8At A (msgA + 0x18#64) ct1Cap ct1Ptr ct1 ∗ F)
        an an an halign an an an (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap4.toNat bs4.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs4, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 292#64); wp_steps; apply SepWP.done an an; intro hinv1
      exact hstep292 msgA v newCap1 newPtr1 ct1Cap ct1Ptr sp bs4 ct1 hct1 hlt1 (Or.inr hfit2) (F := F)
        an an an halign an an an
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (cs_step hcs1 hinv1) (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap5 ptr5 hpcm hrunm hspm htrm hcsm hge2 _ =>
          hnext sm cap5 ptr5 hpcm hrunm hspm htrm hcsm
            (Nat.le_trans hge1 hge2) (fun h => absurd h (by omega)))
    · have hcap4_f : (cap4 == BitVec.ofNat 64 bs4.length) = false := Bool.eq_false_iff.mpr hcap4
      have hlt4 : bs4.length < cap4.toNat :=
        CryptoVerification.SpqrV1.Auth.lt_cap_toNat_of_beq_false hcap4_f hcap4_le (Nat.lt_of_le_of_lt hcap4_le (BitVec.isLt cap4))
      apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 292#64); wp_steps; apply SepWP.done an an; intro hinv0
      exact hstep292 msgA v cap4 ptr4 ct1Cap ct1Ptr sp bs4 ct1 hct1 hlt4 hfit (F := F)
        an an an halign an an an an an (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · rw [vecU8At_eq_header_sep_buf A (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := fnBase + 372#64); wp_steps; apply SepWP.done an an; intro hinv0
    refine SepWPp.weaken_pre
      (by rw [← bs_append_bytesFieldTagged_of_empty 4#32 hct1 bs4,
        vecU8At_eq_header_sep_buf A (msgA + 0x18#64) ct1Cap ct1Ptr ct1, vecHeader]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap4 ptr4 an an an an (cs_step hcs hinv0) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## 6. Epilogue & Top-Level `subroutine_ok` for `encode<EkSentCt1Received> [local#1]` -/

theorem step_ek_epilogue_1_placed {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (sp sv3 : BitVec 64) {s0 s : State} {R : SepProp}
    {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = fnBase + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : UnchunkedEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (authEncodeStackOf resStack) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((sp - 40#64) ↦₆₄ sv3) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace → CalleeSavedPreserved s0 sf → StepInv s0 sf →
      Q sf (stackAt sp (unchunkedMsgEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncodeOnPanic s0 sf ∗ R)) := by
  ek_enc1_fetches_range_placed hfn 372 392; examples_hide_fetches; subst hP
  have hsp_aligned := sp_sub_64_aligned halign
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); wp_steps; apply SepWP.done an an; intro hinv
  have hcs' := cs_step hcs hinv
  refine SepWPp.weaken_pre ?_ (SepWPp.done an an (hnext _ an an an an
    ⟨an, an, an, an, an, hcs'.1, hcs'.2.1, hcs'.2.2.1, hcs'.2.2.2.1, hcs'.2.2.2.2.1, an, hcs'.2.2.2.2.2.1⟩ hcs'.2.2.2.2.2.2.1))
  rw [stackAt_unchunkedMsgEncode hres sp]; refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp) (Entails.sepExists_right (s0.readReg64 .lr)
    (Entails.sepExists_right (s0.readReg64 .x23) (Entails.sepExists_right sv3
      (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
        (Entails.sepExists_right (s0.readReg64 .x20) (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))

theorem ekSentCt1ReceivedEncode1_gen_ok_prog {resStack : Nat} (hres : resStack + 48 + 128 < 2 ^ 64)
    {prog : Program} {fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc : BitVec 64}
    {A : RustAlloc} {x : EkSentCt1ReceivedEncodePinnedGhost} {R : SepProp} {s0 : State}
    (hfn : IsEkEnc1PlacedProg prog fnBase encLen_pc varint_pc auth_pc reserve_pc memcpy_pc)
    (hencLen : subroutine_ok prog encLen_pc (withUnchunkedEncodeCSPlaced s0 (ekSentCt1ReceivedEncodedLenPinnedSpec A)))
    (henc : subroutine_ok prog varint_pc (withUnchunkedEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hauth : subroutine_ok prog auth_pc (withUnchunkedEncodeCSPlaced s0 (authEncodePinnedSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withUnchunkedEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (hpc : s0.pc = fnBase) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp prog (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre; dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hcap_le, hcap_lt, _⟩ :=
    vecU8At_bounds_of_satisfies (A := A) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗ A.pool ∗
        stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)) ∗ emp) ∗ R := by
    rw [sepConj_emp]; convert hpre_mem using 1
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeEkSentCt1ReceivedMsg_len_split x.m
  have hhdr_bds := msgHeaderBytes_len_bounds (ekSentCt1ReceivedPBEncodedLen x.m)
  have hlen_eq_fields := ekSentCt1ReceivedPBEncodedLen_eq_fields_len x.m
  have hlen_fit : ekSentCt1ReceivedPBEncodedLen x.m < 2 ^ 64 := by rcases hfit with h | h <;> omega
  have hfit_hdr : x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length ≤ x.cap.toNat ∨
      x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_hdr_1_placed hres A hfn hencLen henc hdoReserve x.g x.msgA x.v x.cap x.ptr s0.sp x.bs x.m
    hcap_le hlen_fit hfit_hdr (F := emp) hpc hrun rfl halign rfl hx0 hx1
    (UnchunkedEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 sv3 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hge1 hpres1
  let bs1 := x.bs ++ msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)
  let S := ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ sv3) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hbs1_len : bs1.length = x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length :=
    List.length_append
  have hfit_ep : bs1.length + (u64Field1Bytes x.m.epoch).length ≤ cap1.toNat ∨
      bs1.length + (u64Field1Bytes x.m.epoch).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_epoch_1_placed hres A hfn henc hdoReserve x.msgA x.v cap1 ptr1 x.m.epoch s0.sp bs1
    hfit_ep hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗
      optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x30#64) x.m.auth ∗ S ∗ emp)
    (by dsimp [bs1, S, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2
  let bs2 := bs1 ++ u64Field1Bytes x.m.epoch
  have hbs2_len : bs2.length = bs1.length + (u64Field1Bytes x.m.epoch).length := List.length_append
  have hfit_auth : bs2.length + (optAuthField2Bytes x.m.auth).length ≤ cap2.toNat ∨
      bs2.length + (optAuthField2Bytes x.m.auth).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_auth_1_placed A hfn hauth x.g.auth x.msgA x.v cap2 ptr2 s0.sp bs2 x.m.auth
    hfit_auth hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗ vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs2]; ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 hge3 hpres3
  let bs3 := bs2 ++ optAuthField2Bytes x.m.auth
  have hbs3_len : bs3.length = bs2.length + (optAuthField2Bytes x.m.auth).length := List.length_append
  have hfit_dk : bs3.length + (bytesFieldTagged 3#32 x.m.dk).length ≤ cap3.toNat ∨
      bs3.length + (bytesFieldTagged 3#32 x.m.dk).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_dk_1_placed hres A hfn henc hdoReserve hmemcpy
    x.msgA x.v cap3 ptr3 x.g.f3.cap x.g.f3.ptr s0.sp bs3 x.m.dk
    hfit_dk hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hcs3
    (F := optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x30#64) x.m.auth ∗
      ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗
      vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗ S ∗ emp)
    (by dsimp [bs3]; ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hge4 hpres4
  let bs4 := bs3 ++ bytesFieldTagged 3#32 x.m.dk
  have hbs4_len : bs4.length = bs3.length + (bytesFieldTagged 3#32 x.m.dk).length := List.length_append
  have hfit_ct1 : bs4.length + (bytesFieldTagged 4#32 x.m.ct1).length ≤ cap4.toNat ∨
      bs4.length + (bytesFieldTagged 4#32 x.m.ct1).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ek_ct1_1_placed hres A hfn henc hdoReserve hmemcpy
    x.msgA x.v cap4 ptr4 x.g.f4.cap x.g.f4.ptr s0.sp bs4 x.m.ct1 hfit_ct1 hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hcs4
    (F := vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x30#64) x.m.auth ∗ ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗ S ∗ emp)
    (by dsimp [bs4]; ac_rfl) ?_
  intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hcs5 hge5 hpres5
  refine step_ek_epilogue_1_placed hres hfn s0.sp sv3
    (F := vecU8At A (x.msgA + 0x18#64) x.g.f4.cap x.g.f4.ptr x.m.ct1 ∗
      vecU8At A x.v cap5 ptr5 (bs4 ++ bytesFieldTagged 4#32 x.m.ct1) ∗ A.pool ∗ vecU8At A x.msgA x.g.f3.cap x.g.f3.ptr x.m.dk ∗
      optAuthenticatorPBPinnedAt A x.g.auth (x.msgA + 0x30#64) x.m.auth ∗ ((x.msgA + 0x60#64) ↦₆₄ x.m.epoch) ∗ emp)
    hpc5 hrun5 hsp5 halign htr5 hcs5 (by dsimp [S]; ac_rfl) ?_
  intro sf _ _ hspf htrf hcc _; refine ⟨fun hm => ?_, hspf, hcc⟩
  have hge_all : x.cap.toNat ≤ cap5.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 (Nat.le_trans hge4 hge5)))
  have hpres_all : x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat → cap5 = x.cap ∧ ptr5 = x.ptr := by
    intro hfit_cap
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega); obtain ⟨hc2, hp2⟩ := hpres2 (by omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by omega); obtain ⟨hc4, hp4⟩ := hpres4 (by omega)
    obtain ⟨hc5, hp5⟩ := hpres5 (by omega)
    exact ⟨hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))), hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))⟩
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]; refine ⟨cap5, ptr5, ?_⟩
  have hpure : (x.cap.toNat ≤ cap5.toNat ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat → cap5 = x.cap ∧ ptr5 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  rw [hpure, pure_true, emp_sepConj, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt, ← bs0_append_encodeEkSentCt1ReceivedMsg x.bs x.m]
  dsimp only [bs4, bs3, bs2, bs1] at hm; rw [sepConj_emp] at hm; convert hm using 1; ac_rfl

private theorem ekSentCt1ReceivedEncode_post_unpinned_of_pinned_placed {resStack : Nat} {A : RustAlloc}
    {x : EkSentCt1ReceivedEncodeGhost} {g : Unchunked4PBGhost} {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (ekSentCt1ReceivedEncodePinnedSpecOf resStack A).post
      ⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s0 sf ∗ R) :
    sf.mem ⊨ (ekSentCt1ReceivedEncodeSpecOf resStack A).post x s0 sf ∗ R := by
  dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf] at hq
  dsimp only [ekSentCt1ReceivedEncodeSpecOf]
  let Rest : SepProp := ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
    A.pool ∗ stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R
  have hq' : sf.mem ⊨ ekSentCt1ReceivedPBPinnedAt A g x.msgA x.m ∗ Rest := by convert hq using 1; dsimp only [Rest]; ac_rfl
  have hgoal : sf.mem ⊨ ekSentCt1ReceivedPBAt A x.msgA x.m ∗ Rest := by
    rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]; exact ⟨g, hq'⟩
  convert hgoal using 1; dsimp only [Rest]; ac_rfl

theorem ekSentCt1ReceivedEncode_unpinned_of_pinned_placed [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {fnBase : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog fnBase (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog fnBase (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  dsimp only [ekSentCt1ReceivedEncodeSpecOf] at hpre; rw [ekSentCt1ReceivedPBAt, unchunked4At_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre; rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecOf resStack A)).pre
      ⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; exact ⟨hcl0, hpre⟩
  refine hpinned.mono_outcome ⟨x.msgA, g, x.m, x.v, x.cap, x.ptr, x.bs⟩ R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, ekSentCt1ReceivedEncode_post_unpinned_of_pinned_placed hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem ek_sent_ct1_received_encode_1_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_155 H) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn1 : IsEkEnc1PlacedProg (lsProg_155 H) (blkPl_155).base (blkPl_192).base (blkPl_148).base (lsmpl.base 151) (blkPl_157).base (lsρ lsMemcpySym) :=
    ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_192 H) (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
    subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
      (unchunked82_entry_pinned_ok (lsProg_192 H) A (blkPl_192).base
        (Or.inr ⟨‹_›, H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).mono_outcome
        (spec₂ := ekSentCt1ReceivedEncodedLenPinnedSpec A) (y := x) (R₂ := R)
        ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ R s0 hpc hrun hpre hsp (fun _ h => h)
  have hauth0 : subroutine_ok (lsProg_155 H) (lsmpl.base 151) (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStack A)) :=
    ls_subroutine_ok_of_block (auth_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode1_gen_ok_prog (by decide) hfn1
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ek_sent_ct1_received_encode_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_155 H) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpec A)) :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem ek_sent_ct1_received_encode_1_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_155 H) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodePinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn1 : IsEkEnc1PlacedProg (lsProg_155 H) (blkPl_155).base (blkPl_192).base (blkPl_148).base (lsmpl.base 151) (blkPl_157).base (lsρ lsMemcpySym) :=
    ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hencLen0 : subroutine_ok (lsProg_192 H) (blkPl_192).base (ekSentCt1ReceivedEncodedLenPinnedSpec A) :=
    subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
      (unchunked82_entry_pinned_ok (lsProg_192 H) A (blkPl_192).base
        (Or.inr ⟨‹_›, H, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)).mono_outcome
        (spec₂ := ekSentCt1ReceivedEncodedLenPinnedSpec A) (y := x) (R₂ := R)
        ⟨x.a, x.g, x.m.epoch, x.m.auth, x.m.dk, x.m.ct1⟩ R s0 hpc hrun hpre hsp (fun _ h => h)
  have hauth0 : subroutine_ok (lsProg_155 H) (lsmpl.base 151) (withLsCodeLoaded lsmpl (authEncodePinnedSpecOf doReserveStackX A)) :=
    ls_subroutine_ok_of_block (auth_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode1_gen_ok_prog (by decide) hfn1
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (subroutine_ok_withLsCodeLoaded_unchunked hencLen0))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed s0 hcl0 hauth0)
    (subroutine_ok_withUnchunkedEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem ek_sent_ct1_received_encode_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec) (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A)) (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_155 H) (blkPl_155).base (withLsCodeLoaded lsmpl (ekSentCt1ReceivedEncodeSpecX A)) :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end CryptoVerification.SpqrV1.Prost.MessageEncode
