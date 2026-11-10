/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.Encode1
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import ProofLib.SepLogic.WPp

/-!
# `prost::encoding::message::encode::<EpochDirection, Vec<u8>> [local#1]`

Verification of the first monomorphization
`prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]`
(`169` instructions, `676` bytes, calling `encode_varint [local#2]` and
`do_reserve_and_handle [local#2]`).
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
  (ofNat_length_beq_zero_of_lt bv_bytesField_nonempty adds_no_overflow_of_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.literalFetch false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega

def dummyAuthGhost : AuthEncodePinnedGhost := ⟨0, ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨[], []⟩, 0, 0, 0, []⟩

def IsEd1EntryProg (prog : Program) (entry varint_pc reserve_pc memcpy_pc : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧
    entry = (tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name ∧
    varint_pc = entry + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]") ∧
    reserve_pc = entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]") ∧
    memcpy_pc = entry + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy")) ∨
  (∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_154 H ∧ entry = (blkPl_154).base ∧
    varint_pc = (blkPl_148).base ∧ reserve_pc = (blkPl_157).base ∧ memcpy_pc = lsρ lsMemcpySym)

theorem isEpochDirectionEncodeEntryProg_of_ed1 {prog : Program}
    {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (h : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) :
    IsEpochDirectionEncodeEntryProg prog entry := by
  rcases h with ⟨b, ext, rfl, rfl, -, -, -⟩ | ⟨_, H, rfl, rfl, -, -, -⟩
  · exact Or.inl ⟨b, ext, rfl, Or.inl rfl⟩
  · exact Or.inr (Or.inl ⟨‹_›, H, rfl, rfl⟩)

theorem ed1_fetch_add {prog : Program} {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    {k : Nat} {instr : Instr} (hfn : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) = some instr)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_154 H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) = some instr) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some instr := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, -⟩ | ⟨_, H, rfl, rfl, -, -, -⟩; exact hext b ext; exact hpl H

theorem ed1_fetch_bl_varint {prog : Program} {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    {k : Nat} {off : BitVec 64} (hfn : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_154 H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_154).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" -
          (blkPl_154).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (varint_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, rfl, -, -⟩ | ⟨inst, H, rfl, rfl, rfl, -, -⟩
  · have hf := hext b ext
    have heq : off = ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]")) -
        ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) := by rw [hoff]; bv_omega
    rwa [heq] at hf
  · letI := inst
    have h := @hpl inst H
    simp only [blkPl_154_ρ, ls_resolve_blk_148] at h
    have heq : lsmpl.base 148 - (blkPl_154).base - BitVec.ofNat 64 k =
        (blkPl_148).base - ((blkPl_154).base + BitVec.ofNat 64 k) := by
      change (blkPl_148).base - (blkPl_154).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

theorem ed1_fetch_bl_reserve {prog : Program} {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    {k : Nat} {off : BitVec 64} (hfn : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_154 H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_154).ρ "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]" -
          (blkPl_154).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (reserve_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, rfl, -⟩ | ⟨inst, H, rfl, rfl, -, rfl, -⟩
  · have hf := hext b ext
    have heq : off = ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]")) -
        ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) := by rw [hoff]; bv_omega
    rwa [heq] at hf
  · letI := inst
    have h := @hpl inst H
    simp only [blkPl_154_ρ, ls_resolve_blk_157] at h
    have heq : lsmpl.base 157 - (blkPl_154).base - BitVec.ofNat 64 k =
        (blkPl_157).base - ((blkPl_154).base + BitVec.ofNat 64 k) := by
      change (blkPl_157).base - (blkPl_154).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

theorem ed1_fetch_bl_memcpy {prog : Program} {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    {k : Nat} {off : BitVec 64} (hfn : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hext : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) = some (Instr.bl off))
    (hoff : off = bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy") - BitVec.ofNat 64 k)
    (hpl : ∀ [LibsignalPlacement] (H : String → Option (State → State)),
      (lsProg_154 H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_154).ρ "memcpy" - (blkPl_154).base - BitVec.ofNat 64 k))) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some (Instr.bl (memcpy_pc - (entry + BitVec.ofNat 64 k))) := by
  rcases hfn with ⟨b, ext, rfl, rfl, -, -, rfl⟩ | ⟨inst, H, rfl, rfl, -, -, rfl⟩
  · have hf := hext b ext
    have heq : off = ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name +
        bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy")) -
        ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) := by rw [hoff]; bv_omega
    rwa [heq] at hf
  · letI := inst
    have h := @hpl inst H
    have heq : (blkPl_154).ρ "memcpy" - (blkPl_154).base - BitVec.ofNat 64 k =
        lsρ lsMemcpySym - ((blkPl_154).base + BitVec.ofNat 64 k) := by
      change lsρ lsMemcpySym - (blkPl_154).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

open Lean Meta Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` for `encode<EpochDirection> [local#1]` on arbitrary `prog`. -/
elab "ed1_fetches_prog " hfn:term:max kStart:num kEnd:num : tactic => do
  let off := 0x37850
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37850
  let ed1Add := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ed1_fetch_add
  let fetchBlVarint := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ed1_fetch_bl_varint
  let fetchBlReserve := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ed1_fetch_bl_reserve
  let fetchBlMemcpy := mkIdent `CryptoVerification.SpqrV1.Prost.MessageEncode.ed1_fetch_bl_memcpy
  for i in [kStart.getNat / 4 : kEnd.getNat / 4] do
    let k := 4 * i
    let dec := mkIdent (Name.str `CryptoVerification.SpqrV1.Prost.MessageEncode
      ("libsignalSessionBin_decode_" ++ "0x" ++ String.ofList (Nat.toDigits 16 (off + k))))
    let kHex := String.ofList (Nat.toDigits 16 k)
    let lsFetch := mkIdent (`CryptoVerification |>.str s!"blkPC_154_rebase_fetch_0x{kHex}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 40 || k == 168 || k == 220 || k == 276 || k == 380 then
      evalTactic (← `(tactic|
        have := $fetchBlVarint (k := $kq) $hfn
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 504 || k == 524 || k == 548 || k == 604 || k == 628 then
      evalTactic (← `(tactic|
        have := $fetchBlReserve (k := $kq) $hfn
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else if k == 316 || k == 420 then
      evalTactic (← `(tactic|
        have := $fetchBlMemcpy (k := $kq) $hfn
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (by decide) (fun [LibsignalPlacement] H => $lsFetch _ H)))
    else
      evalTactic (← `(tactic|
        have := $ed1Add (k := $kq) $hfn
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff (by decide) $dec)
          (fun [LibsignalPlacement] H => $lsFetch _ H)))

/-! ## 1. `encode<EpochDirection> [local#1]` Step Lemmas -/

/-- Step 1 for `encode<EpochDirection> [local#1]` (`+0 .. +172`). -/
theorem step_hdr_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (tag : BitVec 32) (v cap0 ptr0 dirA nextPtr prevPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63) (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    (hfit : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat ∨
      bs0.length + (epochDirectionHeaderBytes tag d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt sp (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = entry + 172#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 → AuthEncodeCalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0) →
      SepWPp prog ret sm
        ((vecU8At A v cap1 ptr1 (bs0 ++ epochDirectionHeaderBytes tag d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn_ed := isEpochDirectionEncodeEntryProg_of_ed1 hfn1
  ed1_fetches_prog hfn1 40 44; ed1_fetches_prog hfn1 168 172; examples_hide_fetches
  have hhdr_bds := epochDirectionHeaderBytes_len_bounds tag d
  let S := epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine step_epochDir_prologue_placed hres hfn_ed tag dirA v sp
    (F := vecU8At A v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ F)
    hhs0 hpc hrun hsp halign htr hw0 hx1 hx2 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx21_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have htag_eq := encodeVarint_epochDirection_tag_eq_proto tag
  have hvarint1_fit : bs0.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint
        (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)).length ≤ cap0.toNat ∨
      bs0.length + 10 < 2 ^ 62 := by
    rw [htag_eq]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64)
    v cap0 ptr0 sp (entry + 44#64) bs0 hvarint1_fit (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by dsimp [S]; ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01
  rw [htag_eq] at hpres01
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine step_epochDir_len_placed hfn_ed v dirA nextPtr prevPtr sp d hnext_lt hprev_lt hlen_fit
    (F := vecU8At A v cap01 ptr01 (bs0 ++ Proto.encodeKey tag .lengthDelimited) ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ S ∗ F)
    hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hcs2 (by rw [htag_eq]; ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
  have hhdr_eq : (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))).length =
      bs0.length + (epochDirectionHeaderBytes tag d).length := by
    rw [List.length_append, hhdr_bds.1]; omega
  have hvarint2_fit : (bs0 ++ Proto.encodeKey tag .lengthDelimited).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))).length ≤ cap01.toNat ∨
      (bs0 ++ Proto.encodeKey tag .lengthDelimited).length + 10 < 2 ^ 62 := by
    rw [hhdr_eq, List.length_append]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc (BitVec.ofNat 64 (epochDirectionPBEncodedLen d))
    v cap01 ptr01 sp (entry + 172#64) (bs0 ++ Proto.encodeKey tag .lengthDelimited) hvarint2_fit
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3) (by ac_rfl) ?_
  intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1
  rw [hhdr_eq] at hpres1
  have hpres_all : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat → cap1 = cap0 ∧ ptr1 = ptr0 := by
    intro hle0; obtain ⟨hc01, hp01⟩ := hpres01 (by omega)
    obtain ⟨hc1, hp1⟩ := hpres1 (by rw [hc01]; exact hle0)
    exact ⟨hc1.trans hc01, hp1.trans hp01⟩
  refine SepWPp.weaken_pre
    (by dsimp [S]; rw [bs0_append_epochDirectionHeaderBytes bs0 tag d]; exact Entails.of_eq (by ac_rfl))
    (hnext s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 (by rw [hcs34.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.1]; simp only [arm64_norm, *]) (by rw [hcs34.2.2.1]; simp only [arm64_norm, *])
      (by rw [hcs34.2.2.2.1]; simp only [arm64_norm, *]) (by rw [hcs34.2.2.2.2.1]; simp only [arm64_norm, *])
      hcs4 (Nat.le_trans hge01 hge1) hpres_all)

private theorem step_ctr_from_192_1 {resStack : Nat}
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (v curCap curPtr dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hctr_ne : (d.ctr == 0#32) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 224#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn_ed := isEpochDirectionEncodeEntryProg_of_ed1 hfn1
  ed1_fetches_prog hfn1 220 224; examples_hide_fetches
  obtain ⟨hctr_len, _⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr_ne
  refine step_epochDir_push_ctr_tag_placed A hfn_ed v curCap curPtr dirA sp bs1 d hlt
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hctr_eq : (bs1 ++ [0x08#8]).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64)).length =
      bs1.length + (epochDirectionCtrBytes d).length := by
    rw [List.length_append, List.length_singleton, hctr_len]; omega
  have hvarint_fit : (bs1 ++ [0x08#8]).length +
        (CryptoVerification.LibsignalProtoCodec.encodeVarint (d.ctr.zeroExtend 64)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
    rw [hctr_eq, List.length_append, List.length_singleton]
    rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (d.ctr.zeroExtend 64) v curCap curPtr sp (entry + 224#64) (bs1 ++ [0x08#8]) hvarint_fit (F := F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  rw [hctr_eq] at hpres2
  refine SepWPp.weaken_pre
    (by rw [bs_append_epochDirectionCtrBytes_of_ne_zero bs1 d hctr_ne]; exact Entails.of_eq (by ac_rfl))
    (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 (by rw [hcs12.1]; simp only [arm64_norm, *])
      (by rw [hcs12.2.1]; simp only [arm64_norm, *]) (by rw [hcs12.2.2.1]; simp only [arm64_norm, *])
      (by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]) hcs2 hge2 hpres2)

/-- Step 2 for `encode<EpochDirection> [local#1]` (`+172 .. +224`). -/
theorem step_ctr_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (v cap1 ptr1 dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 172#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 224#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp prog ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep192 := step_ctr_from_192_1 A hfn1 henc
  ed1_fetches_prog hfn1 172 192; ed1_fetches_prog hfn1 496 516; examples_hide_fetches; subst hP
  cases hctr : (d.ctr == 0#32)
  · obtain ⟨hctr_len, hctr_ge2⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F) (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap1.toNat = bs1.length := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
      have hfit2 : bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap1 ptr1 sp (entry + 508#64) bs1 1 hbound1 (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 192#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep192 v newCap1 newPtr1 dirA sp bs1 d hctr (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm hge2 _ =>
          hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm
            (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat := lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 192#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep192 v cap1 ptr1 dirA sp bs1 d hctr hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs_placed (mid := entry + 224#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionCtrBytes_of_zero bs1 d hctr]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_next_from_300_1
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_ne : d.next.isEmpty = false) (hle : bs2.length + d.next.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 300#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = nextPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ d.next) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed1_fetches_prog hfn1 300 328; examples_hide_fetches; subst hP
  have hnext_ne_nil : d.next ≠ [] := List.isEmpty_eq_false_iff.mp hnext_ne
  have hnext_pos : 0 < d.next.length := List.length_pos_of_ne_nil hnext_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 d.next.length hle hcap_lt hptr_ne hnext_pos, epochDirectionElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_ed_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs2.length) nextPtr sp (entry + 320#64) d.next
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.next.length) (curCap.toNat - bs2.length - d.next.length) ∗
      ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      ((dirA + 32#64) ↦₆₄ prevPtr) ∗ ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
      (prevPtr ↦ₛ d.prev) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx21_1 : s1.readReg64 .x21 = dirA := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 328#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 d.next hle hcap_lt hptr_ne hnext_ne_nil, epochDirectionElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_next_from_248_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hnext_ne : d.next.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 248#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = nextPtr)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep300 := step_next_from_300_1 A hfn1 hmemcpy
  have hfn_ed := isEpochDirectionEncodeEntryProg_of_ed1 hfn1
  ed1_fetches_prog hfn1 276 300; ed1_fetches_prog hfn1 536 572; examples_hide_fetches
  have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hnext_ne
  refine step_epochDir_push_next_tag_placed A hfn_ed v curCap curPtr dirA nextPtr sp bs1 d hlt
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hvarint_fit : (bs1 ++ [0x12#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.next.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (BitVec.ofNat 64 d.next.length) v curCap curPtr sp (entry + 280#64) (bs1 ++ [0x12#8]) hvarint_fit
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x12#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.next.length)
  have hbs2_len : bs2.length + d.next.length = bs1.length + (epochDirectionNextBytes d).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hnext_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
  have hx23_2 : s2.readReg64 .x23 = nextPtr := by rw [hcs12.2.2.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hnext_lt63 : d.next.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + d.next.length
  · have hfit_next : bs2.length + d.next.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_next⟩ := elem_len_after_reserve_not_ult hfit_next hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
      (entry + 552#64) bs2 d.next.length hbound_next (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.next.length)
    change (BitVec.ofNat 64 d.next.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = dirA := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_3 : s3.readReg64 .x23 = nextPtr := by rw [hcs23.2.2.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 300#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    exact hstep300 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d hnext_ne hle3
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + d.next.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mp h)
    have hpres_all : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 300#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    exact hstep300 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hnext_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 hpres_all))

/-- Step 3 for `encode<EpochDirection> [local#1]` (`+224 .. +328`):
encodes field 2 (`next : Vec<u8>`, tag 2) if non-empty. -/
theorem step_next_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v cap1 ptr1 dirA nextPtr prevPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (d : EpochDirectionPB) (hnext_lt : d.next.length < 2 ^ 63)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 224#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = entry + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat → cap2 = cap1 ∧ ptr2 = ptr1) →
      SepWPp prog ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep248 := step_next_from_248_1 hres A hfn1 henc hdoReserve hmemcpy
  ed1_fetches_prog hfn1 224 248; ed1_fetches_prog hfn1 516 536; examples_hide_fetches; subst hP
  have ⟨hnext_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  cases hn : d.next.isEmpty
  · have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hn
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1, vecHeader, epochDirectionElemsAt]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap1.toNat = bs1.length := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
      have hfit2 : bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap1 ptr1 sp
        (entry + 528#64) bs1 1 hbound1 (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs1, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 248#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep248 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs1 d hn (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm hge2 _ =>
          hnext sm cap2 ptr2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
            (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat := lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 248#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep248 v cap1 ptr1 dirA nextPtr prevPtr sp bs1 d hn hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs_placed (mid := entry + 328#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionNextBytes_of_empty bs1 d hn]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

private theorem step_prev_from_404_1
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_ne : d.prev.isEmpty = false) (hle : bs2.length + d.prev.length ≤ curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 404#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = prevPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs2.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v curCap curPtr (bs2 ++ d.prev) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed1_fetches_prog hfn1 404 432; examples_hide_fetches; subst hP
  have hprev_ne_nil : d.prev ≠ [] := List.isEmpty_eq_false_iff.mp hprev_ne
  have hprev_pos : 0 < d.prev.length := List.length_pos_of_ne_nil hprev_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := curCap) (ptr := curPtr) (bs := bs2)
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F) (by ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A v curCap curPtr bs2 d.prev.length hle hcap_lt hptr_ne hprev_pos, epochDirectionElemsAt]
  apply SepWPp.of_sepWP_cs_placed (mid := memcpy_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine step_ed_memcpy_call_placed hmemcpy
    (curPtr + BitVec.ofNat 64 bs2.length) prevPtr sp (entry + 424#64) d.prev
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
      memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.prev.length)
        (curCap.toNat - bs2.length - d.prev.length) ∗
      ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      (nextPtr ↦ₛ d.next) ∗ ((dirA + 32#64) ↦₆₄ prevPtr) ∗
      ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
    (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
  have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
  have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs01.2.1]; simp only [arm64_norm, *]
  have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 bs2.length := by rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 432#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
  rw [← vecU8At_pack_slice A v curCap curPtr bs2 d.prev hle hcap_lt hptr_ne hprev_ne_nil, epochDirectionElemsAt]
  exact Entails.of_eq (by ac_rfl)

private theorem step_prev_from_352_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_ne : d.prev.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    {s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 352#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = prevPtr)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = entry + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap3.toNat →
      (bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat → cap3 = curCap ∧ ptr3 = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v cap3 ptr3 (bs1 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep404 := step_prev_from_404_1 A hfn1 hmemcpy
  have hfn_ed := isEpochDirectionEncodeEntryProg_of_ed1 hfn1
  ed1_fetches_prog hfn1 380 404; ed1_fetches_prog hfn1 616 652; examples_hide_fetches
  have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hprev_ne
  refine step_epochDir_push_prev_tag_placed A hfn_ed v curCap curPtr prevPtr sp bs1 d hlt
    (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hcs (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := varint_pc); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hvarint_fit : (bs1 ++ [0x1a#8]).length +
      (CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.prev.length)).length ≤ curCap.toNat ∨
      (bs1 ++ [0x1a#8]).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_singleton]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ed_encode_varint_call_placed A henc
    (BitVec.ofNat 64 d.prev.length) v curCap curPtr sp (entry + 384#64)
    (bs1 ++ [0x1a#8]) hvarint_fit (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1) (by ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2
  let bs2 := (bs1 ++ [0x1a#8]) ++ CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 d.prev.length)
  have hbs2_len : bs2.length + d.prev.length = bs1.length + (epochDirectionPrevBytes d).length := by
    dsimp [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hprev_len]; omega
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  have hx21_2 : s2.readReg64 .x21 = prevPtr := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (by dsimp [bs2]; ac_rfl) fun hle2 hcap2_lt _ => ?_
  rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader]
  have hprev_lt63 : d.prev.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
  by_cases hneed : cap2.toNat < bs2.length + d.prev.length
  · have hfit_prev : bs2.length + d.prev.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = true :=
      (elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mpr hneed
    obtain ⟨hnot_ult, hle3, hge3, hbound_prev⟩ := elem_len_after_reserve_not_ult hfit_prev hneed
    apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
      (entry + 632#64) bs2 d.prev.length hbound_prev (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl) ?_
    intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
    let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.prev.length)
    change (BitVec.ofNat 64 d.prev.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true at hnot_ult
    have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
    have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by rw [hcs23.2.1]; simp only [arm64_norm, *]
    have hx21_3 : s3.readReg64 .x21 = prevPtr := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
    rw [vecU8At_eq_header_sep_buf A v cap3 ptr3 bs2, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 404#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv3
    exact hstep404 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d hprev_ne hle3
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))))
  · have hle_fast : bs2.length + d.prev.length ≤ cap2.toNat := by omega
    have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.prev.length) = false :=
      Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hprev_lt63).mp h)
    have hpres_all : bs1.length + (epochDirectionPrevBytes d).length ≤ curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
      intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 404#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
    exact hstep404 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hprev_ne hle_fast
      (F := A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
      (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
      (fun sm hpcm hrunm hspm htrm hcsm =>
        SepWPp.weaken_pre
          (by dsimp [bs2]; rw [bs_append_epochDirectionPrevBytes_of_ne_empty bs1 d hprev_ne]; exact Entails.of_eq (by ac_rfl))
          (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hcsm hge2 hpres_all))

/-- Step 4 for `encode<EpochDirection> [local#1]` (`+328 .. +432`):
encodes field 3 (`prev : Vec<u8>`, tag 3) if non-empty. -/
theorem step_prev_1 {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc) {s0 s : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (v cap2 ptr2 dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8)) (d : EpochDirectionPB)
    (hprev_lt : d.prev.length < 2 ^ 63)
    (hfit : bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 328#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = entry + 432#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      AuthEncodeCalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (epochDirectionPrevBytes d).length ≤ cap2.toNat → cap3 = cap2 ∧ ptr3 = ptr2) →
      SepWPp prog ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ epochDirectionPrevBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hstep352 := step_prev_from_352_1 hres A hfn1 henc hdoReserve hmemcpy
  ed1_fetches_prog hfn1 328 352; ed1_fetches_prog hfn1 596 616; examples_hide_fetches; subst hP
  have ⟨hprev_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hp : d.prev.isEmpty
  · have hprev_len := epochDirectionPrevBytes_len_of_ne_empty d hp
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by ac_rfl) fun hcap2_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A v cap2 ptr2 bs2, vecHeader, epochDirectionElemsAt]
    by_cases hcap2 : cap2 == BitVec.ofNat 64 bs2.length
    · apply SepWPp.of_sepWP_cs_placed (mid := reserve_pc); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      have hcap_eq : cap2.toNat = bs2.length := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap2_le (BitVec.isLt cap2)) hcap2
      have hfit2 : bs2.length + (epochDirectionPrevBytes d).length + 10 < 2 ^ 62 := by rcases hfit with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq (by omega)
      refine step_ed_do_reserve2_call_placed hres A hdoReserve v cap2 ptr2 sp
        (entry + 608#64) bs2 1 hbound1 (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A v newCap1 newPtr1 bs2, vecHeader]
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 352#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
      exact hstep352 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs2 d hp (by dsimp [newCap1]; omega) (Or.inr hfit2) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
        (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try ac_rfl)
        (fun sm cap3 ptr3 hpcm hrunm hspm htrm hcsm hge2 _ =>
          hnext sm cap3 ptr3 hpcm hrunm hspm htrm hcsm (Nat.le_trans (by dsimp [newCap1]; omega) hge2) (fun h => absurd h (by omega)))
    · have hlt1 : bs2.length < cap2.toNat := lt_cap_toNat_of_beq_false hcap2_le (Bool.eq_false_iff.mpr hcap2)
      apply SepWPp.of_sepWP_cs_placed (mid := entry + 352#64); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
      exact hstep352 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d hp hlt1 hfit (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try ac_rfl) hnext
  · apply SepWPp.of_sepWP_cs_placed (mid := entry + 432#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionPrevBytes_of_empty bs2 d hp]; exact Entails.of_eq (by ac_rfl))
      (hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩))

/-! ## 2. Top-Level Correctness of `encode<EpochDirection> [local#1]` -/

/-- General `SepWPp` correctness for `encode<EpochDirection> [local#1]` on an arbitrary `prog`,
parameterized by `resStack` (`doReserveStack` or `doReserveStackX`). -/
theorem epochDirection1_gen_ok_prog {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {A : RustAlloc} {entry varint_pc reserve_pc memcpy_pc : BitVec 64}
    (hfn1 : IsEd1EntryProg prog entry varint_pc reserve_pc memcpy_pc)
    {x : EncodeEpochDirectionPinnedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok prog varint_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok prog reserve_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok prog memcpy_pc sessionMemcpyRegionSpec)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp prog (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s' ∧ StepInv s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeEpochDirectionPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  have hfn_ed := isEpochDirectionEncodeEntryProg_of_ed1 hfn1
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp
  have hpre_pure := hpre; dsimp only [encodeEpochDirectionPinnedSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hx1, hx2, hlen_fit⟩, hpre_mem⟩ := hpre_pure
  obtain ⟨hnext_lt, hprev_lt, hnext_cap0, hprev_cap0⟩ :=
    epochDirectionPBPinnedAt_bounds_of_satisfies (A := A) (g := x.g) (dirA := x.dirA) (d := x.dir)
      (F := vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  obtain ⟨_, hcap_lt, _⟩ :=
    Auth.vecU8At_bounds_of_satisfies (A := A) (v := x.v) (cap := x.cap) (ptr := x.ptr) (bs := x.bs)
      (F := epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗ A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack) ∗ R)
      (by convert hpre_mem using 1; ac_rfl)
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A x.v x.cap x.ptr x.bs ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗
      A.pool ∗ stackAt s0.sp (authEncodeStackOf resStack)) ∗
      epochDirectionRestAt A x.g x.dirA x.dir) ∗ R := by
    rw [epochDirectionPBPinnedAt_eq_elems A x.g x.dirA x.dir hnext_cap0 hprev_cap0] at hpre_mem
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have htot_split := encodeEpochDirectionMsg_len_split x.tag x.dir
  have htot_len := epochDirectionPBEncodedLen_eq_fields_len x.dir
  have hlen_pb_lt : epochDirectionPBEncodedLen x.dir < 2 ^ 64 := by
    rw [htot_len]; rcases hlen_fit with h | h <;> omega
  have hfit_hdr : x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length ≤ x.cap.toNat ∨
      x.bs.length + (epochDirectionHeaderBytes x.tag x.dir).length + 10 < 2 ^ 62 := by
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  let S := epochDirectionSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine step_hdr_1 hres A hfn1 henc
    x.tag x.v x.cap x.ptr x.dirA x.g.next.ptr x.g.prev.ptr s0.sp x.bs x.dir
    hnext_lt hprev_lt hlen_pb_lt hfit_hdr
    (F := epochDirectionRestAt A x.g x.dirA x.dir)
    hpc hrun rfl halign rfl hw0 hx1 hx2 (AuthEncodeCalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hge1 hpres1
  let bs1 := x.bs ++ epochDirectionHeaderBytes x.tag x.dir
  have hfit_ctr : bs1.length + (epochDirectionCtrBytes x.dir).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs1]; rw [List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_ctr_1 hres A hfn1 henc hdoReserve
    x.v cap1 ptr1 x.dirA s0.sp bs1 x.dir hfit_ctr
    (F := epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗ S ∗
      epochDirectionRestAt A x.g x.dirA x.dir)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 (by dsimp [bs1, S]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 hge2 hpres2
  let bs2 := bs1 ++ epochDirectionCtrBytes x.dir
  have hfit_next : bs2.length + (epochDirectionNextBytes x.dir).length ≤ cap2.toNat ∨
      bs2.length + (epochDirectionNextBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs2, bs1]; rw [List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_next_1 hres A hfn1 henc hdoReserve hmemcpy
    x.v cap2 ptr2 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs2 x.dir hnext_lt hfit_next
    (F := S ∗ epochDirectionRestAt A x.g x.dirA x.dir)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2 (by dsimp [bs2, S]; ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hcs3 hge3 hpres3
  let bs3 := bs2 ++ epochDirectionNextBytes x.dir
  have hfit_prev : bs3.length + (epochDirectionPrevBytes x.dir).length ≤ cap3.toNat ∨
      bs3.length + (epochDirectionPrevBytes x.dir).length + 10 < 2 ^ 62 := by
    dsimp [bs3, bs2, bs1]; rw [List.length_append, List.length_append, List.length_append]
    rcases hlen_fit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_prev_1 hres A hfn1 henc hdoReserve hmemcpy
    x.v cap3 ptr3 x.dirA x.g.next.ptr x.g.prev.ptr s0.sp bs3 x.dir hprev_lt hfit_prev
    (F := S ∗ epochDirectionRestAt A x.g x.dirA x.dir)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 hcs3 (by dsimp [bs3, S]) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hcs4 hge4 hpres4
  refine step_epochDir_epilogue_placed hres hfn_ed s0.sp
    (F := vecU8At A x.v cap4 ptr4 (bs3 ++ epochDirectionPrevBytes x.dir) ∗
      epochDirectionElemsAt x.dirA x.g.next.ptr x.g.prev.ptr x.dir ∗ A.pool ∗
      epochDirectionRestAt A x.g x.dirA x.dir)
    hpc4 hrun4 hsp4 halign htr4 hcs4 (by dsimp [S]; ac_rfl) ?_
  intro sf _ _ hspf htrf hcc hinvf; refine ⟨fun hm => ?_, hspf, hcc, hinvf⟩
  have hge_all : x.cap.toNat ≤ cap4.toNat :=
    Nat.le_trans hge1 (Nat.le_trans hge2 (Nat.le_trans hge3 hge4))
  have hpres_all : x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
      cap4 = x.cap ∧ ptr4 = x.ptr := by
    intro hfit_cap
    obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
    obtain ⟨hc2, hp2⟩ := hpres2 (by dsimp [bs1]; rw [hc1, List.length_append]; omega)
    obtain ⟨hc3, hp3⟩ := hpres3 (by dsimp [bs2, bs1]; rw [hc2, hc1, List.length_append, List.length_append]; omega)
    obtain ⟨hc4, hp4⟩ := hpres4 (by
      dsimp [bs3, bs2, bs1]
      rw [hc3, hc2, hc1, List.length_append, List.length_append, List.length_append]; omega)
    exact ⟨hc4.trans (hc3.trans (hc2.trans hc1)), hp4.trans (hp3.trans (hp2.trans hp1))⟩
  dsimp only [encodeEpochDirectionPinnedSpecOf]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
  refine ⟨cap4, ptr4, ?_⟩
  have hpure : (x.cap.toNat ≤ cap4.toNat ∧
      (x.bs.length + (encodeEpochDirectionMsg x.tag x.dir).length ≤ x.cap.toNat →
        cap4 = x.cap ∧ ptr4 = x.ptr)) = True :=
    eq_true ⟨hge_all, hpres_all⟩
  dsimp [bs3, bs2, bs1] at hm
  rw [hpure, pure_true, emp_sepConj,
    epochDirectionPBPinnedAt_eq_elems A x.g x.dirA x.dir hnext_cap0 hprev_cap0,
    ← bs0_append_encodeEpochDirectionMsg x.bs x.tag x.dir]
  convert hm using 1; ac_rfl

/-- General `SepWPp` correctness for `encode<EpochDirection> [local#1]`, parameterized by
`resStack` (`doReserveStack` or `doReserveStackX`). -/
theorem epochDirection1_gen_ok_ext {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : EncodeEpochDirectionPinnedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"))
      (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy")) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧ SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P
      (fun s' Q => ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeEpochDirectionPinnedSpecOf resStack A).post x s0 s' ∗ R)) ∧
        s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s' ∧ StepInv s0 s')
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeEpochDirectionPinnedSpec A).onPanic x s0 sf ∗ R)) :=
  epochDirection1_gen_ok_prog hres (Or.inl ⟨b, ext, rfl, rfl, rfl, rfl, rfl⟩)
    henc hdoReserve hmemcpy hpc hrun hpre hsp

theorem encode_epochDirection_1_pinned_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncodeEpochDirection1PinnedOkExt b A ext := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  have henc0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"))
      (encodeVarintFitSpecOf doReserveStack A) := by
    rw [encodeEpochDirection1_encodeVarint2_fnAddr_eq]; exact encode_varint2_fit_ok_ext hA
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      (doReserve2SpecOf doReserveStack A) := by
    rw [encodeEpochDirection1_doReserve2_fnAddr_eq]; exact do_reserve2_ok_ext hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy")) sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeEpochDirection1Name
      (num% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      (by rw [(ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"), (ls_stub% "memcpy")])
  obtain ⟨P, hP, hwp⟩ := epochDirection1_gen_ok_ext (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced s0 henc0) (subroutine_ok_withAuthEncodeCSPlaced s0 hdoReserve0)
    hmemcpy hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem encode_epochDirection_1_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    EncodeEpochDirection1OkExt b A ext :=
  epochDirection_unpinned_of_pinned (encode_epochDirection_1_pinned_ok_ext hA)

theorem encode_epochDirection_1_pinned_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncodeEpochDirection1PinnedOkX img A ext := by
  have hdoReserve := do_reserve2_ok_ext_x (img := img) hA
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨hinv0, hpre⟩ := hpre
  have henc0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection1Name + bv% (2 ^ 64 - ls_rel% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"))
      ((encodeVarintFitSpecOf doReserveStackX A).inImage img) := by
    rw [encodeEpochDirection1_encodeVarint2_fnAddr_eq]; exact encodeVarint2_fit_ok_ext_x img A ext hdoReserve
  have hdoReserve0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      ((doReserve2SpecOf doReserveStackX A).inImage img) := by
    rw [encodeEpochDirection1_doReserve2_fnAddr_eq]; exact hdoReserve
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeEpochDirection1Name + bv% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy")) sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at encodeEpochDirection1Name
      (num% (ls_rel% "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]" "memcpy"))
      (by rw [(ls_lemma% fnOff "prost::encoding::message::encode::<spqr::proto::pq_ratchet::chain::epoch::EpochDirection, alloc::vec::Vec<u8>> [local#1]"), (ls_stub% "memcpy")])
  obtain ⟨P, hP, hwp⟩ := epochDirection1_gen_ok_ext (by decide)
    (subroutine_ok_withAuthEncodeCSPlaced_x img s0 hinv0 henc0)
    (subroutine_ok_withAuthEncodeCSPlaced_x img s0 hinv0 hdoReserve0)
    hmemcpy hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem encode_epochDirection_1_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    EncodeEpochDirection1OkX img A ext :=
  epochDirection_unpinned_of_pinned_x (encode_epochDirection_1_pinned_ok_ext_x hA)

theorem encode_epochDirection_1_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_154 H) (blkPl_154).base
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpec A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn1 : IsEd1EntryProg (lsProg_154 H) (blkPl_154).base (blkPl_148).base (blkPl_157).base (lsρ lsMemcpySym) :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := epochDirection1_gen_ok_prog (by decide) hfn1
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem encode_epochDirection_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_154 H) (blkPl_154).base
      (withLsCodeLoaded lsmpl (encodeEpochDirectionSpec A)) :=
  epochDirection_unpinned_of_pinned_placed_x
    (encode_epochDirection_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

theorem encode_epochDirection_1_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_154 H) (blkPl_154).base
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  have hfn1 : IsEd1EntryProg (lsProg_154 H) (blkPl_154).base (blkPl_148).base (blkPl_157).base (lsρ lsMemcpySym) :=
    Or.inr ⟨‹_›, H, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨P, hP, hwp⟩ := epochDirection1_gen_ok_prog (by decide) hfn1
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withAuthEncodeCSPlaced_placed_blk s0 hcl0 (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, sepWPp_mono_placed hwp (fun _ _ ⟨hp, h1, h2, _⟩ => ⟨hp, h1, h2⟩) (fun _ _ hp => hp)⟩

theorem encode_epochDirection_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_154 H) (blkPl_154).base
      (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecX A)) :=
  epochDirection_unpinned_of_pinned_placed_x
    (encode_epochDirection_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

end CryptoVerification.SpqrV1.Prost.MessageEncode
