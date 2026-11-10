/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` Key Varint Decode

Little-endian 8-byte helpers and key-varint CPS proofs (`+104 .. +140`, error stubs `+328 .. +368`)
for `<SignedPreKeyRecordStructure as Message>::decode::<&[u8]>` (Block `562`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local arm64_norm] BitVec.toNat_zero

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Little-endian 8-byte split & unsigned borrow helpers for inline `fixed64` -/

theorem spk_pointsToBytes8_cons (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (rest2 : List (BitVec 8)) :
    (a ↦ₛ (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest2)) =
      (a ↦₆₄ ((b7 ++ b6 ++ b5 ++ b4) ++ (b3 ++ b2 ++ b1 ++ b0))) ∗ ((a + 8#64) ↦ₛ rest2) := by
  have heq : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest2) =
      ([b0, b1, b2, b3] ++ [b4, b5, b6, b7]) ++ rest2 := rfl
  rw [heq, pointsToBytes_append, pointsToBytes_append,
    show ([b0, b1, b2, b3] ++ [b4, b5, b6, b7]).length = 8 from rfl,
    show [b0, b1, b2, b3].length = 4 from rfl,
    pointsToBytes4_eq_pointsTo32, pointsToBytes4_eq_pointsTo32,
    pointsTo32_pair]

theorem spk_le64_eq_pair32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b7 ++ b6 ++ b5 ++ b4) ++ (b3 ++ b2 ++ b1 ++ b0)) =
      le64 b0 b1 b2 b3 b4 b5 b6 b7 := by
  have ha : ((b7 ++ b6 ++ b5 ++ b4) ++ (b3 ++ b2 ++ b1 ++ b0)) =
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) := by bv_kernel
  rw [ha]
  exact le64_eq_concat b0 b1 b2 b3 b4 b5 b6 b7

theorem spk_sub8_ge8 {n : ℕ} (hge : 8 ≤ n) (hlt : n < 2 ^ 63) :
    !(BitVec.ofNat 64 n).ult 8#64 = true ∧
      BitVec.ofNat 64 n - 8#64 = BitVec.ofNat 64 (n - 8) := by
  constructor
  · simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]; omega
  · bv_omega

/-! ## Key varint & header check (`+104..+140` & error stubs `+328..+368`) -/

private theorem decodeKey_none_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (bs : List (BitVec 8)) (m : SignedPreKeyRecordStructure) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      decodeErrorAtStackLen A err 0 ∗
      memRegion sp' 16 ∗ (ptr ↦ₛ bs) ∗
      memRegion (sp' + 112#64) 48 ∗
      spkStructLoopOf A sp' bs.length m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      spkStructOf A sp' m ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗
        memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' cfg.subStack := by
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗ (ptr ↦ₛ bs) ∗
        memRegion (sp' + 112#64) 48 ∗
        spkStructLoopOf A sp' bs.length m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      spkStructLoopOf A sp' bs.length m ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗
        memRegion x19 88 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' cfg.subStack := by
    rw [hstack]; ac_rfl
  rw [hp]
  exact sepConj_mono_left (spkStructLoopOf_entails_of A sp' bs.length m)

private theorem decodeKey_err_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure)
    (e0 v120 : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      sliceCursorAfter sp' ptr bs rest ∗
      ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ v120) ∗
      memRegion (sp' + 128#64) 32 ∗
      spkStructLoopOf A sp' bs.length m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      ((sp' + 112#64) ↦₆₄ e0) ∗ memRegion (sp' + 120#64) 40 ∗
        spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack := by
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ v120) ∗
        memRegion (sp' + 128#64) 32 ∗
        spkStructLoopOf A sp' bs.length m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      (((sp' + 120#64) ↦₆₄ v120) ∗ memRegion (sp' + 128#64) 32) ∗
        spkStructLoopOf A sp' bs.length m ∗
        sliceCursorAfter sp' ptr bs rest ∗
        (((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
          memRegion x19 88 ∗ A.pool ∗
          stackAt sp' cfg.subStack) := by
    rw [hstack]; ac_rfl
  rw [hp]
  refine Entails.trans
    (sepConj_mono (spkErr16_pack40 sp' v120)
      (sepConj_mono (spkStructLoopOf_entails_of A sp' bs.length m)
        (sepConj_mono_left (sliceCursorAfter_entails_memRegion sp' ptr bs rest)))) ?_
  apply entails_of_eq; ac_rfl

private theorem decodeKey_ok_pack (cfg : SpkCfg) (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure)
    (e0 e1 : BitVec 64) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
      stackAt sp' cfg.varintStk ∗
      sliceCursorAfter sp' ptr bs rest ∗
      ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗
      memRegion (sp' + 128#64) 32 ∗
      spkStructLoopOf A sp' bs.length m ∗
      memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
        (cfg.subStack - cfg.varintStk) ⊢
      spkAfterVarintMemAt cfg.subStack A sp' x19 ptr bs rest bs.length m := by
  unfold spkAfterVarintMemAt
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  have h48 := Entails.trans (sepConj_mono_right (spkErr16_pack40 sp' e1))
    (spkPointsTo112_memRegion40_entails_48 sp' e0)
  have hp :
      ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗
        stackAt sp' cfg.varintStk ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗
        memRegion (sp' + 128#64) 32 ∗
        spkStructLoopOf A sp' bs.length m ∗
        memRegion x19 88 ∗
        memRegion (sp' - BitVec.ofNat 64 cfg.subStack)
          (cfg.subStack - cfg.varintStk) =
      (((sp' + 112#64) ↦₆₄ e0) ∗ ((sp' + 120#64) ↦₆₄ e1) ∗ memRegion (sp' + 128#64) 32) ∗
        sliceCursorAfter sp' ptr bs rest ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗
        spkStructLoopOf A sp' bs.length m ∗
        memRegion x19 88 ∗ A.pool ∗
        stackAt sp' cfg.subStack := by
    rw [hstack]; ac_rfl
  rw [hp]
  refine Entails.trans (sepConj_mono_left h48) ?_
  apply entails_of_eq; ac_rfl

/-- Key decode CPS (`+104..+140` + error stubs `+328..+368`): valid for ANY `bs` with
`bs.length < 2 ^ 63` (including `bs = []` for the prologue empty-slice path). -/
theorem decodeKey_104_cps {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_key)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hok : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s3 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_dispatch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s3.readReg64 .x1 = BitVec.ofNat 64 tag →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkAfterVarintMemAt cfg.subStack A sp' x19 ptr bs rest bs.length m)
        (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : decodeKey bs = none → out = none) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkLoopMemAt cfg.subStack A sp' x19 ptr bs m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  unfold spkLoopMemAt
  have hcall := B.decodeVarint6
  have hfrom := @fromCommon_372_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 104 40
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 328 44
  dsimp only [tripleRatchetProgAtExt] at hcall hfrom hok hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
    (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom
    ⟨sp' + 104#64, sp', ptr, bs⟩
    hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_keyRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr bs ∗
      A.pool ∗ stackAt sp' cfg.varintStk)
    (φ := sp' + 104#64 = sp' + 104#64 ∧ bs.length < 2 ^ 63)
    (by simp [spkDecodeVarintSpecAt, hsp_eq, h29, arm64_norm])
    ⟨rfl, hlen⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
    ⟨hsp2_eq,
     hx29_2,
     by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
     ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
  dsimp only [spkDecodeVarintSpecAt]
  cases hdv : decodeVarint bs with
  | none =>
    have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx0_1 => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
    have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF3, hsym3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24,
      by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25,
       by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27,
       by simpa [arm64_norm] using hregs2.saved.x28⟩⟩, ?_⟩
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    exact Entails.trans
      (decodeKey_none_pack cfg A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) bs m)
      (spkConvergeMem_none_intro cfg.subStack A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 m bs
        (hnone hdk) hx1_nz)
  | some kv =>
    rcases kv with ⟨key, rest⟩
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_key⟩ => ?_
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    have hw1_k : s2.readReg64 (Reg.gpr 1#5) = key := hx1_key
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (spkMemRegion48_unpack16 sp')))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
    by_cases hkey32 : 2 ^ 32 ≤ key.toNat
    · have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp [show ¬ key.toNat < 4294967296 by omega]
      have hlsr := key_lsr32_ne_zero_of_ge key hkey32
      have hbeq : ((key >>> 32) == 0#64) = false := beq_eq_false_iff_ne.mpr (bne_iff_ne.mp hlsr)
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_fromCommon) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
          (kind := BitVec.ofNat 64 (2 ^ 63 + 4)) (e0 := e0)
          (mErr := m) (bs := bs) (out := out) (hnone hdk)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [KindNoHeap])
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
      simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
      exact decodeKey_err_pack cfg A sp' x19 ptr bs rest m e0 key
    · have hkey_lt : key.toNat < 2 ^ 32 := Nat.lt_of_not_ge hkey32
      have hlsr := key_lsr32_eq_zero_of_lt key hkey_lt
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp [show key.toNat < 4294967296 by omega, hwt]
        have hge6 : 6 ≤ key.toNat % 8 := by
          have hmod8 : key.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
          have h := (WireType.ofNat?_eq_none_iff (key.toNat % 8) hmod8).mp hwt
          omega
        have hcs_cond := key_and7_ule6_of_ge key hge6
        refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_fromCommon) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
        intro hF3 hsym3
        refine Wire.SepWPp.mono_pre ?_
          (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
            (kind := BitVec.ofNat 64 (2 ^ 63 + 3)) (e0 := e0)
            (mErr := m) (bs := bs) (out := out) (hnone hdk)
            (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
             by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
             ⟨by simpa [arm64_norm] using hregs2.saved.x25,
              by simpa [arm64_norm] using hregs2.saved.x26,
              by simpa [arm64_norm] using hregs2.saved.x27,
              by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
            (by simp [arm64_norm]) (by simp [KindNoHeap])
            (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
            hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
        simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
        exact decodeKey_err_pack cfg A sp' x19 ptr bs rest m e0 (key &&& 7#64)
      | some wt =>
        have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
        have hcs_cond := key_and7_ule6_of_lt key hlt6
        by_cases htag0 : key.toNat / 8 < 1
        · have hdk : decodeKey bs = none := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show key.toNat < 8 by omega]
          have htz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
          refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_fromCommon) ?_
          wp_steps
          refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
          intro hF3 hsym3
          refine Wire.SepWPp.mono_pre ?_
            (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
              (kind := BitVec.ofNat 64 (2 ^ 63 + 5)) (e0 := e0)
              (mErr := m) (bs := bs) (out := out) (hnone hdk)
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25,
                by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27,
                by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [arm64_norm]) (by simp [KindNoHeap])
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
          simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
          exact decodeKey_err_pack cfg A sp' x19 ptr bs rest m e0 e1
        · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show ¬ key.toNat < 8 by omega]
          have htnz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
          have htnz' : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) == 0#64) = false := by
            simpa [arm64_norm] using htnz
          refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_dispatch) ?_
          wp_steps
          refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
          intro hF3 hsym3
          have htag_eq : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) =
              BitVec.ofNat 64 (key.toNat / 8) := by
            simpa [arm64_norm] using key_tag32_zeroExtend64_eq key hkey_lt
          have hwt_eq := key_and7_eq_wt key hwt
          refine Wire.SepWPp.mono_pre ?_
            (hok (key.toNat / 8) wt rest _ hdk
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25,
                by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27,
                by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [hwt_eq, arm64_norm])
              (by simp [htag_eq, arm64_norm])
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
          simp only [hsp_eq, hsp2_eq, arm64_norm]
          exact decodeKey_ok_pack cfg A sp' x19 ptr bs rest m e0 e1

/-! ## Relocatable `[LibsignalPlacement]` Key Decode CPS (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem decodeKey_104_placed_cps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_562).base + spkOff_key) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hok : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s3 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s3.pc = (blkPl_562).base + spkOff_dispatch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.readReg64 .x0 = BitVec.ofNat 64 wt.toNat →
      s3.readReg64 .x1 = BitVec.ofNat 64 tag →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : decodeKey bs = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkLoopMem A sp' x19 ptr bs m)
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  unfold spkLoopMem
  have hcall := spk_decodeVarint6_placed_ok d
  have hfrom := @fromCommon_372_placed_wp _ A H hH s0
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' SpqrV1.Varint.decodeVarint2Stack
    (SpqrV1.Varint.skipField3Stack 100)
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 559) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine sepWPp_call_lscro ⟨sp' + 104#64, sp', ptr, bs⟩ hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_keyRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr bs ∗
      A.pool ∗ stackAt sp' SpqrV1.Varint.decodeVarint2Stack)
    (φ := sp' + 104#64 = sp' + 104#64 ∧ bs.length < 2 ^ 63)
    (by simp [SpqrV1.Varint.decodeVarint2Spec, hsp_eq, h29, arm64_norm])
    ⟨rfl, hlen⟩ (by rw [hstack]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := SpkLoopRegs.of_calleeSaved hsp2 hcs2
    ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
     by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
     ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
      by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  dsimp only [SpqrV1.Varint.decodeVarint2Spec]
  cases hdv : decodeVarint bs with
  | none =>
    have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun hx0_1 => Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
    have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcrl3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩, ?_⟩
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    exact Entails.trans (decodeKey_none_pack spkCfgLegacy A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) bs m)
      (spkConvergeMem_none_intro spkCfgLegacy.subStack A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 m bs (hnone hdk) hx1_nz)
  | some kv =>
    rcases kv with ⟨key, rest⟩; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_key⟩ => Wire.SepWPp.pure_pre fun htr2 => ?_
    have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    have hw1_k : s2.readReg64 (Reg.gpr 1#5) = key := hx1_key
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (spkMemRegion48_unpack16 sp')))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
    by_cases hkey32 : 2 ^ 32 ≤ key.toNat
    · have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp [show ¬ key.toNat < 4294967296 by omega]
      have hbeq : ((key >>> 32) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr (bne_iff_ne.mp (key_lsr32_ne_zero_of_ge key hkey32))
      refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
      wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      refine Wire.SepWPp.mono_pre ?_
        (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
          (kind := BitVec.ofNat 64 (2 ^ 63 + 4)) (e0 := e0)
          (mErr := m) (bs := bs) (out := out) (hnone hdk)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) (by simp [KindNoHeap])
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simp [htr2, htr, arm64_norm]))
      simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
      exact decodeKey_err_pack spkCfgLegacy A sp' x19 ptr bs rest m e0 key
    · have hkey_lt : key.toNat < 2 ^ 32 := Nat.lt_of_not_ge hkey32
      have hlsr := key_lsr32_eq_zero_of_lt key hkey_lt
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp [show key.toNat < 4294967296 by omega, hwt]
        have hge6 : 6 ≤ key.toNat % 8 := by
          have h := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (Nat.mod_lt _ (by decide))).mp hwt; omega
        have hcs_cond := key_and7_ule6_of_ge key hge6
        refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
        wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
        refine Wire.SepWPp.mono_pre ?_
          (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
            (kind := BitVec.ofNat 64 (2 ^ 63 + 3)) (e0 := e0)
            (mErr := m) (bs := bs) (out := out) (hnone hdk)
            (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
             by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
             ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
              by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
            (by simp [arm64_norm]) (by simp [KindNoHeap])
            (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
            hcrl3 (by simp [htr2, htr, arm64_norm]))
        simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
        exact decodeKey_err_pack spkCfgLegacy A sp' x19 ptr bs rest m e0 (key &&& 7#64)
      | some wt =>
        have hcs_cond := key_and7_ule6_of_lt key (WireType.lt_six_of_ofNat?_eq_some hwt)
        by_cases htag0 : key.toNat / 8 < 1
        · have hdk : decodeKey bs = none := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show key.toNat < 8 by omega]
          have htz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
          refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_fromCommon) ?_
          wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
          refine Wire.SepWPp.mono_pre ?_
            (hfrom (sp' := sp') (x19 := x19) (ptr := ptr)
              (kind := BitVec.ofNat 64 (2 ^ 63 + 5)) (e0 := e0)
              (mErr := m) (bs := bs) (out := out) (hnone hdk)
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [arm64_norm]) (by simp [KindNoHeap])
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hcrl3 (by simp [htr2, htr, arm64_norm]))
          simp only [hsp_eq, hsp2_eq, hx29_2, arm64_norm]
          exact decodeKey_err_pack spkCfgLegacy A sp' x19 ptr bs rest m e0 e1
        · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
            unfold decodeKey; rw [hdv]
            simp [show key.toNat < 4294967296 by omega, hwt, show ¬ key.toNat < 8 by omega]
          have htnz' : (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) == 0#64) = false := by
            simpa [arm64_norm] using key_tag32_ne_zero_of_ge1 key hkey_lt htag0
          refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_dispatch) ?_
          wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
          have htag_eq : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 key) >>> 3)) =
              BitVec.ofNat 64 (key.toNat / 8) := by
            simpa [arm64_norm] using key_tag32_zeroExtend64_eq key hkey_lt
          have hwt_eq := key_and7_eq_wt key hwt
          refine Wire.SepWPp.mono_pre ?_
            (hok (key.toNat / 8) wt rest _ hdk
              (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
              ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
               by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
               ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
                by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
              (by simp [hwt_eq, arm64_norm]) (by simp [htag_eq, arm64_norm])
              (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
              hcrl3 (by simp [htr2, htr, arm64_norm]))
          simp only [hsp_eq, hsp2_eq, arm64_norm]
          exact decodeKey_ok_pack spkCfgLegacy A sp' x19 ptr bs rest m e0 e1

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
