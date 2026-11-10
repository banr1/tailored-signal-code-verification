/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyHeader
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PendingPreKeyFields
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.SenderReceiverChains
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXAPlaced
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PendingPreKeyFieldsXB
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.PrologueVersionLocalIdentityXPlaced
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `SessionStructure::encode_raw` Tag 9: `pending_pre_key` (Block `14`)

Verifies the outer `0x4a` tag and nested length computation, subfields 3 (`signed_pre_key_id`) and
4 (`timestamp`), and the combined protobuf tag 9 (`pending_pre_key`, Block `14` offsets `536..1080`)
under `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 Arm64.Obj ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  er_truncate32_zext64_lsr6
  erHwVarintLen_eq_encodeVarint_length
  erHwVarintLen_bvShift_eq_encodeVarint_length
  bv_add_neg80_3a_x
attribute [local simp, local arm64_norm] truncate32_signExtend64

set_option maxHeartbeats 400000

section Placed

theorem sepWPpLsCl_extract_pending_some {pl : MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State}
    {A : RustAlloc} {ss : BitVec 64} {g : TailVecGhost} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = optTailVecAt A 48 (ss + 248#64) (some g) ∗ F := by sep_frame)
    (h : g.tail.length = 24 → g.vec.bytes.length ≤ g.vec.cap.toNat →
      g.vec.cap.toNat < 2 ^ 63 → g.vec.ptr ≠ 0#64 →
      SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  exact sepWPp_extract_pending_some hfocus fun h1 h2 h3 h4 => h h1 h2 h3 h4 hcl

/-! ## Tag `74#8` write (`536..596/764`, cold `2124..2152`) -/

theorem step_tag9_write_tag_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hcap_g : g.vec.cap.toNat < 2 ^ 63)
    (hlen_lt : bs.length + 1 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base +
        (if p.preKeyId.isSome then 596#64 else 764#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ [74#8]) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
  rw [hP]
  refine sepWPpLsCl_extract_vecU8At_bounds (hfocus := by sep_frame)
    (fun hle _ _ => ?_)
  have hcmn1 := cmn1_beq_zero_false hcap_g
  have hcmn2 := cap_beq_noneCap_false hcap_g
  by_cases hlt : bs.length < cap.toNat
  · have hbeq_cap := cap_beq_len_false hlt
    rw [vecU8At_open_one A v cap ptr bs hlt]
    unfold pendingOpenAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun old => ?_
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    rw [← vecU8At_close_one A v cap ptr bs 74#8 hlt]
    unfold pendingOpenAt
    exact (by sep_frame)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
    unfold pendingOpenAt
    simp only [vecHeader, sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2144#64) bs 1
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hlt_new : bs.length < newCap.toNat := by omega
      rw [vecU8At_open_one A v newCap p' bs hlt_new]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + (if p.preKeyId.isSome then 596#64 else 764#64))
      wp_steps
      apply SepWP.done
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ newCap p'
        (by simp only [arm64_norm, optU32Tag_bne1_pc, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [← vecU8At_close_one A v newCap p' bs 74#8 hlt_new]
      unfold pendingOpenAt
      exact (by sep_frame)

/-! ## Subfield 1 (`pre_key_id`) length and `base_key.length` load (`596/764 → 636`) -/

theorem step_tag9_len1_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ []) (hlt_vec : g.vec.bytes.length < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if p.preKeyId.isSome then 596#64 else 764#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_frame)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base + 636#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hbeq0 := ofNat64_len_beq_zero_false hne_vec hlt_vec
  have hbne0 := ofNat64_len_bne_zero_true hne_vec hlt_vec
  rw [hP]
  unfold pendingOpenAt
  cases hpk : p.preKeyId with
  | none =>
    simp only [hpk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 636#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hpk, optUint32Field1_none_eq])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk]
    exact (by sep_frame)
  | some pkId =>
    simp only [hpk, Option.isSome_some, ↓reduceIte] at hpc
    have hpk_val : optU32ValAt (ss + 276#64) g.tail (some pkId) = ((ss + 276#64) ↦₃₂ pkId) :=
      optU32ValAt_some _ _ _
    rw [hpk_val]
    simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 636#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← optUint32Field1_some_length_bv pkId, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    simp only [hpk, hpk_val]
    exact (by sep_frame)

/-! ## Subfield 2 (`base_key`) length and `signed_pre_key_id` load (`636 → 672/788`) -/

theorem step_tag9_len2_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (hne_vec : g.vec.bytes ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 636#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_frame)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base +
        (if p.signedPreKeyId == 0#32 then 788#64 else 672#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
  wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
  refine SepWPpLsCl.weaken_pre ?_ (hnext _
    (by simp only [arm64_norm, spk_cbz_pc, *])
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, ← bytesField2_nonempty_length_bv hne_vec, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
  unfold pendingOpenAt
  exact (by sep_frame)

/-! ## Subfield 3 (`signed_pre_key_id`) length and `timestamp` load (`672/788 → 708/800`) -/

theorem step_tag9_len3_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (ss v sp0 : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if p.signedPreKeyId == 0#32 then 788#64 else 672#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = pendingOpenAt A ss g p ∗ F := by sep_frame)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_14).base +
        (if p.timestamp == 0#64 then 800#64 else 708#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) →
      sm.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length →
      sm.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length →
      sm.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm (pendingOpenAt A ss g p ∗ F) Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  rw [hP]
  unfold pendingOpenAt
  simp only [sepConj_assoc]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [hspk, beq_self_eq_true, ↓reduceIte] at hpc
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbnz_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, hspk, int32Field3_zero_eq])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact (by sep_frame)
  · have hspk_beq : (p.signedPreKeyId == 0#32) = false := bv32_beq_zero_false hspk
    simp only [hspk_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + (if p.timestamp == 0#64 then 800#64 else 708#64))
    wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _
      (by simp only [arm64_norm, ts_cbz_pc, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, ← int32Field3_nonzero_length_bv hspk, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    unfold pendingOpenAt
    exact (by sep_frame)

/-! ## Subfield 4 length, outer length varint, and `w24` dispatch (`708/800 → 824/872`) -/

theorem step_tag9_len4_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base +
      (if p.timestamp == 0#64 then 800#64 else 708#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx24 : s.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (optUint32Field 1 p.preKeyId).length)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (bytesField 2 g.vec.bytes).length)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (int32Field 3 p.signedPreKeyId).length)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr (bs ++ [74#8]) ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base +
        (if p.preKeyId.isSome then 824#64 else 872#64) →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length →
      sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗
          vecU8At A v cap' ptr'
            (bs ++ [74#8] ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ A H hEV
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [hts, beq_self_eq_true, ↓reduceIte] at hpc
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr ((blkPl_14).base + 820#64)
      (bs ++ [74#8]) (by simp; omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← encPendingMem_length_bv_ts_zero g p hts, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; rw [hts]; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 872#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact (by sep_frame)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 824#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact (by sep_frame)
  · have hts_beq : (p.timestamp == 0#64) = false := bv64_beq_zero_false hts
    simp only [hts_beq, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallEV sp0 (BitVec.ofNat 64 (encPendingMem g p).length) v cap ptr ((blkPl_14).base + 756#64)
      (bs ++ [74#8]) (by simp; omega)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm, ← uint64Field4_nonzero_length_bv hts, ← encPendingMem_length_bv g p, *]
    · simp only [arm64_norm, *]
    · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = p.timestamp := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22m : sm.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
        have := hcsm.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 g.vec.bytes.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx24m : sm.readReg64 .x24 = BitVec.zeroExtend 64 (optU32Tag p.preKeyId) := by
        have := hcsm.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      cases hpk : p.preKeyId with
      | none =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 872#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact (by sep_frame)
      | some pkId =>
        simp only [hpk, optU32Tag] at hx24m
        apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 824#64)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap' ptr'
          (by simp only [arm64_norm, ↓reduceIte, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        exact (by sep_frame)

/-! ## Subfield 3 (`signed_pre_key_id`, `976 → 1028`, cold `2564..2592`) -/

theorem step_tag9_sub3_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx22 : s.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1028#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      sm.readReg64 .x21 = p.timestamp →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ int32Field 3 p.signedPreKeyId) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
  rw [hP]
  by_cases hspk : p.signedPreKeyId = 0#32
  · simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 1028#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hspk, int32Field3_zero_eq, List.append_nil]
    exact (by sep_frame)
  · have hbeq0 := zext64_beq_zero_false_3b hspk
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 24#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [24#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact (by sep_frame)) ?_
      refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v cap ptr ((blkPl_14).base + 1028#64) (bs ++ [24#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs_1)
        rw [List.append_assoc, int32Field3_nonzero_eq hspk]
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2584#64) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro s1 newCap p1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = BitVec.signExtend 64 p.signedPreKeyId := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpLsCl.exists_elim fun old => ?_
        apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 24#8 hlt_new
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [24#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact (by sep_frame)) ?_
        refine hCallEV sp0 (BitVec.signExtend 64 p.signedPreKeyId) v newCap p1 ((blkPl_14).base + 1028#64) (bs ++ [24#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hcs2
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_2 : s2.readReg64 .x21 = p.timestamp := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs_2)
          rw [List.append_assoc, int32Field3_nonzero_eq hspk]
          exact (by sep_frame)

/-! ## Subfield 4 (`timestamp`, `1028 → 1080`, cold `2592..2620`) -/

theorem step_tag9_sub4_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64) (g : TailVecGhost) (p : PendingPreKey)
    (bs : List (BitVec 8))
    (hlen_lt : bs.length + 12 < 2 ^ 60)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = p.timestamp)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (pendingOpenAt A ss g p ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((pendingOpenAt A ss g p ∗ vecU8At A v cap' ptr' (bs ++ uint64Field 4 p.timestamp) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hCallEV := @encraw_call_encodeVarint_placed_x _ A H hEV
  have hCallDR := @encraw_call_doReserve_buf_placed_x _ A H hDR
  rw [hP]
  by_cases hts : p.timestamp = 0#64
  · simp only [sepConj_assoc]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 1080#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
    simp only [hts, uint64Field4_zero_eq, List.append_nil]
    exact (by sep_frame)
  · have hbeq0 := bv64_beq_zero_false hts
    refine sepWPpLsCl_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpLsCl.exists_elim fun old => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hclose := vecU8At_close_one A v cap ptr bs 32#8 hlt
      refine SepWPpLsCl.weaken_pre (P' :=
          (vecU8At A v cap ptr (bs ++ [32#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
            (pendingOpenAt A ss g p ∗ F))
        (by
          rw [← hclose]
          exact (by sep_frame)) ?_
      refine hCallEV sp0 p.timestamp v cap ptr ((blkPl_14).base + 1080#64) (bs ++ [32#8])
        (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · intro s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine SepWPpLsCl.weaken_pre ?_ (hnext s1 cap' ptr' hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs_1)
        rw [List.append_assoc, uint64Field4_nonzero_eq hts]
        exact (by sep_frame)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [Prost.vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr ((blkPl_14).base + 2612#64) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · simp only [arm64_norm]
      · intro s1 newCap p1 hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge _
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = p.timestamp := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hlt_new : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p1 bs hlt_new]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpLsCl.exists_elim fun old => ?_
        apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        have hclose := vecU8At_close_one A v newCap p1 bs 32#8 hlt_new
        refine SepWPpLsCl.weaken_pre (P' :=
            (vecU8At A v newCap p1 (bs ++ [32#8]) ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
              (pendingOpenAt A ss g p ∗ F))
          (by
            rw [← hclose]
            exact (by sep_frame)) ?_
        refine hCallEV sp0 p.timestamp v newCap p1 ((blkPl_14).base + 1080#64) (bs ++ [32#8])
          (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm]
        · intro s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hcs2
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          refine SepWPpLsCl.weaken_pre ?_ (hnext s2 cap' ptr' hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs_2)
          rw [List.append_assoc, uint64Field4_nonzero_eq hts]
          exact (by sep_frame)

/-! ## Combined Tag 9 (`pending_pre_key`, `536 → 1080`) -/

theorem step_encraw_tag9_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (ss v sp0 cap ptr : BitVec 64)
    (G_pending : Option TailVecGhost) (s_pending : Option PendingPreKey) (bs : List (BitVec 8))
    (hrel : PendingRel G_pending s_pending)
    (hbound : match G_pending with | none => True | some g => g.vec.bytes.length < 2 ^ 32)
    (hbs_lt : bs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_14).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (optTailVecAt A 48 (ss + 248#64) G_pending ∗ vecU8At A v cap ptr bs ∗
      A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_14).base + 1080#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((optTailVecAt A 48 (ss + 248#64) G_pending ∗
          vecU8At A v cap' ptr' (bs ++ encPendingFieldMem G_pending s_pending) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  cases G_pending with
  | none =>
    cases s_pending with
    | some p => exact False.elim hrel
    | none =>
      rw [hP, optTailVecAt_pending_none_eq]
      simp only [sepConj_assoc]
      apply SepWPpLsCl.of_sepWP (mid := (blkPl_14).base + 1080#64)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpLsCl.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [optTailVecAt_pending_none_eq]
      simp only [encPendingFieldMem, List.append_nil]
      exact (by sep_frame)
  | some g =>
    cases s_pending with
    | none => exact False.elim hrel
    | some p =>
      have hne_vec : g.vec.bytes ≠ [] := publicKey_deserialize_ne_nil hrel.1
      have hlt_vec31 : g.vec.bytes.length < 2 ^ 32 := hbound
      have hlt_vec63 : g.vec.bytes.length < 2 ^ 63 := by omega
      have hlen0_le := encodeVarint_length_le_10 (BitVec.ofNat 64 (encPendingMem g p).length)
      have hlen1_le := optUint32Field1_length_le p.preKeyId
      have hlen2_le := encodeVarint_length_le_10 (BitVec.ofNat 64 g.vec.bytes.length)
      have hlen3_le := int32Field3_length_le p.signedPreKeyId
      rw [hP]
      refine sepWPpLsCl_extract_pending_some (A := A) (ss := ss) (g := g)
        (h := fun hlen24 hle_g hcap_g _ => ?_)
      have hopen := optTailVecAt_pending_some_eq_open A ss g p hlen24 hle_g hrel
      rw [hopen]
      refine step_tag9_write_tag_placed_x hDR ss v sp0 cap ptr g p bs hcap_g (by omega)
        hpc hrun hsp halign htr hx19 hx20 hcs (by sep_frame) ?_
      intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1
      refine step_tag9_len1_placed_x ss v sp0 g p hne_vec hlt_vec63
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hcs1 (by sep_frame) ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2
      refine step_tag9_len2_placed_x ss v sp0 g p hne_vec
        hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx24_2 hx8_2 hx23_2 hcs2 (by sep_frame) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3
      refine step_tag9_len3_placed_x ss v sp0 g p
        hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx24_3 hx8_3 hx9_3 hx23_3 hx22_3 hcs3 (by sep_frame) ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
      refine step_tag9_len4_placed_x hEV ss v sp0 cap1 ptr1 g p bs
        (by omega)
        hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx24_4 hx8_4 hx9_4 hx10_4 hx23_4 hx22_4 hx21_4 hcs4
        (by sep_frame) ?_
      intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5
      refine step_tag9_sub1_placed_x hEV hDR ss v sp0 cap5 ptr5 g p
        ((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length))
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc5 hrun5 hsp5 halign htr5 hx19_5 hx20_5 hx23_5 hx22_5 hx21_5 hcs5 (by sep_frame) ?_
      intro s6 cap6 ptr6 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6
      refine step_tag9_sub2_a_placed_x hEV hDR ss v sp0 cap6 ptr6 g p
        (((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId)
        hne_vec hlt_vec63
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc6 hrun6 hsp6 halign htr6 hx19_6 hx20_6 hx23_6 hx22_6 hx21_6 hcs6 (by sep_frame) ?_
      intro s7 cap7 ptr7 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7
      refine step_tag9_sub2_b_placed_x hDR hC ss v sp0 cap7 ptr7 g p
        ((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length)))
        hne_vec
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc7 hrun7 hsp7 halign htr7 hx19_7 hx20_7 hx24_7 hx23_7 hx22_7 hx21_7 hcs7 (by sep_frame) ?_
      intro s8 cap8 ptr8 hpc8 hrun8 hsp8 htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8
      refine step_tag9_sub3_placed_x hEV hDR ss v sp0 cap8 ptr8 g p
        (((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc8 hrun8 hsp8 halign htr8 hx19_8 hx20_8 hx22_8 hx21_8 hcs8 (by sep_frame) ?_
      intro s9 cap9 ptr9 hpc9 hrun9 hsp9 htr9 hx19_9 hx20_9 hx21_9 hcs9
      refine step_tag9_sub4_placed_x hEV hDR ss v sp0 cap9 ptr9 g p
        ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
          optUint32Field 1 p.preKeyId) ++
          ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
          int32Field 3 p.signedPreKeyId)
        (by simp only [List.length_append, List.length_singleton]; omega)
        hpc9 hrun9 hsp9 halign htr9 hx19_9 hx20_9 hx21_9 hcs9 (by sep_frame) ?_
      intro s10 cap10 ptr10 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10
      refine SepWPpLsCl.weaken_pre ?_ (hnext s10 cap10 ptr10 hpc10 hrun10 hsp10 htr10 hx19_10 hx20_10 hcs10)
      rw [← hopen]
      have hbytes :
          ((((((bs ++ [74#8]) ++ encodeVarint (BitVec.ofNat 64 (encPendingMem g p).length)) ++
            optUint32Field 1 p.preKeyId) ++
            ([18#8] ++ encodeVarint (BitVec.ofNat 64 g.vec.bytes.length))) ++ g.vec.bytes) ++
            int32Field 3 p.signedPreKeyId) ++ uint64Field 4 p.timestamp =
          bs ++ encPendingFieldMem (some g) (some p) := by
        rw [← lenField9_eq g p, ← bytesField2_nonempty_eq hne_vec]
        simp only [List.append_assoc]
      rw [hbytes]
      exact (by sep_frame)

end Placed

end CryptoVerification.E2E.Record.Serialization
