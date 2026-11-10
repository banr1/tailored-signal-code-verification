/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenAux.Pure
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXA
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>` Segment 3: `chain_key` (`+284` → `+600`)

Verifies Segment 3 (`chain_key: Option<ChainKey>`, offsets `+284..+600` with cold reserve paths
`+1884..+2012`) of `prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`, Block `12`) on
`SP2Ext` and under relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open EncodeVarintNorm
open Proofs.libsignal.Hooks2
open scoped BigOperators

set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  Prost.truncate32_zext64_lsr6
  Prost.hwVarintLen_eq_encodeVarint_length
  Prost.hwVarintLen_bvShift_eq_encodeVarint_length
  Prost.hwVarintLen_w32_eq_encodeVarint_length
  Prost.hwVarintLen_w32_natShift_eq_encodeVarint_length

theorem L1_EncodeChainSeg3 : True := trivial

/-! ### `Some` branch check and `0x1a` tag write (`+284 → +340`, cold `1884..1908`) -/

theorem step_encChain_seg3_write_tag_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hDR : DoReserveOkX img A ext)
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 340#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap1 ptr1 (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 284 340
  encChain_fetches_range img.base (Rust.withPanics ext) 1884 1912
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  have hck_niche := Prost.cap_add_one_beq_zero_false hck_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x1a#8 hlt]
    refine SepWPpIn.congr_pre ?_
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_x A ext hDR v curCap curPtr sp0 (entry + bv% (1904))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x1a#8 hnew_gt]
    refine SepWPpIn.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl

/-! ### `(encChainKey ck).length` computation and `encode_varint` (`+340 → +416`) -/

theorem step_encChain_seg3_len_varint_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ck.index)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 416#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 340 416
  encChain_fetches_range img.base (Rust.withPanics ext) 424 432
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 (entry + bv% (416)) bs1
      hcur_lt
      (x := x) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hidx_beq : (ck.index == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
    have hlen_eq := encChainKey_length_nonzero hidx
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_x A ext hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 (entry + bv% (416)) bs1
      hcur_lt
      (x := x) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

/-! ### `uint32Field 1 ck.index` encoding (`+416 → +496`, cold `1912..1936`) -/

theorem step_encChain_seg3_index_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (hcur_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 496#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ uint32Field 1 ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 416 424
  encChain_fetches_range img.base (Rust.withPanics ext) 448 496
  encChain_fetches_range img.base (Rust.withPanics ext) 1912 1940
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  by_cases hidx : ckIdx = 0#32
  · have hidx_bne : (ckIdx != 0#32) = false := by simp [hidx]
    apply SepWPpIn.of_sepWP (mid := entry + bv% (496))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hu0 : bs2 ++ uint32Field 1 ckIdx = bs2 := by simp [hidx, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
  · have hidx_bne : (ckIdx != 0#32) = true := bne_iff_ne.mpr hidx
    have hu_eq : (bs2 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ckIdx) =
        bs2 ++ uint32Field 1 ckIdx := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hidx]
    have hcur_snoc_lt : (bs2 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
    refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun hle _ _ => ?_
    by_cases hlt : bs2.length < cap2.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs2 0x08#8
      rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpIn.exists_elim fun y => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x08#8 hlt]
      refine step_encChain_encodeVarint_x A ext hEV
        (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 sp0 (entry + bv% (496)) (bs2 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]) ?_
      intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
      rw [hu_eq]
      exact hnext sm cap3 ptr3 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
    · have hcap_eq : cap2.toNat = bs2.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1_x A ext hDR v cap2 ptr2 sp0 (entry + bv% (1932))
        bs2 hcap_eq (by omega)
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
      have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
      have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
      have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22r : sr.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx :=
        hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs2 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpIn.exists_elim fun y => ?_
      apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs2 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint_x A ext hEV
        (BitVec.zeroExtend 64 ckIdx) v newCap p' sp0 (entry + bv% (496)) (bs2 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
      rw [hu_eq]
      exact hnext sm cap3 ptr3 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))

/-! ### Key field `0x12` tag and `encode_varint 32` (`+496 → +552`, cold `1940..1968`) -/

theorem step_encChain_seg3_key_tag_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a cap3 ptr3 ckPtr sp0 : BitVec 64) (bs3 : List (BitVec 8))
    (hcur_lt : bs3.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hP : P = ((v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A cap3 ptr3 bs3 ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 552#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = ckPtr →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap4 ptr4 ((bs3 ++ [0x12#8]) ++ encodeVarint 32#64) ∗
          ((a + 80#64) ↦₆₄ ckPtr) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 496 552
  encChain_fetches_range img.base (Rust.withPanics ext) 1940 1968
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have hcur_snoc_lt : (bs3 ++ [0x12#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : bs3.length < cap3.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs3 0x12#8
    rw [vecU8Buf_eq_open_one A cap3 ptr3 bs3 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap3 ptr3 bs3 0x12#8 hlt]
    refine step_encChain_encodeVarint_x A ext hEV
      32#64 v cap3 ptr3 sp0 (entry + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine SepWPpIn.congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))
  · have hcap_eq : cap3.toNat = bs3.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_x A ext hDR v cap3 ptr3 sp0 (entry + bv% (1960))
      bs3 hcap_eq (by omega)
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr := hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs3 0x12#8
    rw [vecU8Buf_eq_open_one A newCap p' bs3 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun y => ?_
    apply SepWPpIn.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs3 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint_x A ext hEV
      32#64 v newCap p' sp0 (entry + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine SepWPpIn.congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

/-! ### Key 32-byte reserve and `memcpy` (`+552 → +600`, cold `1968..2012`) -/

theorem step_encChain_seg3_key_copy_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a cap4 ptr4 ckCap ckPtr sp0 : BitVec 64) (bsMid keyBs : List (BitVec 8))
    (hkey_pos : 0 < keyBs.length)
    (hkey_lt : keyBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 keyBs.length)
    (hx22 : s.readReg64 .x22 = ckPtr)
    (hP : P = ((v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap4 ptr4 bsMid ∗
      Prost.vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap5 ptr5 (bsMid ++ keyBs) ∗
          Prost.vecU8Buf A ckCap ckPtr keyBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 552 600
  encChain_fetches_range img.base (Rust.withPanics ext) 1968 2012
  generalize_entry hentry : (SP2Ext img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := cap4) (ptr := ptr4) (bs := bsMid)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle4 _ _ => ?_
  refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := ckCap) (ptr := ckPtr) (bs := keyBs)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap4 ptr4 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hkey_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid keyBs
  by_cases hfit : bsMid.length + keyBs.length ≤ cap4.toNat
  · have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = false :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).2.mpr hfit
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy_x A ext hC cap4 ptr4 ckPtr sp0 (entry + bv% (592))
      bsMid keyBs hkey_pos hfit hkey_lt
      (x := x)
      (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre ?_
      (hnext _ cap4 ptr4 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl
  · have hrem : cap4.toNat - bsMid.length < keyBs.length := by omega
    have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = true :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).1.mpr hrem
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_x A ext hDR v cap4 ptr4 sp0 (entry + bv% (1992))
      bsMid keyBs.length hle4 hrem hmid_lt hkey_lt
      (x := x)
      (F := Prost.vecU8Buf A ckCap ckPtr keyBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy_x A ext hC newCap p' ckPtr sp0 (entry + bv% (592))
      bsMid keyBs hkey_pos hnew_ge hkey_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpIn.of_sepWP (mid := entry + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl

/-! ### Combined Segment 3 (`+284 → +600`): `chain_key: Option<ChainKey>` -/

theorem step_encChain_seg3_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image}
    (hC : SerContractsX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (hDR : DoReserveOkX img A ext)
    (v a curCap curPtr sp0 : BitVec 64) (pin : VecPin) (o : Option ChainKey)
    (curBs : List (BitVec 8))
    (hbound : curBs.length + (msgField 3 (o.map encChainKey)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ optChainKeyAt A pin o (a + 72#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr encodeChainName + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ msgField 3 (o.map encChainKey)) ∗
          optChainKeyAt A pin o (a + 72#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  cases o with
  | none =>
    encChain_fetches_range img.base (Rust.withPanics ext) 284 296
    generalize_entry (SP2Ext img.base ext).fnAddr encodeChainName = entry
    examples_hide_fetches
    rw [optChainKeyAt_none_eq]
    have hnone_beq : (optChainKeyNone + 1#64 == 0#64) = true := rfl
    apply SepWPpIn.of_sepWP (mid := entry + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hmf0 : curBs ++ msgField 3 (Option.map encChainKey none) = curBs := by simp [msgField]
    rw [← optChainKeyAt_none_eq, ← hmf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  | some ck =>
    have hmf_eq := msgField3_some_eq ck
    have hmf_len : 1 + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length +
        (uint32Field 1 ck.index).length + 34 =
        (msgField 3 (some (encChainKey ck))).length := by
      have h := congrArg List.length hmf_eq
      simp only [List.length_append, List.length_singleton, bytesField2_keyToBytes32_length_encChain] at h
      omega
    have ⟨hvar_pos, _⟩ := Prost.encodeVarint_length_bounds (BitVec.ofNat 64 (encChainKey ck).length)
    have hev32_len : (encodeVarint 32#64).length = 1 := by decide +kernel
    have hkey_len := keyToBytes32_length ck.key
    rw [optChainKeyAt_some_eq_encChain A pin ck a, vecU8At_eq_cells_buf A v curCap curPtr curBs]
    refine sepWPpIn_extract_vecU8Buf_bounds_prost (A := A) (cap := pin.cap) (ptr := pin.ptr)
      (bs := HMAC.keyToBytes32 ck.key)
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        Prost.vecU8Buf A curCap curPtr curBs ∗
        ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun _ hck_lt _ => ?_
    refine step_encChain_seg3_write_tag_x A ext hDR
      v a curCap curPtr pin.cap sp0 ck.index curBs hck_lt
      (by simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 80#64) ↦₆₄ pin.ptr) ∗ Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    refine step_encChain_seg3_len_varint_x A ext hEV
      v a cap1 ptr1 sp0 ck (curBs ++ [0x1a#8])
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2
    refine step_encChain_seg3_index_x A ext hEV hDR
      v a cap2 ptr2 sp0 ck.index
      ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length))
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 (by ac_rfl) ?_
    intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3
    rw [vecU8At_eq_cells_buf A v cap3 ptr3
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)]
    refine step_encChain_seg3_key_tag_x A ext hEV hDR
      v a cap3 ptr3 pin.ptr sp0
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 (by ac_rfl) ?_
    intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4
    rw [vecU8At_eq_cells_buf A v cap4 ptr4
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)]
    have hx21_4' : s4.readReg64 .x21 = BitVec.ofNat 64 (HMAC.keyToBytes32 ck.key).length := by
      rw [hkey_len]; exact hx21_4
    refine step_encChain_seg3_key_copy_x A ext hC hDR
      v a cap4 ptr4 pin.cap pin.ptr sp0
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)
      (HMAC.keyToBytes32 ck.key)
      (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton, hev32_len]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4' hx22_4 (by ac_rfl) ?_
    intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5
    have hlist :
        ((((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64) ++
          HMAC.keyToBytes32 ck.key) =
        curBs ++ msgField 3 (Option.map encChainKey (some ck)) := by
      have hbf2 := bytesField2_keyToBytes32_eq ck.key
      simp only [Option.map_some, ← hmf_eq, ← hbf2, List.append_assoc]
    refine SepWPpIn.congr_pre ?_ (hnext s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5)
    rw [hlist, optChainKeyAt_some_eq_encChain A pin ck a]
    ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` proofs (Block `12`, Segment 3) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_encChain_seg3_write_tag_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hDR : DoReservePlacedOkX A H)
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_12).base + 340#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap1 ptr1 (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  have hck_niche := Prost.cap_add_one_beq_zero_false hck_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x1a#8 hlt]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_placed_x A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1904))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x1a#8 hnew_gt]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl

theorem step_encChain_seg3_len_varint_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ck.index)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 416#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
      hcur_lt
      (x := x) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hidx_beq : (ck.index == 0#32) = false := beq_eq_false_iff_ne.mpr hidx
    have hlen_eq := encChainKey_length_nonzero hidx
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint_placed_x A H hEV
      (BitVec.ofNat 64 (encChainKey ck).length) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (416)) bs1
      hcur_lt
      (x := x) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg3_index_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (hcur_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 496#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ uint32Field 1 ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hidx : ckIdx = 0#32
  · have hidx_bne : (ckIdx != 0#32) = false := by simp [hidx]
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (496))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hu0 : bs2 ++ uint32Field 1 ckIdx = bs2 := by simp [hidx, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
  · have hidx_bne : (ckIdx != 0#32) = true := bne_iff_ne.mpr hidx
    have hu_eq : (bs2 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ckIdx) =
        bs2 ++ uint32Field 1 ckIdx := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hidx]
    have hcur_snoc_lt : (bs2 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun hle _ _ => ?_
    by_cases hlt : bs2.length < cap2.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs2 0x08#8
      rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x08#8 hlt]
      refine step_encChain_encodeVarint_placed_x A H hEV
        (BitVec.zeroExtend 64 ckIdx) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (496)) (bs2 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]) ?_
      intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
      rw [hu_eq]
      exact hnext sm cap3 ptr3 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
    · have hcap_eq : cap2.toNat = bs2.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1_placed_x A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1932))
        bs2 hcap_eq (by omega)
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
      have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
      have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
      have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hx22r : sr.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx :=
        hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs2 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpLsCl.exists_elim fun y => ?_
      apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs2 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint_placed_x A H hEV
        (BitVec.zeroExtend 64 ckIdx) v newCap p' sp0 ((blkPl_12).base + bv% (496)) (bs2 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
      rw [hu_eq]
      exact hnext sm cap3 ptr3 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg3_key_tag_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v a cap3 ptr3 ckPtr sp0 : BitVec 64) (bs3 : List (BitVec 8))
    (hcur_lt : bs3.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hP : P = ((v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      Prost.vecU8Buf A cap3 ptr3 bs3 ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (blkPl_12).base + 552#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = ckPtr →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap4 ptr4 ((bs3 ++ [0x12#8]) ++ encodeVarint 32#64) ∗
          ((a + 80#64) ↦₆₄ ckPtr) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  have hcur_snoc_lt : (bs3 ++ [0x12#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle _ _ => ?_
  by_cases hlt : bs3.length < cap3.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs3 0x12#8
    rw [vecU8Buf_eq_open_one A cap3 ptr3 bs3 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap3 ptr3 bs3 0x12#8 hlt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      32#64 v cap3 ptr3 sp0 ((blkPl_12).base + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine SepWPpLsCl.congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))
  · have hcap_eq : cap3.toNat = bs3.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1_placed_x A H hDR v cap3 ptr3 sp0 ((blkPl_12).base + bv% (1960))
      bs3 hcap_eq (by omega)
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = 32#64 := hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr := hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs3 0x12#8
    rw [vecU8Buf_eq_open_one A newCap p' bs3 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs3 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint_placed_x A H hEV
      32#64 v newCap p' sp0 ((blkPl_12).base + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine SepWPpLsCl.congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

theorem step_encChain_seg3_key_copy_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hDR : DoReservePlacedOkX A H)
    (v a cap4 ptr4 ckCap ckPtr sp0 : BitVec 64) (bsMid keyBs : List (BitVec 8))
    (hkey_pos : 0 < keyBs.length)
    (hkey_lt : keyBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 keyBs.length)
    (hx22 : s.readReg64 .x22 = ckPtr)
    (hP : P = ((v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap4 ptr4 bsMid ∗
      Prost.vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap5 ptr5 (bsMid ++ keyBs) ∗
          Prost.vecU8Buf A ckCap ckPtr keyBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := cap4) (ptr := ptr4) (bs := bsMid)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hle4 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := ckCap) (ptr := ckPtr) (bs := keyBs)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      Prost.vecU8Buf A cap4 ptr4 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (by ac_rfl) fun hkey_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid keyBs
  by_cases hfit : bsMid.length + keyBs.length ≤ cap4.toNat
  · have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = false :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).2.mpr hfit
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy_placed_x A H hC cap4 ptr4 ckPtr sp0 ((blkPl_12).base + bv% (592))
      bsMid keyBs hkey_pos hfit hkey_lt
      (x := x)
      (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ cap4 ptr4 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl
  · have hrem : cap4.toNat - bsMid.length < keyBs.length := by omega
    have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = true :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).1.mpr hrem
    apply SepWPpLsCl.of_sepWP (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice_placed_x A H hDR v cap4 ptr4 sp0 ((blkPl_12).base + bv% (1992))
      bsMid keyBs.length hle4 hrem hmid_lt hkey_lt
      (x := x)
      (F := Prost.vecU8Buf A ckCap ckPtr keyBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = ckPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy_placed_x A H hC newCap p' ckPtr sp0 ((blkPl_12).base + bv% (592))
      bsMid keyBs hkey_pos hnew_ge hkey_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 keyBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl

theorem step_encChain_seg3_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced A H)
    (hEV : EncodeVarintPlacedOkX A H)
    (hDR : DoReservePlacedOkX A H)
    (v a curCap curPtr sp0 : BitVec 64) (pin : VecPin) (o : Option ChainKey)
    (curBs : List (BitVec 8))
    (hbound : curBs.length + (msgField 3 (o.map encChainKey)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ optChainKeyAt A pin o (a + 72#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_12).base + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ msgField 3 (o.map encChainKey)) ∗
          optChainKeyAt A pin o (a + 72#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  cases o with
  | none =>
    rw [optChainKeyAt_none_eq]
    have hnone_beq : (optChainKeyNone + 1#64 == 0#64) = true := rfl
    apply SepWPpLsCl.of_sepWP (mid := (blkPl_12).base + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hmf0 : curBs ++ msgField 3 (Option.map encChainKey none) = curBs := by simp [msgField]
    rw [← optChainKeyAt_none_eq, ← hmf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  | some ck =>
    have hmf_eq := msgField3_some_eq ck
    have hmf_len : 1 + (encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)).length +
        (uint32Field 1 ck.index).length + 34 =
        (msgField 3 (some (encChainKey ck))).length := by
      have h := congrArg List.length hmf_eq
      simp only [List.length_append, List.length_singleton, bytesField2_keyToBytes32_length_encChain] at h
      omega
    have ⟨hvar_pos, _⟩ := Prost.encodeVarint_length_bounds (BitVec.ofNat 64 (encChainKey ck).length)
    have hev32_len : (encodeVarint 32#64).length = 1 := by decide +kernel
    have hkey_len := keyToBytes32_length ck.key
    rw [optChainKeyAt_some_eq_encChain A pin ck a, vecU8At_eq_cells_buf A v curCap curPtr curBs]
    refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A) (cap := pin.cap) (ptr := pin.ptr)
      (bs := HMAC.keyToBytes32 ck.key)
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        Prost.vecU8Buf A curCap curPtr curBs ∗
        ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
      (by ac_rfl) fun _ hck_lt _ => ?_
    refine step_encChain_seg3_write_tag_placed_x A H hDR
      v a curCap curPtr pin.cap sp0 ck.index curBs hck_lt
      (by simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 80#64) ↦₆₄ pin.ptr) ∗ Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    refine step_encChain_seg3_len_varint_placed_x A H hEV
      v a cap1 ptr1 sp0 ck (curBs ++ [0x1a#8])
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2
    refine step_encChain_seg3_index_placed_x A H hEV hDR
      v a cap2 ptr2 sp0 ck.index
      ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length))
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 (by ac_rfl) ?_
    intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3
    rw [vecU8At_eq_cells_buf A v cap3 ptr3
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)]
    refine step_encChain_seg3_key_tag_placed_x A H hEV hDR
      v a cap3 ptr3 pin.ptr sp0
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗
        Prost.vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 (by ac_rfl) ?_
    intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4
    rw [vecU8At_eq_cells_buf A v cap4 ptr4
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)]
    have hx21_4' : s4.readReg64 .x21 = BitVec.ofNat 64 (HMAC.keyToBytes32 ck.key).length := by
      rw [hkey_len]; exact hx21_4
    refine step_encChain_seg3_key_copy_placed_x A H hC hDR
      v a cap4 ptr4 pin.cap pin.ptr sp0
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)
      (HMAC.keyToBytes32 ck.key)
      (by omega) (by omega)
      (by simp only [List.length_append, List.length_singleton, hev32_len]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4 hx21_4' hx22_4 (by ac_rfl) ?_
    intro s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5
    have hlist :
        ((((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
          uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64) ++
          HMAC.keyToBytes32 ck.key) =
        curBs ++ msgField 3 (Option.map encChainKey (some ck)) := by
      have hbf2 := bytesField2_keyToBytes32_eq ck.key
      simp only [Option.map_some, ← hmf_eq, ← hbf2, List.append_assoc]
    refine SepWPpLsCl.congr_pre ?_ (hnext s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5)
    rw [hlist, optChainKeyAt_some_eq_encChain A pin ck a]
    ac_rfl

end Placed

end CryptoVerification.E2E.Record.Serialization
