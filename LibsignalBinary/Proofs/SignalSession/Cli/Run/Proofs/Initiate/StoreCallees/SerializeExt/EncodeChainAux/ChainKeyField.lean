/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.ProloguePart1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>` Segment 3: `chain_key: Option<ChainKey>` (`+0x11c → +0x258`)
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
  sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record
open EncodeVarintNorm
open scoped BigOperators

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Prost.ofNat_countLeadingZeros_64
  Prost.ofNat_countLeadingZeros_32
  Prost.truncate32_ofNat64
  Prost.truncate32_zext64_lsr6
  Prost.hwVarintLen_eq_encodeVarint_length
  Prost.hwVarintLen_bvShift_eq_encodeVarint_length
  Prost.hwVarintLen_w32_eq_encodeVarint_length
  Prost.hwVarintLen_w32_natShift_eq_encodeVarint_length

theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

theorem keyToBytes32_ne_nil_encChain (k : BitVec 256) : HMAC.keyToBytes32 k ≠ [] := by
  intro h
  have := keyToBytes32_length k
  simp [h] at this

theorem bytesField2_keyToBytes32_eq (k : BitVec 256) :
    [0x12#8] ++ encodeVarint 32#64 ++ HMAC.keyToBytes32 k =
      bytesField 2 (HMAC.keyToBytes32 k) := by
  have h1 := bytesField_nonempty_eq 2 0x12#8 (HMAC.keyToBytes32 k) (keyToBytes32_ne_nil_encChain k) (by decide +kernel)
  rw [keyToBytes32_length] at h1
  exact h1

theorem bytesField2_keyToBytes32_length_encChain (k : BitVec 256) :
    (bytesField 2 (HMAC.keyToBytes32 k)).length = 34 := by
  rw [← bytesField2_keyToBytes32_eq]
  have hev : (encodeVarint 32#64).length = 1 := by decide +kernel
  simp [List.length_append, hev, keyToBytes32_length]

theorem uint32Field1_zero_eq : uint32Field 1 0#32 = [] := rfl

theorem uint32Field1_nonzero_eq {idx : BitVec 32} (h : idx ≠ 0#32) :
    [0x08#8] ++ encodeVarint (BitVec.zeroExtend 64 idx) = uint32Field 1 idx := by
  have hk : encodeKey 1 .varint = [0x08#8] := by decide +kernel
  simp [uint32Field, h, hk]

theorem uint32Field1_nonzero_length_bv {idx : BitVec 32} (h : idx ≠ 0#32) :
    BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 idx)).length + 1#64 =
      BitVec.ofNat 64 (uint32Field 1 idx).length := by
  rw [← uint32Field1_nonzero_eq h]
  simp only [List.length_append, List.length_singleton, ← BitVec.ofNat_add, Nat.add_comm]

theorem encChainKey_length_zero {ck : ChainKey} (h : ck.index = 0#32) :
    34#64 = BitVec.ofNat 64 (encChainKey ck).length := by
  unfold encChainKey
  rw [h, uint32Field1_zero_eq, List.nil_append, bytesField2_keyToBytes32_length_encChain]

theorem encChainKey_length_nonzero {ck : ChainKey} (h : ck.index ≠ 0#32) :
    34#64 + (BitVec.ofNat 64 (encodeVarint (BitVec.zeroExtend 64 ck.index)).length + 1#64) =
      BitVec.ofNat 64 (encChainKey ck).length := by
  rw [uint32Field1_nonzero_length_bv h]
  unfold encChainKey
  rw [List.length_append, bytesField2_keyToBytes32_length_encChain, ← BitVec.ofNat_add, Nat.add_comm]

theorem encChainKey_length_bounds (ck : ChainKey) :
    34 ≤ (encChainKey ck).length ∧ (encChainKey ck).length ≤ 45 := by
  unfold encChainKey
  rw [List.length_append, bytesField2_keyToBytes32_length_encChain]
  by_cases h : ck.index = 0#32
  · rw [h, uint32Field1_zero_eq]; simp
  · rw [← uint32Field1_nonzero_eq h, List.length_append, List.length_singleton]
    have ⟨_, hle⟩ := Prost.encodeVarint_length_bounds (BitVec.zeroExtend 64 ck.index)
    omega

theorem msgField3_some_eq (ck : ChainKey) :
    [0x1a#8] ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length) ++
      uint32Field 1 ck.index ++ bytesField 2 (HMAC.keyToBytes32 ck.key) =
      msgField 3 (some (encChainKey ck)) := by
  unfold msgField lenField encChainKey
  have hk : encodeKey 3 .lengthDelimited = [0x1a#8] := by decide +kernel
  rw [hk]
  simp [List.append_assoc]

theorem optChainKeyAt_none_eq (A : RustAlloc) (pin : VecPin) (a : BitVec 64) :
    optChainKeyAt A pin none (a + 72#64) =
      ((a + 72#64) ↦₆₄ optChainKeyNone) ∗ memRegion (a + 80#64) 24 := by
  dsimp only [optChainKeyAt]
  have h80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  rw [h80]

theorem optChainKeyAt_some_eq_encChain (A : RustAlloc) (pin : VecPin) (ck : ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin (some ck) (a + 72#64) =
      ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
      ((a + 88#64) ↦₆₄ 32#64) ∗
      vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
      ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 := by
  dsimp only [optChainKeyAt]
  have h80 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have h88 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  have h96 : (a + 72#64) + 24#64 = a + 96#64 := by bv_omega
  have h100 : (a + 72#64) + 28#64 = a + 100#64 := by bv_omega
  rw [vecU8At_eq_cells_buf, keyToBytes32_length, h80, h88, h96, h100]
  ac_rfl

/-! ### Step 3a (`+284 → +340`, cold `1884..1908`): check `Some`, write tag `0x1a#8`, load `w22`, `x21` -/

theorem step_encChain_seg3_write_tag (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr ckCap sp0 : BitVec 64) (ckIdx : BitVec 32) (curBs : List (BitVec 8))
    (hck_lt : ckCap.toNat < 2 ^ 63)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 340#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap1 ptr1 (curBs ++ [0x1a#8]) ∗
          ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 284 340
  encChain_fetches_range img.base (Rust.withPanics ext) 1884 1912
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 72#64) ↦₆₄ ckCap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ckIdx) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hck_niche := Prost.cap_add_one_beq_zero_false hck_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x1a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x1a#8 hlt]
    refine sepWPp_congr_pre ?_
      (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 img A ext hDR v curCap curPtr sp0 (entry + bv% (1904))
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
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (340))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x1a#8 hnew_gt]
    refine sepWPp_congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf]; ac_rfl

/-! ### Step 3b (`+340 → +416`, with `+424..+432`): compute `(encChainKey ck).length` and call `encode_varint` -/

theorem step_encChain_seg3_len_varint (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (v a cap1 ptr1 sp0 : BitVec 64) (ck : ChainKey) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ck.index)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 416#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = BitVec.zeroExtend 64 ck.index →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 340 416
  encChain_fetches_range img.base (Rust.withPanics ext) 424 432
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  by_cases hidx : ck.index = 0#32
  · have hidx_beq : (ck.index == 0#32) = true := by simp [hidx]
    have hlen_eq := encChainKey_length_zero hidx
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint img A ext hEV
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint img A ext hEV
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

/-! ### Step 3c (`+416 → +496`, cold `1912..1936`): encode `uint32Field 1 ck.index` -/

theorem step_encChain_seg3_index (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a cap2 ptr2 sp0 : BitVec 64) (ckIdx : BitVec 32) (bs2 : List (BitVec 8))
    (hcur_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 416#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hx22 : s.readReg64 .x22 = BitVec.zeroExtend 64 ckIdx)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 496#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap3 ptr3 (bs2 ++ uint32Field 1 ckIdx) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 416 424
  encChain_fetches_range img.base (Rust.withPanics ext) 448 496
  encChain_fetches_range img.base (Rust.withPanics ext) 1912 1940
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  by_cases hidx : ckIdx = 0#32
  · have hidx_bne : (ckIdx != 0#32) = false := by simp [hidx]
    apply SepWPpX.of_sepWP (mid := entry + bv% (496))
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
    refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle => ?_
    by_cases hlt : bs2.length < cap2.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs2 0x08#8
      rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPpX.exists_elim fun y => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x08#8 hlt]
      refine step_encChain_encodeVarint img A ext hEV
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
      apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1 img A ext hDR v cap2 ptr2 sp0 (entry + bv% (1932))
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
      refine SepWPpX.exists_elim fun y => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs2 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint img A ext hEV
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

/-! ### Step 3d (`+496 → +552`, cold `1940..1968`): write tag `0x12#8` and call `encode_varint 32#64` -/

theorem step_encChain_seg3_key_tag (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a cap3 ptr3 ckPtr sp0 : BitVec 64) (bs3 : List (BitVec 8))
    (hcur_lt : bs3.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = 32#64)
    (hP : P = ((v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A cap3 ptr3 bs3 ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 552#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = 32#64 →
      sm.readReg64 .x22 = ckPtr →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap4 ptr4 ((bs3 ++ [0x12#8]) ++ encodeVarint 32#64) ∗
          ((a + 80#64) ↦₆₄ ckPtr) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 496 552
  encChain_fetches_range img.base (Rust.withPanics ext) 1940 1968
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have hcur_snoc_lt : (bs3 ++ [0x12#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      ((a + 80#64) ↦₆₄ ckPtr) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : bs3.length < cap3.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs3 0x12#8
    rw [vecU8Buf_eq_open_one A cap3 ptr3 bs3 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap3 ptr3 bs3 0x12#8 hlt]
    refine step_encChain_encodeVarint img A ext hEV
      32#64 v cap3 ptr3 sp0 (entry + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine sepWPp_congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))
  · have hcap_eq : cap3.toNat = bs3.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 img A ext hDR v cap3 ptr3 sp0 (entry + bv% (1960))
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
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs3 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint img A ext hEV
      32#64 v newCap p' sp0 (entry + bv% (552)) (bs3 ++ [0x12#8])
      hcur_snoc_lt
      (x := x) (F := ((a + 80#64) ↦₆₄ ckPtr) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap4 ptr4 hpcm hrunm hspm htrm hcsm
    refine sepWPp_congr_pre (by ac_rfl)
      (hnext sm cap4 ptr4 hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])))

/-! ### Step 3e (`+552 → +600`, cold `1968..2012`): reserve & `memcpy` 32 key bytes -/

theorem step_encChain_seg3_key_copy (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a cap4 ptr4 ckCap ckPtr sp0 : BitVec 64) (bsMid keyBs : List (BitVec 8))
    (hkey_pos : 0 < keyBs.length)
    (hkey_lt : keyBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 552#64)
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
      vecU8Buf A cap4 ptr4 bsMid ∗
      vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap5 ptr5 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap5 ptr5 (bsMid ++ keyBs) ∗
          vecU8Buf A ckCap ckPtr keyBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 552 600
  encChain_fetches_range img.base (Rust.withPanics ext) 1968 2012
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap4) (ptr := ptr4) (bs := bsMid)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A ckCap ckPtr keyBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle4 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := ckCap) (ptr := ckPtr) (bs := keyBs)
    (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap4 ptr4 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hkey_le => ?_
  have hlen_add := bv_len_add_slice bsMid keyBs
  by_cases hfit : bsMid.length + keyBs.length ≤ cap4.toNat
  · have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = false :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).2.mpr hfit
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy img A ext hA cap4 ptr4 ckPtr sp0 (entry + bv% (592))
      bsMid keyBs hkey_pos hfit hkey_lt
      (x := x)
      (F := (v ↦₆₄ cap4) ∗ ((v + 8#64) ↦₆₄ ptr4) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre ?_
      (hnext _ cap4 ptr4 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl
  · have hrem : cap4.toNat - bsMid.length < keyBs.length := by omega
    have hult : (cap4 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 keyBs.length) = true :=
      (spare_ult_iff hle4 hmid_lt hkey_lt).1.mpr hrem
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice img A ext hDR v cap4 ptr4 sp0 (entry + bv% (1992))
      bsMid keyBs.length hle4 hrem hmid_lt hkey_lt
      (x := x)
      (F := vecU8Buf A ckCap ckPtr keyBs ∗ F)
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    refine step_encChain_memcpy img A ext hA newCap p' ckPtr sp0 (entry + bv% (592))
      bsMid keyBs hkey_pos hnew_ge hkey_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A ckCap ckPtr keyBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
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
    apply SepWPpX.of_sepWP (mid := entry + bv% (600))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A ckCap ckPtr keyBs hkey_pos hkey_le]
    ac_rfl

/-! ### Combined Segment 3 (`+0x11c → +0x258`, offsets `284..600`): `chain_key: Option<ChainKey>` -/

theorem step_encChain_seg3 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr sp0 : BitVec 64) (pin : VecPin) (o : Option ChainKey)
    (curBs : List (BitVec 8))
    (hbound : curBs.length + (msgField 3 (o.map encChainKey)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ optChainKeyAt A pin o (a + 72#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 600#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ msgField 3 (o.map encChainKey)) ∗
          optChainKeyAt A pin o (a + 72#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  cases o with
  | none =>
    encChain_fetches_range img.base (Rust.withPanics ext) 284 296
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
    examples_hide_fetches
    rw [optChainKeyAt_none_eq]
    have hnone_beq : (optChainKeyNone + 1#64 == 0#64) = true := rfl
    apply SepWPpX.of_sepWP (mid := entry + bv% (600))
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
    refine sepWPp_extract_vecU8Buf_bounds (A := A) (cap := pin.cap) (ptr := pin.ptr)
      (bs := HMAC.keyToBytes32 ck.key)
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
        vecU8Buf A curCap curPtr curBs ∗
        ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗ memRegion (a + 100#64) 4 ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun _ hck_lt _ => ?_
    refine step_encChain_seg3_write_tag img A ext hDR
      v a curCap curPtr pin.cap sp0 ck.index curBs hck_lt
      (by simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 80#64) ↦₆₄ pin.ptr) ∗ vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    refine step_encChain_seg3_len_varint img A ext hEV
      v a cap1 ptr1 sp0 ck (curBs ++ [0x1a#8])
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2
    refine step_encChain_seg3_index img A ext hEV hDR
      v a cap2 ptr2 sp0 ck.index
      ((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length))
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 80#64) ↦₆₄ pin.ptr) ∗
        ((a + 88#64) ↦₆₄ 32#64) ∗ ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hx21_2 hx22_2 (by ac_rfl) ?_
    intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3
    rw [vecU8At_eq_cells_buf A v cap3 ptr3
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)]
    refine step_encChain_seg3_key_tag img A ext hEV hDR
      v a cap3 ptr3 pin.ptr sp0
      (((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index)
      (by simp only [List.length_append, List.length_singleton]; simp only [Option.map_some] at hbound; omega)
      (x := x)
      (F := ((a + 72#64) ↦₆₄ pin.cap) ∗ ((a + 88#64) ↦₆₄ 32#64) ∗
        ((a + 96#64) ↦₃₂ ck.index) ∗
        vecU8Buf A pin.cap pin.ptr (HMAC.keyToBytes32 ck.key) ∗
        memRegion (a + 100#64) 4 ∗ F)
      hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3 hx21_3 (by ac_rfl) ?_
    intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4
    rw [vecU8At_eq_cells_buf A v cap4 ptr4
      (((((curBs ++ [0x1a#8]) ++ encodeVarint (BitVec.ofNat 64 (encChainKey ck).length)) ++
        uint32Field 1 ck.index) ++ [0x12#8]) ++ encodeVarint 32#64)]
    have hx21_4' : s4.readReg64 .x21 = BitVec.ofNat 64 (HMAC.keyToBytes32 ck.key).length := by
      rw [hkey_len]; exact hx21_4
    refine step_encChain_seg3_key_copy img A ext hA hDR
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
    refine sepWPp_congr_pre ?_ (hnext s5 cap5 ptr5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5)
    rw [hlist, optChainKeyAt_some_eq_encChain A pin ck a]
    ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
