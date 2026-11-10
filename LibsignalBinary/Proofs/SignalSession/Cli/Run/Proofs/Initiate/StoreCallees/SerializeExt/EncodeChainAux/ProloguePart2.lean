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

/-!
# `encode::<Chain, Vec<u8>>`: Segments 1 (`sender_ratchet_key`) and 2 (`sender_ratchet_key_private`)
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
  sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Combined Segment 1 (`+0x044 → +0x0b0`, offsets `68..176`): appends `bytesField 1 srk.bytes`. -/
theorem step_encChain_seg1 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : srk.bytes = []
  · encChain_fetches_range img.base (Rust.withPanics ext) 68 72
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
    examples_hide_fetches
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply SepWPpX.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length + srk.bytes.length =
        (bytesField 1 srk.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag img A ext hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy img A ext hA hDR
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes) ∗
          vecU8Buf A srk.cap srk.ptr srk.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

/-! ### Segment 2 (`+0x0b0 → +0x11c`, offsets `176..284`, cold `1780..1848`): `sender_ratchet_key_private` -/

theorem vecU8At_add24_eq_cells_buf (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (a + 24#64) cap ptr bs =
      ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦₆₄ ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [vecU8At_eq_cells_buf, h32, h40]

theorem step_encChain_seg2_tag (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr privPtr sp0 : BitVec 64) (curBs privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 236#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length →
      sm.readReg64 .x22 = privPtr →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 176 232
  encChain_fetches_range img.base (Rust.withPanics ext) 1780 1804
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hpriv_nz := bv_ofNat_beq_zero_false hpriv_pos hpriv_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x12#8 hlt]
    refine step_encChain_encodeVarint img A ext hEV
      (BitVec.ofNat 64 privBs.length) v curCap curPtr sp0 (entry + bv% (236)) (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 img A ext hDR v curCap curPtr sp0 (entry + bv% (1800))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun y => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint img A ext hEV
      (BitVec.ofNat 64 privBs.length) v newCap p' sp0 (entry + bv% (236)) (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg2_copy (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a cap2 ptr2 privCap privPtr sp0 : BitVec 64) (bsMid privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 privBs.length)
    (hx22 : s.readReg64 .x22 = privPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range img.base (Rust.withPanics ext) 236 280
  encChain_fetches_range img.base (Rust.withPanics ext) 1808 1848
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := privCap) (ptr := privPtr) (bs := privBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hpriv_le => ?_
  have hlen_add := bv_len_add_slice bsMid privBs
  by_cases hfit : bsMid.length + privBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).2.mpr hfit
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy img A ext hA cap2 ptr2 privPtr sp0 (entry + bv% (276))
      bsMid privBs hpriv_pos hfit hpriv_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < privBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).1.mpr hrem
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice img A ext hDR v cap2 ptr2 sp0 (entry + bv% (1832))
      bsMid privBs.length hle2 hrem hmid_lt hpriv_lt
      (x := x)
      (F := vecU8Buf A privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy img A ext hA newCap p' privPtr sp0 (entry + bv% (276))
      bsMid privBs hpriv_pos hnew_ge hpriv_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPpX.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

/-- Combined Segment 2 (`+0x0b0 → +0x11c`, offsets `176..284`): appends `bytesField 2 priv.bytes`. -/
theorem step_encChain_seg2 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v a curCap curPtr sp0 : BitVec 64) (priv : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 2 priv.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A priv (a + 24#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : priv.bytes = []
  · encChain_fetches_range img.base (Rust.withPanics ext) 176 180
    generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName = entry
    examples_hide_fetches
    unfold vecGhostAt
    rw [vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    have hlen0 : BitVec.ofNat 64 priv.bytes.length = 0#64 := by simp [hnil]
    apply SepWPpX.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 2 priv.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hpriv_pos : 0 < priv.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x12#8] ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length) ++ priv.bytes =
        bytesField 2 priv.bytes :=
      bytesField_nonempty_eq 2 0x12#8 priv.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length + priv.bytes.length =
        (bytesField 2 priv.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 priv.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    refine step_encChain_seg2_tag img A ext hEV hDR
      v a curCap curPtr priv.ptr sp0 curBs priv.bytes
      hpriv_pos (by omega) (by omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ vecU8Buf A priv.cap priv.ptr priv.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length))]
    refine step_encChain_seg2_copy img A ext hA hDR
      v a cap2 ptr2 priv.cap priv.ptr sp0
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) priv.bytes
      hpriv_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes =
        curBs ++ bytesField 2 priv.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes) ∗
          vecU8Buf A priv.cap priv.ptr priv.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
