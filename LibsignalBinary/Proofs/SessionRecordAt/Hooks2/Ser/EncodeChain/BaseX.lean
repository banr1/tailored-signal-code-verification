/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>` (`0x44b0`): Stack Budget and Callee Step Lemmas

Defines the callee stack budget `encChainSubStackX` below `sp0 - 96` and proves framed callee step
lemmas (`encode_varint`, `do_reserve_and_handle`, and `memcpy`) for
`prost::encoding::message::encode::<Chain, Vec<u8>>` (`0x44b0`, Block `12`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_EncodeChainBaseX : True := trivial

/-! ## Stack budget below `sp0 - 96` -/

/-- Callee stack budget below `sp0 - 96#64` (`encodeChainStackX - 0x60`). -/
abbrev encChainSubStackX : Nat := Prost.encodeVarintStackX + Proofs.libsignal.Hooks2.doReserveStackX + chainLenStack

/-- What is left of `encChainSubStackX` after lending a callee `m` bytes. -/
abbrev encChainSubRestX (sp : BitVec 64) (m : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 encChainSubStackX) (encChainSubStackX - m)

theorem stackAt_encodeChainStackX_split (sp0 : BitVec 64) :
    stackAt sp0 encodeChainStackX =
      stackAt (sp0 - 96#64) encChainSubStackX ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : encodeChainStackX = encChainSubStackX + 8 * 12 := by decide
  rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 encChainSubStackX 12 (by decide)]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem stackAt_encChainSubX_split (sp : BitVec 64) (m : Nat) (hm : m ≤ encChainSubStackX) :
    stackAt sp encChainSubStackX = encChainSubRestX sp m ∗ stackAt sp m :=
  stackAt_sub_split_ser sp m encChainSubStackX hm (by decide)

theorem stackAt_sub_to_encodeVarintX (sp : BitVec 64) :
    stackAt sp encChainSubStackX =
      encChainSubRestX sp Prost.encodeVarintStackX ∗ stackAt sp Prost.encodeVarintStackX :=
  stackAt_encChainSubX_split sp _ (by decide)

theorem stackAt_sub_to_doReserveX (sp : BitVec 64) :
    stackAt sp encChainSubStackX = encChainSubRestX sp Proofs.libsignal.Hooks2.doReserveStackX ∗ stackAt sp Proofs.libsignal.Hooks2.doReserveStackX :=
  stackAt_encChainSubX_split sp _ (by decide)

theorem stackAt_sub_to_chainLenX (sp : BitVec 64) :
    stackAt sp encChainSubStackX = encChainSubRestX sp chainLenStack ∗ stackAt sp chainLenStack :=
  stackAt_encChainSubX_split sp _ (by decide)

theorem stackAt_sub_to_msgKeyLenX (sp : BitVec 64) :
    stackAt sp encChainSubStackX = encChainSubRestX sp msgKeyLenStack ∗ stackAt sp msgKeyLenStack :=
  stackAt_encChainSubX_split sp _ (by decide)

theorem stackAt_sub_to_memcpyX (sp : BitVec 64) :
    stackAt sp encChainSubStackX = encChainSubRestX sp CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack :=
  stackAt_encChainSubX_split sp _ (by decide)

/-! ## Callee offsets on `SP2Ext` -/

theorem encodeVarint_fnAddr_eq_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) =
      (SP2Ext b ext).fnAddr encodeVarintName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeChainName, encodeVarintName, h1, h2]
  bv_lin

theorem chainLen_fnAddr_eq_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") = (SP2Ext b ext).fnAddr chainLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeChainName, chainLenName, h1, h2]
  bv_lin

theorem msgKeyLen_fnAddr_eq_encChain_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") = (SP2Ext b ext).fnAddr msgKeyLenName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeChainName, msgKeyLenName, h1, h2]
  bv_lin

theorem doReserve_fnAddr_eq_encChain_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") = (SP2Ext b ext).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeChainName, doReserveName, h1, h2]
  bv_lin

/-- The `bl memcpy` sites of `encode::<Chain>` (one stub, caller-relative offset). -/
theorem encChain_memcpy_ok_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  hC.memcpy_ok_at encodeChainName (num% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) (by
    rw [(ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")]; simp only [arm64_norm])

/-! ## Callee step lemmas on `SP2Ext` -/

/-- Step a `bl encode_varint` (`entry + relOff`) call inside `encode::<Chain>`. -/
theorem step_encChain_encodeVarint_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image} (hEV : EncodeVarintOkX img A ext)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [encodeVarint_fnAddr_eq_x] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpIn.call_inImage (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := encChainSubRestX (sp0 - 96#64) Prost.encodeVarintStackX ∗ F)
    hEV hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarintX (sp0 - 96#64)] at hm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega)⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Prost.encodeVarintSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPpIn.exists_elim fun cap' => SepWPpIn.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc]
    refine SepWPpIn.pure_elim fun _ => ?_
    refine SepWPpIn.congr_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm)
    rw [stackAt_sub_to_encodeVarintX (sp0 - 96#64)]
    ac_rfl

/-- Step a 1-byte `bl do_reserve_and_handle` (`entry + 2044#64`) call inside `encode::<Chain>`. -/
theorem step_encChain_reserve1_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image} (hDR : DoReserveOkX img A ext)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          Prost.vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain_x] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPpIn.call_inImage (x := DoReserveCall.mk v curCap curPtr curBs 1)
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpIn.pure_elim fun htrm => ?_
    refine SepWPpIn.congr_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt)
    rw [stackAt_sub_to_doReserveX (sp0 - 96#64)]
    ac_rfl

/-- Step a slice `bl do_reserve_and_handle` (`entry + 2044#64`) call inside `encode::<Chain>`. -/
theorem step_encChain_reserveSlice_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image} (hDR : DoReserveOkX img A ext)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          Prost.vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain_x] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpIn.call_inImage (x := DoReserveCall.mk v curCap curPtr curBs add)
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpIn.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpIn.pure_elim fun htrm => ?_
    refine SepWPpIn.congr_pre ?_
      (hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
        hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false)
    rw [stackAt_sub_to_doReserveX (sp0 - 96#64)]
    ac_rfl

/-- Steps a `bl memcpy` (`entry + 277152#64`) call inside `encode::<Chain>`, lending `externStack`
bytes from `stackAt (sp0 - 96#64) encChainSubStackX`. -/
theorem step_encChain_memcpy_x (A : RustAlloc) (ext : String → Option (State → State))
    {img : Obj.Image} (hC : SerContractsX img A ext)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeChainName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (Prost.vecU8Buf A curCap curPtr curBs ∗ (srcPtr ↦ₛ sliceBs) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((Prost.vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpIn.call_inImage (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗
      encChainSubRestX (sp0 - 96#64) CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ F)
    (encChain_memcpy_ok_x hC) hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle,
      stackAt_sub_to_memcpyX (sp0 - 96#64)] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    simp only [sessionMemcpySpec] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [sessionMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPpIn.congr_pre ?_ (hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm)
    rw [stackAt_sub_to_memcpyX (sp0 - 96#64),
      ← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle]
    ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` callee step lemmas (Block `12`) -/

section Placed

open CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Step a `bl encode_varint` (`lsmpl.base 10`) call inside `encode::<Chain>` (Block `12`). -/
theorem step_encChain_encodeVarint_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (hEV : EncodeVarintPlacedOkX A H)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hEV' : subroutine_ok (lsProg_12 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpecX A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hEV
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpLsCl.call_withLsCodeLoaded (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := encChainSubRestX (sp0 - 96#64) Prost.encodeVarintStackX ∗ F)
    hEV' hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarintX (sp0 - 96#64)] at hm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega)⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Prost.encodeVarintSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPpLsCl.exists_elim fun cap' => SepWPpLsCl.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun _ => ?_
    refine SepWPpLsCl.congr_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm)
    rw [stackAt_sub_to_encodeVarintX (sp0 - 96#64)]
    ac_rfl

/-- Step a 1-byte `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode::<Chain>` (Block `12`). -/
theorem step_encChain_reserve1_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (hDR : DoReservePlacedOkX A H)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          Prost.vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPpLsCl.call_withLsCodeLoaded (x := DoReserveCall.mk v curCap curPtr curBs 1)
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR' hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    refine SepWPpLsCl.congr_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt)
    rw [stackAt_sub_to_doReserveX (sp0 - 96#64)]
    ac_rfl

/-- Step a slice `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode::<Chain>` (Block `12`). -/
theorem step_encChain_reserveSlice_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (hDR : DoReservePlacedOkX A H)
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      Prost.vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          Prost.vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpLsCl.call_withLsCodeLoaded (x := DoReserveCall.mk v curCap curPtr curBs add)
    (F := encChainSubRestX (sp0 - 96#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hDR' hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserveX (sp0 - 96#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, Prost.vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    refine SepWPpLsCl.congr_pre ?_
      (hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
        hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false)
    rw [stackAt_sub_to_doReserveX (sp0 - 96#64)]
    ac_rfl

/-- Step a `bl memcpy` (`lsρ lsMemcpySym`) call inside `encode::<Chain>` (Block `12`). -/
theorem step_encChain_memcpy_placed_x [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (hC : SerContractsXPlaced A H)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (Prost.vecU8Buf A curCap curPtr curBs ∗ (srcPtr ↦ₛ sliceBs) ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((Prost.vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)) :=
    hC.memcpy (callerProg := lsProg_12 H)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpLsCl.call_withLsCl (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗
      encChainSubRestX (sp0 - 96#64) CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ F)
    hmc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle,
      stackAt_sub_to_memcpyX (sp0 - 96#64)] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    simp only [sessionMemcpySpec] at hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [sessionMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPpLsCl.congr_pre ?_ (hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm)
    rw [stackAt_sub_to_memcpyX (sp0 - 96#64),
      ← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle]
    ac_rfl

end Placed

end CryptoVerification.E2E.Record.Serialization
