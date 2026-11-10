/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` (`0x4d38`): Stack Budget and Callee Step Lemmas

Defines the callee stack budget `encodeRawSubStackX` below `sp0 - 80` and proves framed callee call
helpers (`do_reserve_and_handle`, `encode_varint`, `encode::<Chain>`, and `memcpy`) inside
`<SessionStructure as prost::Message>::encode_raw` (`0x4d38`, Block `14`) on `SP2Ext` and under
relocatable `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open ProofLib.ProgramReflection
open Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_EncodeRawBaseX : True := trivial

/-! ## Stack budget below `sp0 - 80#64` -/

/-- Callee stack budget below `sp0 - 80#64` (`encodeRawStackX - 0x50`). -/
abbrev encodeRawSubStackX : Nat :=
  Prost.encodeVarintStackX + Proofs.libsignal.Hooks2.doReserveStackX + encodeChainStackX

/-- What is left of `encodeRawSubStackX` after lending a callee `m` bytes. -/
abbrev encRawSubRestX (sp : BitVec 64) (m : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 encodeRawSubStackX) (encodeRawSubStackX - m)

theorem stackAt_encodeRawStackX_split (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStackX =
      stackAt (sp0 - 80#64) encodeRawSubStackX ∗
      cells (sp0 - 80#64) 10 := by
  have htop := encraw_stackAt_split_top sp0 encodeRawSubStackX 80 (by decide)
  change stackAt sp0 encodeRawStackX =
    stackAt (sp0 - 80#64) encodeRawSubStackX ∗ memRegion (sp0 - 80#64) 80 at htop
  rw [htop, show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem stackAt_encodeRawStackX_unfold (sp0 : BitVec 64) :
    stackAt sp0 encodeRawStackX =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        stackAt (sp0 - 80#64) encodeRawSubStackX := by
  rw [stackAt_encodeRawStackX_split sp0, sepConj_comm]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin,
    sepConj_assoc]

theorem encRawSavedRegs_entails_frameX (sp0 : BitVec 64) (s0 : State) (v56 : BitVec 64) :
    stackAt (sp0 - 80#64) encodeRawSubStackX ∗ encRawSavedRegs sp0 s0 v56 ⊢
      stackAt sp0 encodeRawStackX := by
  rw [stackAt_encodeRawStackX_split sp0]
  unfold encRawSavedRegs
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  refine sepConj_mono (Entails.sepExists_intro _) ?_
  exact Entails.sepExists_intro _

theorem stackAt_sub_to_encodeVarint_erX (sp : BitVec 64) :
    stackAt sp encodeRawSubStackX =
      encRawSubRestX sp Prost.encodeVarintStackX ∗ stackAt sp Prost.encodeVarintStackX :=
  stackAt_sub_split_ser sp _ _ (by decide) (by decide)

theorem stackAt_sub_to_doReserve_erX (sp : BitVec 64) :
    stackAt sp encodeRawSubStackX =
      encRawSubRestX sp Proofs.libsignal.Hooks2.doReserveStackX ∗ stackAt sp Proofs.libsignal.Hooks2.doReserveStackX :=
  stackAt_sub_split_ser sp _ _ (by decide) (by decide)

theorem stackAt_sub_to_encodeChainX (sp : BitVec 64) :
    stackAt sp encodeRawSubStackX =
      encRawSubRestX sp encodeChainStackX ∗ stackAt sp encodeChainStackX :=
  stackAt_sub_split_ser sp _ _ (by decide) (by decide)

theorem stackAt_sub_to_memcpy_erX (sp : BitVec 64) :
    stackAt sp encodeRawSubStackX =
      encRawSubRestX sp CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ stackAt sp CryptoVerification.LibsignalTripleRatchet.extHookStack :=
  stackAt_sub_split_ser sp _ _ (by decide) (by decide)

/-! ## Callee address lemmas on `SP2Ext` -/

theorem fnAddr_encraw_add_eq_x (b : BitVec 64) (ext : String → Option (State → State))
    {target : String} {off : BitVec 64}
    (h : BitVec.ofNat 64 (libsignalSessionCode.fnOff encodeRawName) + off =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff target)) :
    (SP2Ext b ext).fnAddr encodeRawName + off = (SP2Ext b ext).fnAddr target := by
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, BitVec.add_assoc, h]

theorem encodeVarint_fnAddr_eq_encraw_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")) =
      (SP2Ext b ext).fnAddr encodeVarintName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeRawName, encodeVarintName, h1, h2]
  bv_lin

theorem doReserve_fnAddr_eq_encraw_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")) =
      (SP2Ext b ext).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeRawName, doReserveName, h1, h2]
  bv_lin

theorem encodeChain_fnAddr_eq_encraw_x (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")) =
      (SP2Ext b ext).fnAddr encodeChainName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")
  have h2 := (ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, encodeRawName, encodeChainName, h1, h2]
  bv_lin

theorem encraw_encodeVarint_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((Prost.encodeVarintSpecX A).inImage img) := by
  rw [encodeVarint_fnAddr_eq_encraw_x]
  exact hEV

theorem encraw_doReserve_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((Proofs.libsignal.Hooks2.doReserveSpecX A).inImage img) := by
  rw [doReserve_fnAddr_eq_encraw_x]
  exact hDR

theorem encraw_encodeChain_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      ((encodeChainSpecX A).inImage img) := by
  rw [encodeChain_fnAddr_eq_encraw_x]
  exact hEC

theorem encraw_memcpy_ok_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  hC.memcpy_ok_at encodeRawName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")) (by
    rw [(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")]; simp only [arm64_norm])

/-! ## In-version composition and extraction helpers -/

theorem encraw_seq_wppIn {img : Obj.Image} {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpIn img prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_frame)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpIn img prog ret sm (P2 ∗ F) Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  have h1' := h1 hF hsym
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hFm := hsteps.frozenLoaded hF
    have hsymm := (hsteps.symtab_eq).trans hsym
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hFm hsymm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem encraw_seq_wppIn' {img : Obj.Image} {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpIn img prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_frame)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpIn img prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  have h1' := h1 hF hsym
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hFm := hsteps.frozenLoaded hF
    have hsymm := (hsteps.symtab_eq).trans hsym
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hFm hsymm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem sepWPpIn_extract_vecU8At_bounds {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)} {P F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecU8At A v cap ptr bs ∗ F := by sep_frame)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWPpIn img prog ret s P Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  intro hF hsym
  exact sepWPp_extract_vecU8At_bounds hfocus fun hle hcap hptr =>
    h hle hcap hptr hF hsym

/-! ## Callee call step helpers in `SepWPpIn` -/

/-- Execute a `bl do_reserve_and_handle` call inside `encode_raw` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_doReserve_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_doReserve_ok_x hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine SepWPpIn.call_inImage (x := DoReserveCall.mk v cap ptr bs add)
    (F := encRawSubRestX (sp0 - 80#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_erX (sp0 - 80#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpIn.exists_elim fun p' => ?_
    refine SepWPpIn.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_erX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode_varint` call inside `encode_raw` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_encodeVarint_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkX img A ext)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeVarint_ok_x hEV
  refine SepWPpIn.call_inImage (x := ⟨val, v, cap, ptr, bs⟩)
    (F := encRawSubRestX (sp0 - 80#64) Prost.encodeVarintStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)] at hm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega)⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [Prost.encodeVarintSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPpIn.exists_elim fun cap' => SepWPpIn.exists_elim fun ptr' => ?_
    refine SepWPpIn.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode::<Chain>` call inside `encode_raw` on `protoChainAt` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_protoEncodeChain_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeChain_ok_x hEC
  refine SepWPpIn.call_inImage (x := ⟨tag, a, gc, v, cap, ptr, bs⟩)
    (F := encRawSubRestX (sp0 - 80#64) encodeChainStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChainX (sp0 - 80#64)] at hm
    simp only [encodeChainSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpIn.exists_elim fun cap' => SepWPpIn.exists_elim fun ptr' => ?_
    refine SepWPpIn.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChainX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode::<Chain>` call inside `encode_raw` on `chainAt` when `s.sp = sp0 - 80#64`. -/
theorem encraw_call_encodeChain_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEC : EncodeChainOkX img A ext)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  refine encraw_call_protoEncodeChain_x hEC tag sp0 a v cap ptr ret_pc gc bs htag hlen_lt
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' hpcm hrunm hspm htrm hcsm

/-- Executes a `bl memcpy` call inside `encode_raw` to copy `payload` into `vecU8At A v cap ptr bs`,
lending `externStack` bytes from `stackAt (sp0 - 80#64) encodeRawSubStackX`. -/
theorem encraw_call_memcpy_x {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload) ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_memcpy_ok_x hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine SepWPpIn.call_inImage (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗
          encRawSubRestX (sp0 - 80#64) CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos,
        stackAt_sub_to_memcpy_erX (sp0 - 80#64)] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hsat
    rw [sepConj_assoc] at hsat
    exact False.elim (not_satisfies_false_sepConj hsat)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_memcpy_erX (sp0 - 80#64)]
    exact (by sep_frame)

/-! ## Relocatable `[LibsignalPlacement]` callee step lemmas (Block `14`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem encraw_encodeVarint_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H) :
    subroutine_ok (lsProg_14 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (Prost.encodeVarintSpecX A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEV

theorem encraw_doReserve_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX A H) :
    subroutine_ok (lsProg_14 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (Proofs.libsignal.Hooks2.doReserveSpecX A)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hDR

theorem encraw_encodeChain_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H) :
    subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecX A)) :=
  ls_subroutine_ok_of_callee (callerProg := lsProg_14 H) hEC

theorem encraw_memcpy_placed_ok_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    subroutine_ok (lsProg_14 H) (lsρ CryptoVerification.lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)) :=
  hC.memcpy (callerProg := lsProg_14 H)

theorem encraw_seq_wppLsCl {pl : MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpLsCl pl prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_frame)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpLsCl pl prog ret sm (P2 ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  have h1' := h1 hcl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hclm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem encraw_seq_wppLsCl' {pl : MultiPlacement} {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (h1 : SepWPpLsCl pl prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (PanicAllocPost s))
    (hfocus : P = P1 ∗ F := by sep_frame)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPpLsCl pl prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  have h1' := h1 hcl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨hpan_s, P_m, hmm, hp⟩ | hoom⟩ :=
    h1' (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ hclm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · have hm' : sm.mem ⊨ (P_m ∗ F) ∗ R := by rw [sepConj_assoc]; exact hmm
    have halloc := hp (F ∗ R) hmm
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using halloc.1
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_s, P_m ∗ F, hm', hpan sm (P_m ∗ F) halloc0⟩)⟩
  · exact (not_satisfies_false_sepConj hoom.2).elim

theorem sepWPpLsCl_extract_vecU8At_bounds {pl : MultiPlacement} {prog : Program}
    {ret : BitVec 64} {s : State} {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfocus : P = vecU8At A v cap ptr bs ∗ F := by sep_frame)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0#64 →
      SepWPpLsCl pl prog ret s P Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  intro hcl
  exact sepWPp_extract_vecU8At_bounds hfocus fun hle hcap hptr =>
    h hle hcap hptr hcl

/-- Execute a `bl do_reserve_and_handle` (`lsmpl.base 13`) call inside `encode_raw` (Block `14`). -/
theorem encraw_call_doReserve_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDR : DoReservePlacedOkX A H)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_doReserve_placed_ok_x hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine SepWPpLsCl.call_withLsCodeLoaded (x := DoReserveCall.mk v cap ptr bs add)
    (F := encRawSubRestX (sp0 - 80#64) Proofs.libsignal.Hooks2.doReserveStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_erX (sp0 - 80#64)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun p' => ?_
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_erX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode_varint` (`lsmpl.base 10`) call inside `encode_raw` (Block `14`). -/
theorem encraw_call_encodeVarint_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEV : EncodeVarintPlacedOkX A H)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeVarint_placed_ok_x hEV
  refine SepWPpLsCl.call_withLsCodeLoaded (x := ⟨val, v, cap, ptr, bs⟩)
    (F := encRawSubRestX (sp0 - 80#64) Prost.encodeVarintStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)] at hm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr (by omega)⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [Prost.encodeVarintSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Prost.encodeVarintSpecX, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun cap' => SepWPpLsCl.exists_elim fun ptr' => ?_
    refine SepWPpLsCl.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeVarint_erX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on `protoChainAt`. -/
theorem encraw_call_protoEncodeChain_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_encodeChain_placed_ok_x hEC
  refine SepWPpLsCl.call_withLsCodeLoaded (x := ⟨tag, a, gc, v, cap, ptr, bs⟩)
    (F := encRawSubRestX (sp0 - 80#64) encodeChainStackX ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChainX (sp0 - 80#64)] at hm
    simp only [encodeChainSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ R' hm
    simp only [encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpLsCl.exists_elim fun cap' => SepWPpLsCl.exists_elim fun ptr' => ?_
    refine SepWPpLsCl.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_encodeChainX (sp0 - 80#64)]
    exact (by sep_frame)

/-- Execute a `bl encode::<Chain>` (`lsmpl.base 12`) call inside `encode_raw` on `chainAt`. -/
theorem encraw_call_encodeChain_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hEC : EncodeChainPlacedOkX A H)
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (protoChainAt A gc a ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  refine encraw_call_protoEncodeChain_placed_x hEC tag sp0 a v cap ptr ret_pc gc bs htag hlen_lt
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
  have hPostEq :
      ((protoChainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A gc a ∗ vecU8At A v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A gc a]; ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' hpcm hrunm hspm htrm hcsm

/-- Execute a `bl memcpy` (`lsρ lsMemcpySym`) call inside `encode_raw` (Block `14`). -/
theorem encraw_call_memcpy_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (sp0 v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsρ CryptoVerification.lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗
      stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F := by sep_frame)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_14 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload) ∗ stackAt (sp0 - 80#64) encodeRawSubStackX) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpLsCl lsmpl (lsProg_14 H) ret s P Q (PanicAllocPost s0) := by
  have hcall := encraw_memcpy_placed_ok_x hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine SepWPpLsCl.call_withLsCl (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗
          encRawSubRestX (sp0 - 80#64) CryptoVerification.LibsignalTripleRatchet.extHookStack ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos,
        stackAt_sub_to_memcpy_erX (sp0 - 80#64)] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (by sep_frame) hm
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ R' hsat
    rw [sepConj_assoc] at hsat
    exact False.elim (not_satisfies_false_sepConj hsat)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpLsCl.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm' hcsm)
    rw [stackAt_sub_to_memcpy_erX (sp0 - 80#64)]
    exact (by sep_frame)

end Placed

end CryptoVerification.E2E.Record.Serialization
