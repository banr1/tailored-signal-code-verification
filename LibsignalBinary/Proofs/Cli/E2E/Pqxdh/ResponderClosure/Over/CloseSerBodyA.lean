/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.PrologueVersionLocalIdentity
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeRaw.BaseX
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `SessionRecord::serialize` with One Previous Session: Field-2 Proof

Proves `serField2_step : SerField2StepStmt img A ext` (`+444 .. +692`), encoding `previous_sessions`
field 2 (`0x12`, varint length, and raw `enc` bytes) from `DoReserveOkX` and `EncodeVarintOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux
open Proofs.libsignal.Hooks2

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Instruction decodes (`+444 .. +664`) -/

gen_decodes libsignalSessionCode_tree serF2Bin
  [(ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 444) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize" + 664)]

/-! ## Arithmetic and alignment helpers -/

theorem sf2_sp_aligned {sp0 : BitVec 64} {s : State}
    (hsp0 : sp0 &&& 15#64 = 0#64) (hsp : s.sp = sp0 - 800#64) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hsp0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem SerField2Saved.refl (s : State) : SerField2Saved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SerField2Saved.trans {s0 s1 s2 : State}
    (h1 : SerField2Saved s0 s1) (h2 : SerField2Saved s1 s2) : SerField2Saved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.trans h1.2.2.2.2.2⟩

theorem SerField2Saved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) : SerField2Saved s1 s2 := by
  unfold SerField2Saved
  reg_chain

theorem sf2_doReserve_fnAddr (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName +
        bv% (2 ^ 64 +
          (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) =
      (SP2Ext b ext).fnAddr doReserveName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::serialize")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]")
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, serializeName, doReserveName, h1, h2]
  rw [BitVec.add_assoc]; rfl

theorem sf2_lt_of_ofNat {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sf2_cap_beq_len_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (cap == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hn : n < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
  omega

theorem sf2_cap_eq_ofNat_len {cap : BitVec 64} {n : Nat} (heq : cap.toNat = n) :
    cap = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (heq ▸ cap.isLt)]

theorem sf2_lenField_two (enc : List (BitVec 8)) :
    CryptoVerification.E2E.Record.lenField 2 enc =
      [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc := by
  unfold CryptoVerification.E2E.Record.lenField
  rfl

/-! ## Frame-specialized callee steps -/

/-- `bl do_reserve_and_handle` from `serialize` with `sp = sp0 - 800`. -/
theorem sf2_call_doReserve {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDR : DoReserveOkX img A ext)
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f, PanicAllocPost s0 sf P_f → Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName +
      bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  have hcall : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName +
        bv% (2 ^ 64 +
          (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      ((Proofs.libsignal.Hooks2.doReserveSpecX A).inImage img) := by
    rw [sf2_doReserve_fnAddr]; exact hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine SepWPpIn.call_inImage (x := DoReserveCall.mk v cap ptr bs add)
    (F := memRegion (sp0 - 800#64 - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Hooks2.doReserveStackX) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_serializeSub_splitX (sp0 - 800#64) Proofs.libsignal.Hooks2.doReserveStackX
      (by decide)] at hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_frame
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _
    apply hQp
    intro R' hm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [Proofs.libsignal.Hooks2.doReserveSpecX, hsp, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPpIn.exists_elim fun p' => ?_
    refine SepWPpIn.pure_elim fun htrm => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
      hpcm hrunm hspm htrm' hcsm hnew_ge hnew_lt)
    rw [stackAt_serializeSub_splitX (sp0 - 800#64) Proofs.libsignal.Hooks2.doReserveStackX
      (by decide)]
    exact entails_of_sep_focus (by sep_frame)

/-- `bl encode_varint` from `serialize` with `sp = sp0 - 800`. -/
theorem sf2_call_encodeVarint {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkX img A ext)
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f, PanicAllocPost s0 sf P_f → Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName +
      bv% (2 ^ 64 +
        (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A v cap' ptr' (bs ++ encodeVarint val) ∗ A.pool ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  have hcall := encodeVarint_sub_okX hEV
  refine SepWPpIn.call_inImage (x := ⟨val, v, cap, ptr, bs⟩) (F := F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [encodeVarintSubSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen_lt⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_frame
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _
    apply hQp
    intro R' hm
    simp only [encodeVarintSubSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSubSpecX, hsp, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPpIn.exists_elim fun cap' => SepWPpIn.exists_elim fun ptr' => ?_
    refine SepWPpIn.pure_elim fun htrm => ?_
    refine SepWPpIn.pure_elim fun _ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm' hcsm)
    exact entails_of_sep_focus (by sep_frame)

/-- `bl memcpy` from `serialize` with `sp = sp0 - 800`, copying `payload` into the spare capacity
of `vecU8At A v cap ptr bs`. -/
theorem sf2_call_memcpy {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (sp0 v v8 v16 cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (h8 : v + 8#64 = v8) (h16 : v + 16#64 = v16)
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f, PanicAllocPost s0 sf P_f → Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName +
      bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        (((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecCopyDone A cap ptr bs payload ∗ (srcPtr ↦ₛ payload) ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s P Q Qp := by
  subst h8 h16
  have hcall := memcpy_sub_okX hC
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  have hexp := vecU8At_expose_slice A v cap ptr bs payload.length hle hcap hptr hpos
  rw [vecU8At_eq_header_sep_buf] at hexp
  refine SepWPpIn.call_inImage (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length)) ∗ F)
    hcall hpc hrun halign hlr ?_ ?_ ?_ ?_
  · intro R' hm
    have hbuf : (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs =
        vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
      simp only [vecHeader, sepConj_assoc]
    rw [hP] at hm
    have hm' : s.mem ⊨ ((vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs) ∗
        (srcPtr ↦ₛ payload) ∗ stackAt (sp0 - 800#64) serializeSubStackX ∗ F) ∗ R' := by
      apply satisfies_of_sep_focus hm
      rw [← hbuf]
      sep_frame
    rw [hexp] at hm'
    simp only [memcpySubSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm'
    sep_frame
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _
    apply hQp
    intro R' hsat
    simp only [memcpySubSpecX] at hsat
    rw [sepConj_assoc] at hsat
    exact False.elim (not_satisfies_false_sepConj hsat)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [memcpySubSpecX, hsp, sepConj_assoc]
    refine SepWPpIn.pure_elim fun ⟨_, htrm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPpIn.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm' hcsm)
    unfold vecCopyDone
    have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧
        payload ≠ []) = True := eq_true ⟨hle, hcap, hptr, hne⟩
    rw [hpure, pure_true, emp_sepConj]
    exact entails_of_sep_focus (by sep_frame)

/-! ## Output vector header at `sp0 - 432` -/

theorem sf2_off8 (sp0 : BitVec 64) : sp0 - 432#64 + 8#64 = sp0 - 424#64 :=
  bv_sub_add_lit sp0 432 8

theorem sf2_off16 (sp0 : BitVec 64) : sp0 - 432#64 + 16#64 = sp0 - 416#64 :=
  bv_sub_add_lit sp0 432 16

theorem sf2_vec432_eq (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp0 - 432#64) cap ptr bs =
      ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, ← sf2_off8, ← sf2_off16]
  simp only [vecHeader, sepConj_assoc]

theorem sf2_vec432_open_one (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A (sp0 - 432#64) cap ptr bs =
      ∃∗ y : BitVec 8,
        ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  rw [vecU8At_open_one A (sp0 - 432#64) cap ptr bs hlt, sf2_off8, sf2_off16]

theorem sf2_vec432_close_one (A : RustAlloc) (sp0 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) (R : SepProp) :
    ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
      ((sp0 - 416#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs ∗ R =
      vecU8At A (sp0 - 432#64) cap ptr (bs ++ [byte]) ∗ R := by
  rw [← vecU8At_close_one A (sp0 - 432#64) cap ptr bs byte hlt R, sf2_off8, sf2_off16]

theorem sf2_vec432_slice_eq (A : RustAlloc) (sp0 cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ []) :
    vecU8At A (sp0 - 432#64) cap ptr (bs ++ payload) =
      ((sp0 - 432#64) ↦₆₄ cap) ∗ ((sp0 - 424#64) ↦₆₄ ptr) ∗
        ((sp0 - 416#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
        vecCopyDone A cap ptr bs payload := by
  have h := vecU8At_close_slice A (sp0 - 432#64) cap ptr bs payload hle hcap hptr hne emp
  simp only [sepConj_emp] at h
  rw [sf2_off8, sf2_off16] at h
  exact h.symm

/-! ## Payload copy and loop exit (`+472 .. +692`) -/

set_option maxHeartbeats 400000 in
theorem sf2_copy {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs1 enc fin : List (BitVec 8))
    (hfin : fin = bs1 ++ enc)
    (henc : enc ≠ [])
    (hleE : enc.length ≤ capE.toNat)
    (hfit : bs1.length + enc.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hlen : bs1.length + enc.length < 2 ^ 61)
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f,
      CryptoVerification.E2E.Record.Serialization.EncodeRawAux.PanicAllocPost s0 sf P_f →
        Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (472))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs1.length)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (sp0 - 432#64) cap' ptr' fin ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s
      ((vecU8At A (sp0 - 432#64) cap ptr bs1 ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q Qp := by
  subst hfin
  have hCallMC := @sf2_call_memcpy img A ext hC
  have hfn := libsignalSessionCode_fnOff_serialize
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 472 40
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  have henc_nat : (BitVec.ofNat 64 enc.length).toNat = enc.length := sf2_lt_of_ofNat (by omega)
  rw [sf2_vec432_eq, vecU8At_open_src A q' capE ptrE enc henc hleE]
  simp only [sepConj_assoc]
  apply SepWPpIn.of_sepWP
    (mid := entry + bv% (ls_off% "memcpy" -
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine hCallMC sp0 (sp0 - 432#64) (sp0 - 424#64) (sp0 - 416#64) cap ptr ptrE
    (entry + bv% (492)) bs1 enc (sf2_off8 sp0) (sf2_off16 sp0) hfit hcap hptr henc hQp
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (F := (q' ↦₆₄ capE) ∗ ((q' + 8#64) ↦₆₄ ptrE) ∗
      ((q' + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecSrcRest A capE ptrE enc ∗ A.pool ∗ F)
    (by sep_frame) ?_
  · simp only [arm64_norm]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · exact sf2_sp_aligned halign (by simp only [arm64_norm, *])
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · intro sm hpcm hrunm hspm htrm hcsm
    have hx20m : sm.readReg64 .x20 = BitVec.ofNat 64 bs1.length := by
      have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
      have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx25m : sm.readReg64 .x25 = 24#64 := by
      have := hcsm.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hsvm : SerField2Saved sI sm :=
      (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
        (SerField2Saved.of_calleeSavedPreserved hcsm)
    have hspm' : sm.sp = sp0 - 800#64 := hspm
    apply SepWPpIn.of_sepWP (mid := entry + bv% (692))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_ (hnext _ cap ptr
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hsvm.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])))
    rw [sf2_vec432_slice_eq A sp0 cap ptr bs1 enc hfit hcap hptr henc,
      vecU8At_open_src A q' capE ptrE enc henc hleE]
    exact entails_of_sep_focus (by sep_frame)

/-! ## Post-`encode_varint` segment (`+556 .. +692`) -/

set_option maxHeartbeats 400000 in
theorem sf2_after_varint {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs1 enc : List (BitVec 8))
    (hleE : enc.length ≤ capE.toNat)
    (hlen : bs1.length + enc.length < 2 ^ 61)
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f,
      CryptoVerification.E2E.Record.Serialization.EncodeRawAux.PanicAllocPost s0 sf P_f →
        Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (556))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (sp0 - 432#64) cap' ptr' (bs1 ++ enc) ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
          stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s
      ((vecU8At A (sp0 - 432#64) cap ptr bs1 ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q Qp := by
  have hCopy := @sf2_copy img A ext hC
  have hDRc := @sf2_call_doReserve img A ext hDR
  have hfn := libsignalSessionCode_fnOff_serialize
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 556 28
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 500 12
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 616 24
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 640 20
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := sp0 - 432#64) (cap := cap) (ptr := ptr)
    (bs := bs1) (h := fun hle1 hcap1 hptr1 => ?_)
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := sf2_lt_of_ofNat (by omega)
  have henc_nat : (BitVec.ofNat 64 enc.length).toNat = enc.length := sf2_lt_of_ofNat (by omega)
  by_cases hfit : bs1.length + enc.length ≤ cap.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    by_cases henc : enc = []
    · subst henc
      simp only [List.length_nil, Nat.add_zero] at hhi hx21
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (692))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpIn.weaken_pre ?_ (hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])))
      rw [List.append_nil, sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
    · have hbeq0 : (BitVec.ofNat 64 enc.length == 0#64) = false :=
        ofNat64_len_beq_zero_false henc (by omega)
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (472))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpIn.weaken_pre ?_ (hCopy sp0 q' cap ptr capE ptrE bs1 enc (bs1 ++ enc) rfl
        henc hleE hfit hcap1 hptr1 hlen (sI := sI) (F := F) hQp
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])) hnext)
      rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
  · have hnfit : cap.toNat < bs1.length + enc.length := by omega
    have henc : enc ≠ [] := by
      intro h; subst h; simp only [List.length_nil, Nat.add_zero] at hnfit; omega
    have hhi := cmp_hi_true_of_gt (add := enc.length) hle1 hnfit hcap1 (by omega)
    rw [sf2_vec432_eq]
    simp only [sepConj_assoc]
    apply SepWPpIn.of_sepWP
      (mid := entry + bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_ (hDRc sp0 (sp0 - 432#64) cap ptr (entry + bv% (640)) bs1
      enc.length (by omega) (by omega) (F := vecU8At A q' capE ptrE enc ∗ F) hQp
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) rfl ?_)
    · rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)
    · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = ptrE := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx25_1 : s1.readReg64 .x25 = 24#64 := by
        have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hsv1 : SerField2Saved sI s1 :=
        (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
          (SerField2Saved.of_calleeSavedPreserved hcs1)
      have hls := cmp_ls_true_of_le hnew_ge hnew_lt
      refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := sp0 - 432#64) (cap := newCap)
        (ptr := p') (bs := bs1) (h := fun _ _ hp'_ne => ?_)
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (472))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpIn.weaken_pre ?_ (hCopy sp0 q' newCap p' capE ptrE bs1 enc (bs1 ++ enc) rfl
        henc hleE hnew_ge hnew_lt hp'_ne hlen (sI := sI) (F := F) hQp
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hsv1.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])) hnext)
      rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)

/-! ## Key byte `0x12` and `encode_varint` (`+528 .. +692`) -/

set_option maxHeartbeats 400000 in
theorem sf2_tag {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (hEV : EncodeVarintOkX img A ext)
    (sp0 q' cap ptr capE ptrE : BitVec 64) (bs enc : List (BitVec 8))
    (hleE : enc.length ≤ capE.toNat)
    (hlt : bs.length < cap.toNat)
    (hlen : bs.length + 11 + enc.length < 2 ^ 61)
    {ret : BitVec 64} {s0 sI s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hQp : ∀ sf P_f,
      CryptoVerification.E2E.Record.Serialization.EncodeRawAux.PanicAllocPost s0 sf P_f →
        Qp sf P_f)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (528))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 800#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 bs.length)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 enc.length)
    (hx22 : s.readReg64 .x22 = ptrE)
    (hx25 : s.readReg64 .x25 = 24#64)
    (hx27 : s.readReg64 .x27 = 18#64)
    (hsv : SerField2Saved sI s)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (SP2Ext img.base ext).fnAddr serializeName + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved sI sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (sp0 - 432#64) cap' ptr'
            (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc) ∗
          vecU8At A q' capE ptrE enc ∗ A.pool ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp) :
    SepWPpIn img (SP2Ext img.base ext) ret s
      ((vecU8At A (sp0 - 432#64) cap ptr bs ∗ vecU8At A q' capE ptrE enc ∗ A.pool ∗
        stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
      Q Qp := by
  have hAfter := @sf2_after_varint img A ext hC hDR
  have hEVc := @sf2_call_encodeVarint img A ext hEV
  have hfn := libsignalSessionCode_fnOff_serialize
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 528 28
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  have hbs_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := sf2_lt_of_ofNat (by omega)
  rw [sf2_vec432_open_one A sp0 cap ptr bs hlt]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPpIn.exists_elim fun old => ?_
  apply SepWPpIn.of_sepWP
    (mid := entry + bv% (2 ^ 64 +
      (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") -
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [sf2_vec432_close_one A sp0 cap ptr bs 0x12#8 hlt]
  refine hEVc sp0 (BitVec.ofNat 64 enc.length) (sp0 - 432#64) cap ptr (entry + bv% (556))
    (bs ++ [0x12#8]) (by simp only [List.length_append, List.length_singleton]; omega)
    (F := vecU8At A q' capE ptrE enc ∗ F) hQp
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_frame) ?_
  · simp only [arm64_norm]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · exact sf2_sp_aligned halign (by simp only [arm64_norm, *])
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · simp only [arm64_norm, *]
  · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
    have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
      have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx22_1 : s1.readReg64 .x22 = ptrE := by
      have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hx25_1 : s1.readReg64 .x25 = 24#64 := by
      have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
    have hsv1 : SerField2Saved sI s1 :=
      (hsv.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])).trans
        (SerField2Saved.of_calleeSavedPreserved hcs1)
    have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 enc.length)
    refine SepWPpIn.weaken_pre ?_ (hAfter sp0 q' cap1 ptr1 capE ptrE
      (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length)) enc hleE
      (by simp only [List.length_append, List.length_singleton]; omega)
      (sI := sI) (F := F) hQp hpc1 hrun1 hsp1 halign htr1 hx21_1 hx22_1 hx25_1 hsv1 hnext)
    exact entails_of_sep_focus (by sep_frame)

/-! ## Field-2 step (`+444 .. +692`) -/

set_option maxHeartbeats 400000 in
/-- Encodes field 2 (`0x12`, varint length, and `enc` bytes) of `<SessionRecord>::serialize` across
`+444 .. +692`. -/
theorem serField2_step {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext)
    (hDR : DoReserveOkX img A ext)
    (hEV : EncodeVarintOkX img A ext) :
    SerField2StepStmt img A ext := by
  intro sp0 q' cap ptr capE ptrE bs enc ret s0 s P F Q Qp hQp hlen32 hpc hrun hsp halign htr
    hx22 hx25 hP hnext
  have hTag := @sf2_tag img A ext hC hDR hEV
  have hDRc := @sf2_call_doReserve img A ext hDR
  have hfn := libsignalSessionCode_fnOff_serialize
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 444 28
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 512 16
  code_fetches_from CryptoVerification.libsignalSessionCode serF2Bin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) 584 32
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr serializeName = entry
  examples_hide_fetches
  subst hP
  have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 enc.length)
  have hlf := sf2_lenField_two enc
  have hlflen : (CryptoVerification.E2E.Record.lenField 2 enc).length =
      1 + (encodeVarint (BitVec.ofNat 64 enc.length)).length + enc.length := by
    rw [hlf]; simp only [List.length_append, List.length_singleton]
  have hlen : bs.length + 11 + enc.length < 2 ^ 61 := by omega
  have hnext' : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = entry + bv% (692) →
      sm.status = .Running →
      sm.sp = sp0 - 800#64 →
      sm.trace = s0.trace →
      SerField2Saved s sm →
      SepWPpIn img (SP2Ext img.base ext) ret sm
        ((vecU8At A (sp0 - 432#64) cap' ptr'
            (bs ++ [0x12#8] ++ encodeVarint (BitVec.ofNat 64 enc.length) ++ enc) ∗
          vecU8At A q' capE ptrE enc ∗ A.pool ∗ stackAt (sp0 - 800#64) serializeSubStackX) ∗ F)
        Q Qp := by
    intro sm cap' ptr' h1 h2 h3 h4 h5
    have h := hnext sm cap' ptr' h1 h2 h3 h4 h5
    rw [hlf] at h
    simpa only [List.append_assoc] using h
  refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := sp0 - 432#64) (cap := cap) (ptr := ptr)
    (bs := bs) (h := fun hle1 hcap1 hptr1 => ?_)
  refine sepWPpIn_extract_vecU8At_bounds (A := A) (v := q') (cap := capE) (ptr := ptrE)
    (bs := enc) (h := fun hleE _ _ => ?_)
  have hbs_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := sf2_lt_of_ofNat (by omega)
  rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A q' capE ptrE enc]
  simp only [vecHeader, sepConj_assoc]
  by_cases hlt : bs.length < cap.toNat
  · have hbeq := sf2_cap_beq_len_false hlt
    apply SepWPpIn.of_sepWP (mid := entry + bv% (528))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_ (hTag sp0 q' cap ptr capE ptrE bs enc hleE hlt hlen
      (sI := s) (F := F) hQp
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm]) hnext')
    rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A q' capE ptrE enc]
    simp only [vecHeader]
    exact entails_of_sep_focus (by sep_frame)
  · have hcap_eq : cap.toNat = bs.length := by omega
    have hcap_bv := sf2_cap_eq_ofNat_len hcap_eq
    apply SepWPpIn.of_sepWP
      (mid := entry + bv% (2 ^ 64 +
        (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") -
        (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine SepWPpIn.weaken_pre ?_ (hDRc sp0 (sp0 - 432#64) cap ptr (entry + bv% (608)) bs 1
      (by omega) (by omega) (F := vecU8At A q' capE ptrE enc ∗ F) hQp
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (sf2_sp_aligned halign (by simp only [arm64_norm, *])) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) rfl ?_)
    · rw [sf2_vec432_eq, vecU8At_eq_header_sep_buf A q' capE ptrE enc]
      simp only [vecHeader]
      exact entails_of_sep_focus (by sep_frame)
    · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 enc.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = ptrE := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx25_1 : s1.readReg64 .x25 = 24#64 := by
        have := hcs1.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx27_1 : s1.readReg64 .x27 = 18#64 := by
        have := hcs1.2.2.2.2.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hsv1 : SerField2Saved s s1 :=
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm] : SerField2Saved s _).trans
          (SerField2Saved.of_calleeSavedPreserved hcs1)
      have hnew_gt : bs.length < newCap.toNat := by omega
      rw [sf2_vec432_eq]
      simp only [sepConj_assoc]
      apply SepWPpIn.of_sepWP (mid := entry + bv% (528))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine SepWPpIn.weaken_pre ?_ (hTag sp0 q' newCap p' capE ptrE bs enc hleE hnew_gt hlen
        (sI := s) (F := F) hQp
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hsv1.trans (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [arm64_norm])) hnext')
      rw [sf2_vec432_eq]
      exact entails_of_sep_focus (by sep_frame)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
