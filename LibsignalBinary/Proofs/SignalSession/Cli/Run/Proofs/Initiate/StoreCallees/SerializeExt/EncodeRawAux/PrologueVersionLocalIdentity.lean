/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.BasePart2
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeRawAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::encode_raw` Segment 1a: Prologue, Tag 1 (`session_version`), and Tag 2 (`local_identity_public`)
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

def vecSrcRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

def vecCopyDone (A : RustAlloc) (cap ptr : BitVec 64) (bs payload : List (BitVec 8)) : SepProp :=
  ⌜bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ payload ≠ []⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
      (cap.toNat - bs.length - payload.length)

theorem encodeVarintAux_length_le : ∀ (fuel : Nat) (v : BitVec 64),
    (encodeVarintAux fuel v).length ≤ fuel
  | 0, v => by simp [encodeVarintAux]
  | fuel + 1, v => by
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have ih := encodeVarintAux_length_le fuel (v >>> 7)
      omega

theorem encodeVarint_length_le_10 (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

theorem vecU8At_open_src (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) :
    vecU8At A a cap ptr bs =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs := by
  have hne_cap : cap ≠ 0 := by intro h; subst h; simp at hle; exact hne hle
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader vecU8Buf vecSrcRest
  simp only [hne_cap, ↓reduceIte]
  ac_rfl

theorem vecU8At_close_src (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) (R : SepProp) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs ∗ R =
      vecU8At A a cap ptr bs ∗ R := by
  rw [vecU8At_open_src A a cap ptr bs hne hle]
  simp only [sepConj_assoc]

theorem vecU8At_open_src_off (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat)
    (h8 : (ss + off) + 8#64 = ss + a8 := by bv_lin)
    (h16 : (ss + off) + 16#64 = ss + a16 := by bv_lin) :
    vecU8At A (ss + off) cap ptr bs =
      ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs := by
  rw [vecU8At_open_src A (ss + off) cap ptr bs hne hle, h8, h16]

theorem vecU8At_close_src_off (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs ≠ []) (hle : bs.length ≤ cap.toNat) (R : SepProp)
    (h8 : (ss + off) + 8#64 = ss + a8 := by bv_lin)
    (h16 : (ss + off) + 16#64 = ss + a16 := by bv_lin) :
    ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecSrcRest A cap ptr bs ∗ R =
      vecU8At A (ss + off) cap ptr bs ∗ R := by
  rw [← h8, ← h16, vecU8At_close_src A (ss + off) cap ptr bs hne hle R]

theorem vecU8At_close_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) (hne : payload ≠ []) (R : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      vecCopyDone A cap ptr bs payload ∗ R =
      vecU8At A v cap ptr (bs ++ payload) ∗ R := by
  rw [← vecU8At_pack_slice A v cap ptr bs payload hle hcap hptr hne]
  unfold vecCopyDone
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ payload ≠ []) = True :=
    eq_true ⟨hle, hcap, hptr, hne⟩
  rw [hpure, pure_true, emp_sepConj]
  ac_rfl

theorem encraw_call_doReserve_buf {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
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
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v newCap p' bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by
    rw [hP, vecU8At_eq_header_sep_buf]
    simp only [vecHeader, sepConj_assoc]
  exact encraw_call_doReserve hDR sp0 v cap ptr ret_pc bs add hcap_le hlen_lt
    hpc hrun hsp halign htr hlr hx0 hx1 hx2 hx3 hx4 hP' hnext

theorem encraw_call_memcpy_buf {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    {stkSp : BitVec 64} {F_rest : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          vecCopyDone A cap ptr bs payload ∗ (srcPtr ↦ₛ payload)) ∗ F)
        Q (PanicAllocPost s0))
    (hF : F = stackAt stkSp encodeRawSubStack ∗ F_rest := by sep_focus)
    (hsp_stk : s.sp = stkSp := by simp only [wp_norm, arm64_norm, *]) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hP' : P = (vecU8At A v cap ptr bs ∗ (srcPtr ↦ₛ payload)) ∗ F := by
    rw [hP, vecU8At_eq_header_sep_buf]
    simp only [vecHeader, sepConj_assoc]
  refine encraw_call_memcpy hA v cap ptr srcPtr ret_pc bs payload hle hcap hptr hne
    hpc hrun halign htr hlr hx0 hx1 hx2 hP' ?_ hF hsp_stk
  intro sm hpcm hrunm hspm htrm hcsm
  refine SepWPpX.weaken_pre ?_ (hnext sm hpcm hrunm hspm htrm hcsm)
  unfold vecCopyDone
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ payload ≠ []) = True :=
    eq_true ⟨hle, hcap, hptr, hne⟩
  rw [hpure, pure_true, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

private theorem er_vecU8Buf_eq_open_one (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8Buf A cap ptr bs =
      ∃∗ y : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs :=
  Prost.vecU8Buf_eq_open_one A cap ptr bs hlt

private theorem er_vecU8Buf_snoc_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ [byte]) :=
  Prost.vecU8Buf_snoc_eq A cap ptr bs byte hlt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr vecRest vecU8Buf vecSrcRest vecCopyDone
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm]
theorem bv_add_neg80 (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 :=
  (BitVec.sub_eq_add_neg x 80#64).symm

/-! ## Helpers for `Vec<u8>` 1-byte and slice operations without exposing `memRegion` -/

theorem vecU8At_open_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8At A v cap ptr bs =
      ∃∗ y : BitVec 8,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ vecRest A cap ptr bs := by
  rw [vecU8At_eq_header_sep_buf, er_vecU8Buf_eq_open_one A cap ptr bs hlt]
  simp only [vecHeader, sepExists_sepConj_right, sepConj_assoc]

theorem vecU8At_close_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) (R : SepProp) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ vecRest A cap ptr bs ∗ R =
      vecU8At A v cap ptr (bs ++ [byte]) ∗ R := by
  rw [bv_len_add_one bs byte, ← sepConj_assoc ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte),
      er_vecU8Buf_snoc_eq A cap ptr bs byte hlt, vecU8At_eq_header_sep_buf]
  simp only [vecHeader, sepConj_assoc]

theorem vecU8At_Nil_eq (A : RustAlloc) (a cap ptr : BitVec 64) :
    vecU8At A a cap ptr [] =
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  rw [vecU8At_eq_header_sep_buf]
  simp only [vecHeader, List.length_nil, sepConj_assoc]

theorem vecU8At_Nil_off (A : RustAlloc) (ss off a8 a16 cap ptr : BitVec 64)
    (h8 : (ss + off) + 8#64 = ss + a8 := by bv_lin)
    (h16 : (ss + off) + 16#64 = ss + a16 := by bv_lin) :
    vecU8At A (ss + off) cap ptr [] =
      ((ss + off) ↦₆₄ cap) ∗ ((ss + a8) ↦₆₄ ptr) ∗ ((ss + a16) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  rw [vecU8At_Nil_eq, h8, h16]

theorem cmp_hi_false_of_le {cap : BitVec 64} {len add : Nat}
    (hle : len + add ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem cmp_hi_true_of_gt {cap : BitVec 64} {len add : Nat}
    (hlen_le : len ≤ cap.toNat) (hlt : cap.toNat < len + add)
    (hcap : cap.toNat < 2 ^ 63) (hadd : add < 2 ^ 63) :
    BitVec.ult (cap - BitVec.ofNat 64 len) (BitVec.ofNat 64 add) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

theorem cmp_ls_true_of_le {cap : BitVec 64} {len add : Nat}
    (hle : len + add ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 add) (cap - BitVec.ofNat 64 len) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  have hlen_mod : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_mod : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_mod]
    · rw [BitVec.le_def, hlen_mod]; omega
  rw [hsub, hadd_mod]
  omega

/-! ## 1. Prologue (`+0x000 → +0x01c`, offsets `0..28`) -/

/-- Prologue (`+0x000..+0x018`, 7 instructions): allocates `0x50` stack frame, saves
`x29, x30, x25, x24, x23, x22, x21, x20, x19`, sets `x29 = sp0 - 80#64` and `x20 = ss`. -/
theorem step_encraw_prologue {img : Obj.Image} {ext : String → Option (State → State)}
    (ss v sp0 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : s.readReg64 .x1 = v)
    (hcs0 : CalleeSavedPreserved s0 s)
    (hlr0 : s.readReg64 .lr = s0.readReg64 .lr)
    (hP : P = stackAt sp0 encodeRawStackX ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (v56 : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 28#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = ss →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((encRawSavedRegs sp0 s0 v56 ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F) Q Qp) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q Qp := by
  encraw_fetches_range img.base (Rust.withPanics ext) 0 28
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rcases hcs0 with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  rw [hP, stackAt_encodeRawStackX_unfold sp0]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPpX.exists_elim fun v80 => SepWPpX.exists_elim fun v72 =>
    SepWPpX.exists_elim fun v64 => SepWPpX.exists_elim fun v56 =>
    SepWPpX.exists_elim fun v48 => SepWPpX.exists_elim fun v40 =>
    SepWPpX.exists_elim fun v32 => SepWPpX.exists_elim fun v24 =>
    SepWPpX.exists_elim fun v16 => SepWPpX.exists_elim fun v8 => ?_
  apply SepWPpX.of_sepWP (mid := entry + bv% (28))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [show
      ((sp0 - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((sp0 - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((sp0 - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((sp0 - 56#64) ↦₆₄ v56) ∗
      ((sp0 - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
      ((sp0 - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((sp0 - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((sp0 - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((sp0 - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((sp0 - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
      stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
      (encRawSavedRegs sp0 s0 v56 ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F by
    simp only [encRawSavedRegs, Reg.lr, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21,
      Reg.x20, Reg.x19, sepConj_assoc]]
  exact hnext _ v56
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩

/-! ## 2. Tag 1 (`session_version`, `+0x01c → +0x054`, reserve `+0x6cc..+0x6f0`) -/

/-- Tag 1 (`+0x01c..+0x054`, reserve `+0x6cc..+0x6f0`): sets `x19 = v`, reads `w0 = [ss, #0x148]`
(`session_version`), and appends `uint32Field 1 ver` to `v`. -/
theorem step_encraw_tag1 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (ss v sp0 cap ptr : BitVec 64) (ver : BitVec 32) (bs : List (BitVec 8))
    (hlen_lt : bs.length + 11 < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 28#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = ss)
    (hx1 : s.readReg64 .x1 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 84#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A v cap' ptr' (bs ++ uint32Field 1 ver) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve img A ext hDR
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  encraw_fetches_range img.base (Rust.withPanics ext) 28 84
  encraw_fetches_range img.base (Rust.withPanics ext) 1740 1776
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  by_cases hver : ver = 0#32
  · subst hver
    apply SepWPpX.of_sepWP (mid := entry + bv% (84))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    simpa only [uint32Field_zero, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hver_beq : (ver == 0#32) = false := bv32_beq_zero_false hver
    have hfield_eq : bs ++ uint32Field 1 ver =
        (bs ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 ver) := by
      rw [uint32Field_ne_zero (k := 0x08#8) hver, List.append_assoc]
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_one A v cap ptr bs 0x08#8 hlt]
      refine hCallEV sp0 (BitVec.zeroExtend 64 ver) v cap ptr (entry + bv% (84))
        (bs ++ [0x08#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        rw [← hfield_eq]
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [show
          ((ss + 0x148#64) ↦₃₂ ver) ∗ (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
          ((ss + 0x148#64) ↦₃₂ ver) ∗ vecU8At A v cap ptr bs ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack ∗ F by
        rw [vecU8At_eq_header_sep_buf]; simp only [vecHeader, sepConj_assoc]]
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (1764)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
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
        have hx21_1 : s1.readReg64 .x21 = BitVec.zeroExtend 64 ver := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hnew_gt : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p' bs hnew_gt]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x08#8 hnew_gt]
        refine hCallEV sp0 (BitVec.zeroExtend 64 ver) v newCap p' (entry + bv% (84))
          (bs ++ [0x08#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro sm cap' ptr' hpcm hrunm hspm htrm hcsm
          have hx19m : sm.readReg64 .x19 = v := by
            have := hcsm.1; simp only [arm64_norm, *] at this; exact this
          have hx20m : sm.readReg64 .x20 = ss := by
            have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
          have hcsm' : EncRawUpperSaved s0 sm :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
          rw [← hfield_eq]
          refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

/-! ## 3. Tag 2 (`local_identity_public`, `+0x054 → +0x0c0`, reserve `+0x6f0..+0x754`) -/

/-- Second half of Tag 2 (`+0x090..+0x0c0`, reserve `+0x70c..+0x754`): reserves `fBs.length` bytes
if needed and copies `fBs` via `memcpy`. -/
theorem step_encraw_tag2_b {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (ss v sp0 fCap fPtr cap1 ptr1 : BitVec 64) (bs1 fBs : List (BitVec 8))
    (hf_nil : fBs ≠ [])
    (hf_le : fBs.length ≤ fCap.toNat)
    (hf_cap : fCap.toNat < 2 ^ 63)
    (hlen_lt : bs1.length + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 fBs.length)
    (hx22 : s.readReg64 .x22 = fPtr)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A ss fCap fPtr fBs ∗ vecU8At A v cap1 ptr1 bs1 ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A ss fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs1 ++ fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallMC := @encraw_call_memcpy_buf img A ext hA
  encraw_fetches_range img.base (Rust.withPanics ext) 144 192
  encraw_fetches_range img.base (Rust.withPanics ext) 1804 1876
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap1) (ptr := ptr1) (bs := bs1)
    (h := fun hle1 hcap1 hptr1 => ?_)
  have hf_nat : (BitVec.ofNat 64 fBs.length).toNat = fBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hbs1_nat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [vecU8At_open_src A ss fCap fPtr fBs hf_nil hf_le,
      vecU8At_eq_header_sep_buf A v cap1 ptr1 bs1]
  simp only [vecHeader, sepConj_assoc]
  by_cases hfit : bs1.length + fBs.length ≤ cap1.toNat
  · have hhi := cmp_hi_false_of_le hfit hcap1
    apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallMC v cap1 ptr1 fPtr (entry + bv% (184)) bs1 fBs hfit hcap1 hptr1 hf_nil
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · intro sm hpcm hrunm hspm htrm hcsm
      have hx19m : sm.readReg64 .x19 = v := by
        have := hcsm.1; simp only [arm64_norm, *] at this; exact this
      have hx20m : sm.readReg64 .x20 = ss := by
        have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
        have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hspm' : sm.sp = sp0 - 80#64 := by
        rw [hspm]; simp only [arm64_norm, *]
      have hcsm' : EncRawUpperSaved s0 sm :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
      apply SepWPpX.of_sepWP (mid := entry + bv% (192))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_slice A v cap1 ptr1 bs1 fBs hfit hcap1 hptr1 hf_nil]
      refine SepWPpX.weaken_pre ?_ (hnext _ cap1 ptr1
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
      rw [vecU8At_open_src A ss fCap fPtr fBs hf_nil hf_le]
      exact entails_of_sep_focus (by sep_focus)
  · have hhi := cmp_hi_true_of_gt (add := fBs.length) hle1 (by omega) hcap1 (by omega)
    apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine hCallDR sp0 v cap1 ptr1 (entry + bv% (1828)) bs1 fBs.length
      (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
    · simp only [arm64_norm]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm, *]
    · simp only [arm64_norm]
    · simp only [arm64_norm]
    · intro s1 newCap p' hpc1 hrun1 hsp1 htr1 hcs1 hnew_ge hnew_lt
      have hx19_1 : s1.readReg64 .x19 = v := by
        have := hcs1.1; simp only [arm64_norm, *] at this; exact this
      have hx20_1 : s1.readReg64 .x20 = ss := by
        have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
      have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
        have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hx22_1 : s1.readReg64 .x22 = fPtr := by
        have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
      have hcs_1 : EncRawUpperSaved s0 s1 :=
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
          (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
      have hls := cmp_ls_true_of_le hnew_ge hnew_lt
      refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := newCap) (ptr := p') (bs := bs1)
        (h := fun _ _ hp'_ne => ?_)
      rw [vecU8At_eq_header_sep_buf A v newCap p' bs1]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine hCallMC v newCap p' fPtr (entry + bv% (184)) bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro sm hpcm hrunm hspm htrm hcsm
        have hx19m : sm.readReg64 .x19 = v := by
          have := hcsm.1; simp only [arm64_norm, *] at this; exact this
        have hx20m : sm.readReg64 .x20 = ss := by
          have := hcsm.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcsm.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bs1.length := by
          have := hcsm.2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hspm' : sm.sp = sp0 - 80#64 := by
          rw [hspm]; simp only [arm64_norm, *]
        have hcsm' : EncRawUpperSaved s0 sm :=
          (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcsm)
        apply SepWPpX.of_sepWP (mid := entry + bv% (192))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_slice A v newCap p' bs1 fBs hnew_ge hnew_lt hp'_ne hf_nil]
        refine SepWPpX.weaken_pre ?_ (hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm'.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩))
        rw [vecU8At_open_src A ss fCap fPtr fBs hf_nil hf_le]
        exact entails_of_sep_focus (by sep_focus)

/-- Tag 2 (`+0x054..+0x0c0`, reserve `+0x6f0..+0x754`): appends `bytesField 2 fBs`
(`local_identity_public` at `ss + 0x00`) to `v`. -/
theorem step_encraw_tag2 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (ss v sp0 fCap fPtr cap ptr : BitVec 64) (bs fBs : List (BitVec 8))
    (hlen_lt : bs.length + 11 + fBs.length < 2 ^ 62)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 80#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = ss)
    (hcs : EncRawUpperSaved s0 s)
    (hP : P = (vecU8At A ss fCap fPtr fBs ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName + 192#64 →
      sm.status = .Running →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = ss →
      EncRawUpperSaved s0 sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A ss fCap fPtr fBs ∗ vecU8At A v cap' ptr' (bs ++ bytesField 2 fBs) ∗
          A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q (PanicAllocPost s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q (PanicAllocPost s0) := by
  have hCallDR := @encraw_call_doReserve_buf img A ext hDR
  have hCallEV := @encraw_call_encodeVarint img A ext hEV
  have hStepB := @step_encraw_tag2_b img A ext hA hDR
  encraw_fetches_range img.base (Rust.withPanics ext) 84 144
  encraw_fetches_range img.base (Rust.withPanics ext) 1776 1804
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr encodeRawName = entry
  examples_hide_fetches
  rw [hP]
  refine sepWPp_extract_vecU8At_bounds (A := A) (v := ss) (cap := fCap) (ptr := fPtr) (bs := fBs)
    (h := fun hf_le hf_cap _ => ?_)
  by_cases hf_nil : fBs = []
  · subst hf_nil
    rw [vecU8At_Nil_eq A ss fCap fPtr]
    simp only [sepConj_assoc]
    apply SepWPpX.of_sepWP (mid := entry + bv% (192))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [show
        (ss ↦₆₄ fCap) ∗ ((ss + 8#64) ↦₆₄ fPtr) ∗ ((ss + 16#64) ↦₆₄ 0#64) ∗
        vecU8Buf A fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
        stackAt (sp0 - 80#64) encodeRawSubStack ∗ F =
        (vecU8At A ss fCap fPtr [] ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F by
      rw [vecU8At_Nil_eq A ss fCap fPtr]; simp only [sepConj_assoc]]
    simpa only [bytesField_nil, List.append_nil] using
      hnext _ cap ptr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
  · have hf_beq : (BitVec.ofNat 64 fBs.length == 0#64) = false :=
      ofNat64_len_beq_zero_false hf_nil (by omega)
    have hfield_eq : bs ++ bytesField 2 fBs =
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ++ fBs := by
      rw [bytesField_ne_nil (k := 0x12#8) hf_nil]; simp only [List.append_assoc]
    have hlen_bs1 :
        ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)).length + fBs.length < 2 ^ 62 := by
      have h10 := encodeVarint_length_le_10 (BitVec.ofNat 64 fBs.length)
      simp only [List.length_append, List.length_singleton]
      omega
    refine sepWPp_extract_vecU8At_bounds (A := A) (v := v) (cap := cap) (ptr := ptr) (bs := bs)
      (h := fun hle _ _ => ?_)
    rw [vecU8At_open_src A ss fCap fPtr fBs hf_nil hf_le]
    by_cases hlt : bs.length < cap.toNat
    · have hbeq_cap := cap_beq_len_false hlt
      rw [vecU8At_open_one A v cap ptr bs hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPpX.exists_elim fun old => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8At_close_src A ss fCap fPtr fBs hf_nil hf_le,
          vecU8At_close_one A v cap ptr bs 0x12#8 hlt]
      refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v cap ptr (entry + bv% (144))
        (bs ++ [0x12#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcs1
        have hx19_1 : s1.readReg64 .x19 = v := by
          have := hcs1.1; simp only [arm64_norm, *] at this; exact this
        have hx20_1 : s1.readReg64 .x20 = ss := by
          have := hcs1.2.1; simp only [arm64_norm, *] at this; exact this
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = fPtr := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        refine hStepB ss v sp0 fCap fPtr cap1 ptr1
          ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
          hf_nil hf_le hf_cap hlen_bs1 hpc1 hrun1 hsp1 halign htr1
          hx19_1 hx20_1 hx21_1 hx22_1 hcs_1 (by sep_focus) ?_
        intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
        rw [← hfield_eq]
        refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
        exact entails_of_sep_focus (by sep_focus)
    · have hcap_eq : cap.toNat = bs.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      rw [vecU8At_eq_header_sep_buf A v cap ptr bs]
      simp only [vecHeader, sepConj_assoc]
      apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      have hx1_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine hCallDR sp0 v cap ptr (entry + bv% (1796)) bs 1
        (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
      · simp only [arm64_norm]
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
      · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
      · simp only [arm64_norm, *]
      · simp only [arm64_norm, *]
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
        have hx21_1 : s1.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
          have := hcs1.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hx22_1 : s1.readReg64 .x22 = fPtr := by
          have := hcs1.2.2.2.1; simp only [arm64_norm, *] at this; exact this
        have hcs_1 : EncRawUpperSaved s0 s1 :=
          (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
            (EncRawUpperSaved.of_calleeSavedPreserved hcs1)
        have hnew_gt : bs.length < newCap.toNat := by omega
        rw [vecU8At_open_one A v newCap p' bs hnew_gt]
        simp only [sepExists_sepConj_left, sepConj_assoc]
        refine SepWPpX.exists_elim fun old => ?_
        apply SepWPpX.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8At_close_one A v newCap p' bs 0x12#8 hnew_gt]
        refine hCallEV sp0 (BitVec.ofNat 64 fBs.length) v newCap p' (entry + bv% (144))
          (bs ++ [0x12#8]) (by simp; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by sep_focus) ?_
        · simp only [arm64_norm]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · exact sp_sub_80_spAligned halign (by simp only [arm64_norm, *])
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · simp only [arm64_norm, *]
        · intro s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2
          have hx19_2 : s2.readReg64 .x19 = v := by
            have := hcs2.1; simp only [arm64_norm, *] at this; exact this
          have hx20_2 : s2.readReg64 .x20 = ss := by
            have := hcs2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx21_2 : s2.readReg64 .x21 = BitVec.ofNat 64 fBs.length := by
            have := hcs2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hx22_2 : s2.readReg64 .x22 = fPtr := by
            have := hcs2.2.2.2.1; simp only [arm64_norm, *] at this; exact this
          have hcs_2 : EncRawUpperSaved s0 s2 :=
            (hcs_1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩).trans
              (EncRawUpperSaved.of_calleeSavedPreserved hcs2)
          have hCloseSrc :
              (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              (ss ↦₆₄ fCap) ∗ ((ss + 8#64) ↦₆₄ fPtr) ∗
              ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 fBs.length) ∗
              (fPtr ↦ₛ fBs) ∗ vecSrcRest A fCap fPtr fBs ∗ F =
              (vecU8At A v cap1 ptr1 ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) ∗
                A.pool ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
              vecU8At A ss fCap fPtr fBs ∗ F := by
            rw [vecU8At_close_src A ss fCap fPtr fBs hf_nil hf_le]
          rw [hCloseSrc]; clear hCloseSrc
          refine hStepB ss v sp0 fCap fPtr cap1 ptr1
            ((bs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 fBs.length)) fBs
            hf_nil hf_le hf_cap hlen_bs1 hpc2 hrun2 hsp2 halign htr2
            hx19_2 hx20_2 hx21_2 hx22_2 hcs_2 (by sep_focus) ?_
          intro sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm'
          rw [← hfield_eq]
          refine SepWPpX.weaken_pre ?_ (hnext sm cap' ptr' hpcm hrunm hspm htrm hx19m hx20m hcsm')
          exact entails_of_sep_focus (by sep_focus)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
