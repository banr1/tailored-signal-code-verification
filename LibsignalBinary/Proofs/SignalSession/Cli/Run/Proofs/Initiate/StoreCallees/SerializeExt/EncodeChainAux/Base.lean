/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.WPX
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.EncodeChainAux.Fetch
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `encode::<Chain, Vec<u8>>`: Stack, `Vec<u8>`, and Callee Step Helpers
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.Prost hiding vecU8Buf vecU8At_eq_header_sep_buf sepWPp_extract_vecU8Buf_le vecU8Buf_eq_open_one vecU8Buf_snoc_eq
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack frame and saved-register bundle -/

/-- Callee stack budget below `sp0 - 96#64` (`encodeChainStackX - 0x60 = 33120` bytes). -/
abbrev encChainSubStack : Nat := Prost.encodeVarintStackX + doReserveStackX + chainLenStack

/-- The 12 saved register words stored at `[sp0 - 96#64 .. sp0)` by the prologue (`+0x000..+0x014`). -/
def encChainSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_encodeChainStackX_split (sp0 : BitVec 64) :
    stackAt sp0 encodeChainStackX =
      stackAt (sp0 - 96#64) encChainSubStack ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : encodeChainStackX = encChainSubStack + 8 * 12 := by decide
  rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 encChainSubStack 12 (by decide)]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem stackAt_sub_to_encodeVarint (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 33120#64) 16576 ∗ stackAt sp Prost.encodeVarintStackX := by
  unfold stackAt
  change memRegion (sp - 33120#64) 33120 =
    memRegion (sp - 33120#64) 16576 ∗ memRegion (sp - 16544#64) 16544
  have h3 : (sp - 33120#64) + 16576#64 = sp - 16544#64 := by bv_omega
  have hsplit := memRegion_split (sp - 33120#64) 16576 16544 (by decide)
  rw [show (16576 : Nat) + 16544 = 33120 by decide,
      show BitVec.ofNat 64 16576 = 16576#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_doReserve (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 33120#64) 16624 ∗ stackAt sp doReserveStackX := by
  unfold stackAt
  change memRegion (sp - 33120#64) 33120 =
    memRegion (sp - 33120#64) 16624 ∗ memRegion (sp - 16496#64) 16496
  have h3 : (sp - 33120#64) + 16624#64 = sp - 16496#64 := by bv_omega
  have hsplit := memRegion_split (sp - 33120#64) 16624 16496 (by decide)
  rw [show (16624 : Nat) + 16496 = 33120 by decide,
      show BitVec.ofNat 64 16624 = 16624#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_chainLen (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 33120#64) 33040 ∗ stackAt sp chainLenStack := by
  unfold stackAt
  change memRegion (sp - 33120#64) 33120 =
    memRegion (sp - 33120#64) 33040 ∗ memRegion (sp - 80#64) 80
  have h3 : (sp - 33120#64) + 33040#64 = sp - 80#64 := by bv_omega
  have hsplit := memRegion_split (sp - 33120#64) 33040 80 (by decide)
  rw [show (33040 : Nat) + 80 = 33120 by decide,
      show BitVec.ofNat 64 33040 = 33040#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_msgKeyLen (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 33120#64) 33104 ∗ stackAt sp msgKeyLenStack := by
  unfold stackAt
  change memRegion (sp - 33120#64) 33120 =
    memRegion (sp - 33120#64) 33104 ∗ memRegion (sp - 16#64) 16
  have h3 : (sp - 33120#64) + 33104#64 = sp - 16#64 := by bv_omega
  have hsplit := memRegion_split (sp - 33120#64) 33104 16 (by decide)
  rw [show (33104 : Nat) + 16 = 33120 by decide,
      show BitVec.ofNat 64 33104 = 33104#64 from rfl, h3] at hsplit
  exact hsplit

theorem sp_sub_96_aligned {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 96#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-! ## 2. `vecU8Buf` slice-open, slice-append, and read-open helpers -/

def vecSliceRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) (n : Nat) : SepProp :=
  ⌜bs.length + n ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + n)) (cap.toNat - (bs.length + n))

theorem vecU8Buf_eq_open_slice (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hn : 0 < n) (hle : bs.length + n ≤ cap.toNat) :
    vecU8Buf A cap ptr bs =
      memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗ vecSliceRest A cap ptr bs n := by
  have hne : cap ≠ 0 := by
    intro h0; have : cap.toNat = 0 := by simp [h0]
    omega
  have hcap_le : cap.toNat ≤ 2 ^ 64 := Nat.le_of_lt cap.isLt
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + n ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecSliceRest
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) n
    (cap.toNat - (bs.length + n)) (by omega)
  rw [show n + (cap.toNat - (bs.length + n)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add] at hsplit
  rw [hsplit]
  ac_rfl

theorem vecU8Buf_append_slice_eq (A : RustAlloc) (cap ptr : BitVec 64)
    (bs sliceBs : List (BitVec 8)) (hn : 0 < sliceBs.length)
    (hle : bs.length + sliceBs.length ≤ cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ sliceBs) ∗
      vecSliceRest A cap ptr bs sliceBs.length =
      vecU8Buf A cap ptr (bs ++ sliceBs) := by
  have hne : cap ≠ 0 := by
    intro h0; have : cap.toNat = 0 := by simp [h0]
    omega
  unfold vecU8Buf vecSliceRest
  simp only [hne, ↓reduceIte]
  have h1 : ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ sliceBs) ∗
      (⌜bs.length + sliceBs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + sliceBs.length))
          (cap.toNat - (bs.length + sliceBs.length))) =
      ⌜bs.length + sliceBs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ sliceBs)) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + sliceBs.length))
          (cap.toNat - (bs.length + sliceBs.length)) := by
    ac_rfl
  rw [h1, pointsToBytes_append, List.length_append]

def vecReadRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8Buf_eq_open_bytes (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hle : bs.length ≤ cap.toNat) :
    vecU8Buf A cap ptr bs = (ptr ↦ₛ bs) ∗ vecReadRest A cap ptr bs := by
  have hne : cap ≠ 0 := by
    intro h0; have : cap.toNat = 0 := by simp [h0]
    omega
  unfold vecU8Buf vecReadRest
  simp only [hne, ↓reduceIte]
  ac_rfl

theorem sepWPp_congr_pre {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P1 = P2) (h : SepWPpX img prog ret s P2 Q Qp) :
    SepWPpX img prog ret s P1 Q Qp :=
  hP ▸ h

theorem sepWPp_extract_vecU8Buf_bounds {img : Obj.Image} {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp := by
  intro hinv R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  obtain ⟨h1, h2, h3⟩ := vecU8Buf_bounds hhm
  exact h h1 h2 h3 hinv R hm hL

theorem sepWPp_extract_vecU8Buf_le {img : Obj.Image} {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → SepWPpX img prog ret s P Q Qp) :
    SepWPpX img prog ret s P Q Qp :=
  sepWPp_extract_vecU8Buf_bounds hP fun h1 _ _ => h h1

theorem vecU8Buf_eq_open_one (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) :
    vecU8Buf A cap ptr bs =
      ∃∗ y : BitVec 8, ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗ Prost.vecRest A cap ptr bs :=
  Prost.vecU8Buf_eq_open_one A cap ptr bs hlt

theorem vecU8Buf_snoc_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗ Prost.vecRest A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ [byte]) :=
  Prost.vecU8Buf_snoc_eq A cap ptr bs byte hlt

theorem vecU8At_eq_cells_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  simp only [vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]

/-! ## 3. Arithmetic bounds for `reserveCap` and capacity comparisons -/

theorem reserveCap_slice_bounds {cap len add : Nat}
    (hle : len ≤ cap) (hrem : cap - len < add) (hlen : len < 2 ^ 32) (hadd : add < 2 ^ 32) :
    reserveCap cap len add + 1 ≤ 2 ^ 63 ∧
    len + add ≤ (BitVec.ofNat 64 (reserveCap cap len add)).toNat ∧
    ((BitVec.ofNat 64 (reserveCap cap len add) - BitVec.ofNat 64 len).ult
      (BitVec.ofNat 64 add)) = false := by
  unfold reserveCap
  have hcap : cap < len + add := by omega
  have hmax : max (max (len + add) (2 * cap)) 8 < 2 ^ 35 := by omega
  have htoNat : (BitVec.ofNat 64 (max (max (len + add) (2 * cap)) 8)).toNat =
      max (max (len + add) (2 * cap)) 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_toNat : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_toNat : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by rw [htoNat]; omega, ?_⟩
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
  rw [BitVec.toNat_sub_of_le]
  · rw [htoNat, hlen_toNat, hadd_toNat]; omega
  · rw [BitVec.le_def, htoNat, hlen_toNat]; omega

theorem spare_ult_iff {cap : BitVec 64} {len add : Nat}
    (hle : len ≤ cap.toNat) (hlen : len < 2 ^ 32) (hadd : add < 2 ^ 32) :
    ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 add) = true ↔ cap.toNat - len < add) ∧
    ((cap - BitVec.ofNat 64 len).ult (BitVec.ofNat 64 add) = false ↔ len + add ≤ cap.toNat) := by
  have hlen_toNat : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hadd_toNat : (BitVec.ofNat 64 add).toNat = add := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (cap - BitVec.ofNat 64 len).toNat = cap.toNat - len := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hlen_toNat]
    · rw [BitVec.le_def, hlen_toNat]; exact hle
  constructor
  · simp only [BitVec.ult, decide_eq_true_eq, hsub, hadd_toNat]
  · simp only [BitVec.ult, decide_eq_false_iff_not, hsub, hadd_toNat]; omega

/-! ## 4. Reusable callee step lemmas (`encode_varint`, `do_reserve_and_handle`, `memcpy`) -/

theorem trVRegs_of_call {s0 s sm : State} (htrm : sm.trace = s.trace)
    (hcsm : CalleeSavedPreserved s sm)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 :=
  ⟨htrm.trans htr.1, hcsm.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩

theorem trVRegs_trans {s0 s sm : State}
    (htrm : sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 :=
  ⟨htrm.1.trans htr.1, htrm.2.trans htr.2⟩

/-- Executes a `bl encode_varint` call inside `encode::<Chain>`. -/
theorem step_encChain_encodeVarint (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hEV : Prost.EncodeVarintOkExtX img A ext)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [encodeVarint_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPpX.call (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp0 - 96#64 - 33120#64) 16576 ∗ F)
    hEV hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint (sp0 - 96#64)] at hm
    simp only [encodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by omega⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [encodeVarintSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun cap' => SepWPpX.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc]
    refine SepWPpX.pure_elim fun htrm => ?_
    refine SepWPpX.pure_elim fun _ => ?_
    have hGoalEq :
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) Prost.encodeVarintStackX ∗
          memRegion (sp0 - 96#64 - 33120#64) 16576 ∗ F) =
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F := by
      rw [stackAt_sub_to_encodeVarint (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm cap' ptr' hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

/-- Executes a 1-byte `bl do_reserve_and_handle` call inside `encode::<Chain>`. -/
theorem step_encChain_reserve1 (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
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
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPpX.call (x := DoReserveCall.mk v curCap curPtr curBs 1)
    (F := memRegion (sp0 - 96#64 - 33120#64) 16624 ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpecX, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpecX, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpX.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStackX ∗
          memRegion (sp0 - 96#64 - 33120#64) 16624 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_doReserve (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt

/-- Executes a slice `bl do_reserve_and_handle` call inside `encode::<Chain>`. -/
theorem step_encChain_reserveSlice (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (hDR : OkAtX img ext doReserveName (doReserveSpecX A))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
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
      vecU8Buf A curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F))
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R))) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpX.call (x := DoReserveCall.mk v curCap curPtr curBs add)
    (F := memRegion (sp0 - 96#64 - 33120#64) 16624 ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpecX, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpecX, encodeChainSpecX, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpecX, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpX.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPpX.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStackX ∗
          memRegion (sp0 - 96#64 - 33120#64) 16624 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_doReserve (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
      hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false

theorem stackAt_sub_to_memcpy (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 33120#64) 16736 ∗ stackAt sp extHookStack := by
  unfold stackAt
  change memRegion (sp - 33120#64) 33120 =
    memRegion (sp - 33120#64) 16736 ∗ memRegion (sp - 16384#64) 16384
  have h3 : (sp - 33120#64) + 16736#64 = sp - 16384#64 := by bv_omega
  have hsplit := memRegion_split (sp - 33120#64) 16736 16384 (by decide)
  rw [show (16736 : Nat) + 16384 = 33120 by decide,
      show BitVec.ofNat 64 16736 = 16736#64 from rfl, h3] at hsplit
  exact hsplit

theorem step_encChain_memcpy (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (hA : AllocContractsX img A ext)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F F_rest : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr encodeChainName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (vecU8Buf A curCap curPtr curBs ∗ (srcPtr ↦ₛ sliceBs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret sm
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)))
    (hF : F = stackAt (sp0 - 96#64) encChainSubStack ∗ F_rest := by sep_focus) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpecX A).onPanic x s0 sf ∗ R)) := by
  have hmc := hA.session_memcpy_ok_at encodeChainName
    (num% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hk := by rw [(ls_lemma% fnOff "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")]; simp only [arm64_norm])
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPpX.call (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗ memRegion (sp0 - 96#64 - 33120#64) 16736 ∗ F_rest)
    hmc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, hF, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle,
        stackAt_sub_to_memcpy (sp0 - 96#64)] at hm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpySpec, libcMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpX.pure_elim fun ⟨_, htrm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ stackAt (sp0 - 96#64) extHookStack ∗
          vecSliceRest A curCap curPtr curBs sliceBs.length ∗
          memRegion (sp0 - 96#64 - 33120#64) 16736 ∗ F_rest) =
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F) := by
      rw [hF, ← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle,
          stackAt_sub_to_memcpy (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
