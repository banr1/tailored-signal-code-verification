/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymA
public import LibsignalBinary.Proofs.E2E.Record.Serialization.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Stack, `Vec<u8>`, and callee stepping helpers for `encode::<Chain, Vec<u8>>` (`0x44b0`)
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack frame and saved registers -/

/-- Callee stack budget below `sp0 - 96#64` (`encodeChainStack - 0x60`). -/
abbrev encChainSubStack : Nat := Prost.encodeVarintStack + doReserveStack + chainLenStack

/-- Callee-saved register words stored in `[sp0 - 96#64 .. sp0)` by the prologue. -/
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

theorem stackAt_encodeChainStack_split (sp0 : BitVec 64) :
    stackAt sp0 encodeChainStack =
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
  have heq : encodeChainStack = encChainSubStack + 8 * 12 := by decide
  rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 encChainSubStack 12 (by decide)]
  simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit, sepExists_sepConj_right]

theorem stackAt_sub_to_encodeVarint (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 8544#64) 4288 ∗ stackAt sp Prost.encodeVarintStack := by
  change memRegion (sp - 8544#64) 8544 =
    memRegion (sp - 8544#64) 4288 ∗ memRegion (sp - 4256#64) 4256
  have h3 : (sp - 8544#64) + 4288#64 = sp - 4256#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 8544#64) 4288 4256 (by decide)
  rw [show (4288 : Nat) + 4256 = 8544 by decide,
      show BitVec.ofNat 64 4288 = 4288#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_doReserve (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 8544#64) 4336 ∗ stackAt sp doReserveStack := by
  change memRegion (sp - 8544#64) 8544 =
    memRegion (sp - 8544#64) 4336 ∗ memRegion (sp - 4208#64) 4208
  have h3 : (sp - 8544#64) + 4336#64 = sp - 4208#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 8544#64) 4336 4208 (by decide)
  rw [show (4336 : Nat) + 4208 = 8544 by decide,
      show BitVec.ofNat 64 4336 = 4336#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_chainLen (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 8544#64) 8464 ∗ stackAt sp chainLenStack := by
  change memRegion (sp - 8544#64) 8544 =
    memRegion (sp - 8544#64) 8464 ∗ memRegion (sp - 80#64) 80
  have h3 : (sp - 8544#64) + 8464#64 = sp - 80#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 8544#64) 8464 80 (by decide)
  rw [show (8464 : Nat) + 80 = 8544 by decide,
      show BitVec.ofNat 64 8464 = 8464#64 from rfl, h3] at hsplit
  exact hsplit

theorem stackAt_sub_to_msgKeyLen (sp : BitVec 64) :
    stackAt sp encChainSubStack =
      memRegion (sp - 8544#64) 8528 ∗ stackAt sp msgKeyLenStack := by
  change memRegion (sp - 8544#64) 8544 =
    memRegion (sp - 8544#64) 8528 ∗ memRegion (sp - 16#64) 16
  have h3 : (sp - 8544#64) + 8528#64 = sp - 16#64 := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hsplit := memRegion_split (sp - 8544#64) 8528 16 (by decide)
  rw [show (8528 : Nat) + 16 = 8544 by decide,
      show BitVec.ofNat 64 8528 = 8528#64 from rfl, h3] at hsplit
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

/-! ## `vecU8Buf` slice-append and read helpers -/

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

theorem sepWPp_extract_vecU8Buf_bounds {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8Buf A cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (F ∗ R) := by
    rw [← sepConj_assoc, ← hP]; exact hm
  obtain ⟨h1, h2, h3⟩ := vecU8Buf_bounds hhm
  exact h h1 h2 h3 R hm hL

theorem vecU8At_eq_cells_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  simp only [vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]

/-! ## `reserveCap` arithmetic bounds -/

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

/-! ## Callee stepping lemmas (`encode_varint`, `do_reserve_and_handle`, `memcpy`) -/

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

theorem step_encChain_encodeVarint (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  rw [encodeVarint_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F)
    hEV hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint (sp0 - 96#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by omega⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [encodeVarintSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun _ => ?_
    have hGoalEq :
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) Prost.encodeVarintStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F) =
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F := by
      rw [stackAt_sub_to_encodeVarint (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm cap' ptr' hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

theorem step_encChain_reserve1 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine SepWPp.call (x := DoReserveCall.mk v curCap curPtr curBs 1)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
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

theorem step_encChain_reserveSlice (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  rw [doReserve_fnAddr_eq_encChain] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.call (x := DoReserveCall.mk v curCap curPtr curBs add)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
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

theorem step_encChain_memcpy (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.call (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗ F)
    encChain_memcpy_ok hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle] at hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [framelessMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗
          vecSliceRest A curCap curPtr curBs sliceBs.length ∗ F) =
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F) := by
      rw [← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

/-! ## Relocatable `[LibsignalPlacement]` callee stepping lemmas (block `12`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

/-- Lifts a `SepWP` basic block into `SepWPp` while preserving `LibsignalCodeLoaded`. -/
theorem sepWPp_of_sepWP_lscl {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

/-- Steps a `withLsCodeLoaded` subroutine call inside `SepWPp`. -/
theorem sepWPp_call_lscl {α : Type} {prog : Program} {pl : MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → LibsignalCodeLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (hcl.of_keepsFrozen hsteps.keepsFrozen)
        hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, hpanic sm hpan⟩)⟩
  · exact (hexit sm code _ hex hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hoom sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem step_encChain_encodeVarint_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hEV' : subroutine_ok (lsProg_12 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hEV
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_lscl (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F)
    hEV' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint (sp0 - 96#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by omega⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [encodeVarintSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun _ => ?_
    have hGoalEq :
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) Prost.encodeVarintStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4288 ∗ F) =
        (vecU8At A v cap' ptr' (curBs ++ encodeVarint val) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F := by
      rw [stackAt_sub_to_encodeVarint (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm cap' ptr' hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm

theorem step_encChain_reserve1_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hcap_eq : curCap.toNat = curBs.length)
    (hlen_lt : curBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length < newCap.toNat →
      SepWPp (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_gt, _⟩ := reserveCap_bounds (len := curBs.length) (by omega)
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 1 := by
    rw [hx2]; rfl
  refine sepWPp_call_lscl (x := DoReserveCall.mk v curCap curPtr curBs 1)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, ?_⟩, ?_⟩
    · rw [hcap_eq]; exact hres_bound
    · convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp, hcap_eq,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_doReserve (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curBs.length curBs.length 1)) p'
      hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_gt

theorem step_encChain_reserveSlice_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8)) (add : Nat)
    (hle : curBs.length ≤ curCap.toNat)
    (hrem : curCap.toNat - curBs.length < add)
    (hlen_lt : curBs.length < 2 ^ 32)
    (hadd_lt : add < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      curBs.length + add ≤ newCap.toNat →
      ((newCap - BitVec.ofNat 64 curBs.length).ult (BitVec.ofNat 64 add)) = false →
      SepWPp (lsProg_12 H) ret sm
        (((v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A newCap p' curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hDR' : subroutine_ok (lsProg_12 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hDR
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  obtain ⟨hres_bound, hnew_ge, hult_false⟩ := reserveCap_slice_bounds hle hrem hlen_lt hadd_lt
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = add := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_call_lscl (x := DoReserveCall.mk v curCap curPtr curBs add)
    (F := memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F)
    hDR' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve (sp0 - 96#64)] at hm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, hres_bound⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpec, encodeChainSpec, allocPanic, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [doReserveSpec, vecU8At_eq_header_sep_buf, vecHeader, hsp,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun p' => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    have hGoalEq :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) doReserveStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 4336 ∗ F) =
        (((v ↦₆₄ BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
          vecU8Buf A (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p' curBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_doReserve (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length add)) p'
      hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hnew_ge hult_false

theorem step_encChain_memcpy_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hmc' : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl framelessMemcpySpec) :=
    subroutine_ok_withLsCodeLoaded_of_plain (ls_hook_ok_of_mem (prog := lsProg_12 H) hmc)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_call_lscl (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗ F)
    hmc' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle] at hm
    simp only [framelessMemcpySpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [framelessMemcpySpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗
          vecSliceRest A curCap curPtr curBs sliceBs.length ∗ F) =
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗ (srcPtr ↦ₛ sliceBs)) ∗ F) := by
      rw [← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm

end Placed

end CryptoVerification.E2E.Record.Serialization

