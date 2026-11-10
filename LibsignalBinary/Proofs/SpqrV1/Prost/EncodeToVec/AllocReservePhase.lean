/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec`: Buffer Allocation, Epilogue, and Callee Wrappers

Empty-state encoded-length characterization, `vecU8At` byte/slice append helpers, stack-restore
epilogue (`0x6d720..0x6d74c`), initial `Vec<u8>` buffer allocation (`0x6d214..0x6d250`), and
exact-capacity callee call wrappers at `s.sp = sp - 144#64`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

/-! ## 1. Empty-State Encoded Length Characterization -/

theorem optVersionNegotiationPBFieldEncodedLen_pos (vn : VersionNegotiationPB) :
    0 < optVersionNegotiationPBFieldEncodedLen (some vn) := by
  dsimp [optVersionNegotiationPBFieldEncodedLen, versionNegotiationPBEncodedLen]
  have := (varintLen_bounds (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))).1
  omega

theorem optChainPBFieldEncodedLen_pos (ch : ChainPB) :
    0 < optChainPBFieldEncodedLen (some ch) := by
  dsimp [optChainPBFieldEncodedLen]
  have := (varintLen_bounds (BitVec.ofNat 64 (chainPBEncodedLen ch))).1
  omega

theorem optPqRatchetInnerPBFieldEncodedLen_pos (in_ : PqRatchetState.Inner) :
    0 < optPqRatchetInnerPBFieldEncodedLen (some in_) := by
  cases in_ with
  | v1 v1s =>
    dsimp [optPqRatchetInnerPBFieldEncodedLen]
    have := (varintLen_bounds (BitVec.ofNat 64 (v1StatePBEncodedLen v1s))).1
    omega

theorem pqRatchetState_fields_none_of_encodedLen_zero {st : PqRatchetState}
    (h0 : pqRatchetStatePBEncodedLen st = 0) :
    st.versionNegotiation = none ∧ st.chain = none ∧ st.inner = none ∧
      PqRatchetState.encodeRaw st = [] := by
  have h0' := h0
  unfold pqRatchetStatePBEncodedLen at h0
  have hvn : st.versionNegotiation = none := by
    cases h : st.versionNegotiation with
    | none => rfl
    | some vn =>
      have hp := optVersionNegotiationPBFieldEncodedLen_pos vn
      rw [h] at h0; omega
  have hch : st.chain = none := by
    cases h : st.chain with
    | none => rfl
    | some ch =>
      have hp := optChainPBFieldEncodedLen_pos ch
      rw [h] at h0; omega
  have hin : st.inner = none := by
    cases h : st.inner with
    | none => rfl
    | some in_ =>
      have hp := optPqRatchetInnerPBFieldEncodedLen_pos in_
      rw [h] at h0; omega
  refine ⟨hvn, hch, hin, ?_⟩
  have hlen := pqRatchetStatePBEncodedLen_eq_proto st
  rw [h0'] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

/-! ## 2. `vecU8At` Byte and Slice Manipulation Helpers -/

theorem vecU8At_expose_header (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          if cap = 0 then emp
          else
            A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]

private theorem cap_ne_zero_of_pos {cap : BitVec 64} (h : 0 < cap.toNat) : cap ≠ 0 := by
  intro heq; subst heq; simp at h

theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At_expose_header] at hm
    convert hm using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) (hn_pos : 0 < n) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
          (cap.toNat - bs.length - n)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr bs, hpure, pure_true, emp_sepConj]
  simp only [hcap_ne, ↓reduceIte]
  rw [memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
        (n := n) (k := cap.toNat - bs.length - n)
        (by omega) rfl (by omega)]

theorem vecU8At_pack_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (hne : payload ≠ []) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
        (cap.toNat - bs.length - payload.length)) =
    vecU8At A v cap ptr (bs ++ payload) := by
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr (bs ++ payload)]
  simp only [hcap_ne, ↓reduceIte]
  have hlen : (bs ++ payload).length = bs.length + payload.length := List.length_append
  have hbv : BitVec.ofNat 64 (bs.length + payload.length) =
      BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length) =
      ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by bv_omega
  have hsub : cap.toNat - (bs.length + payload.length) =
      cap.toNat - bs.length - payload.length := by omega
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, pointsToBytes_append, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem memRegion_one_eq (a : BitVec 64) : memRegion a 1 = ∃∗ y : BitVec 8, a ↦₈ y :=
  IsBlock.eq (IsBlock.memRegion a 1)
    (IsBlock.sepExists fun v => IsBlock.pointsTo8 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_eight_eq (a : BitVec 64) : memRegion a 8 = ∃∗ v : BitVec 64, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_24_eq (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8) (by decide) (by bv_omega) (by decide),
    memRegion_eight_eq a, memRegion_eight_eq (a + 8#64), memRegion_eight_eq (a + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem vecU8At_expose_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    vecU8At A v cap ptr bs =
      ∃∗ y : BitVec 8,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1) := by
  rw [vecU8At_expose_slice A v cap ptr bs 1 (by omega) hcap hptr (by omega),
    memRegion_one_eq (ptr + BitVec.ofNat 64 bs.length)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem vecU8At_pack_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) =
    vecU8At A v cap ptr (bs ++ [byte]) := by
  have h := vecU8At_pack_slice A v cap ptr bs [byte] (by simp; omega) hcap hptr (by simp)
  simpa only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton] using h

theorem vecU8At_empty_zero (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) =
    vecU8At A v 0#64 1#64 [] := by
  have hpure : (([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0) = True :=
    eq_true ⟨by decide, by decide, by decide⟩
  rw [vecU8At_expose_header A v 0#64 1#64 [], hpure, pure_true, emp_sepConj]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]

theorem vecU8At_empty_of_alloc (A : RustAlloc) (v ptr : BitVec 64) (sz : Nat)
    (hpos : 0 < sz) (hsz : sz < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ BitVec.ofNat 64 sz) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr sz 1 ∗ memRegion ptr sz) =
    vecU8At A v (BitVec.ofNat 64 sz) ptr [] := by
  have htoNat : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 sz ≠ 0 := cap_ne_zero_of_pos (by omega)
  have hpure : (([] : List (BitVec 8)).length ≤ (BitVec.ofNat 64 sz).toNat ∧
      (BitVec.ofNat 64 sz).toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by simp, by omega, hptr⟩
  rw [vecU8At_expose_header A v (BitVec.ofNat 64 sz) ptr [], hpure, pure_true, emp_sepConj]
  simp only [hcap_ne, ↓reduceIte, htoNat, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, pointsToBytes_nil, emp_sepConj]

theorem cap_beq_len_false_of_lt {cap : BitVec 64} {bsLen : Nat}
    (hlt : bsLen < cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (cap == BitVec.ofNat 64 bsLen) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem elem_len_ult_spare_false_of_le {cap : BitVec 64} {bsLen elemLen : Nat}
    (hle : bsLen + elemLen ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    ((cap - BitVec.ofNat 64 bsLen).ult (BitVec.ofNat 64 elemLen)) = false := by
  have hle_bv : BitVec.ofNat 64 bsLen ≤ cap := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_sub_of_le hle_bv,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem calleeSavedPreserved_writeLr_setPC {s s' : State} {lr pc : BitVec 64}
    (h : CalleeSavedPreserved ((s.writeReg64 (Reg.gpr 30#5) lr).setPC pc) s') :
    s'.readReg64 .x19 = s.readReg64 .x19 ∧
    s'.readReg64 .x20 = s.readReg64 .x20 ∧
    s'.readReg64 .x21 = s.readReg64 .x21 ∧
    s'.readReg64 .x22 = s.readReg64 .x22 ∧
    s'.readReg64 .x23 = s.readReg64 .x23 ∧
    s'.readReg64 .x24 = s.readReg64 .x24 ∧
    s'.readReg64 .x25 = s.readReg64 .x25 ∧
    s'.readReg64 .x26 = s.readReg64 .x26 ∧
    s'.readReg64 .x27 = s.readReg64 .x27 ∧
    s'.readReg64 .x28 = s.readReg64 .x28 ∧
    s'.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs s' = calleeSavedVRegs s := by
  rcases h with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hvregs⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [arm64_norm] using ‹_›

/-! ## 3. Epilogue (`0x6d720..0x6d74c`, `+1808..+1856`) -/

/-- Epilogue (`0x6d720..0x6d74c`, `+1808..+1856`):
Moves `vecU8At A (sp - 120#64) cap ptr bs` from stack slot `sp_cur + 0x18` (`sp - 120#64`) into
`vecU8 A sret bs` (`x27 = sret`), restores callee-saved registers `x19..x30` from `sp - 96..sp - 8`,
restores `sp`, and returns to `s0.readReg64 .lr`. -/
theorem step_encodeToVec_epilogue {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State} (sret sp cap ptr v0 v1 v2 : BitVec 64) (bs : List (BitVec 8))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 1808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx27 : s.readReg64 .x27 = sret)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp - 120#64) cap ptr bs ∗
      memRegion sret 24 ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0 ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hret : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf ((vecU8 A sret bs ∗ stackAt sp (encodeToVecStackOf resStack)) ∗ F)) :
    SepWPp (spqrProgAtExt b ext) (s0.readReg64 .lr) s P Q Qp := by
  etv_fetches b (Rust.withPanics ext) hfn 1808 1856
  examples_hide_fetches; subst hP; unfold encodeToVecSavedRegs
  rw [vecU8At_expose_header A (sp - 120#64) cap ptr bs, memRegion_24_eq sret]
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun s2_v => SepWPp.exists_elim fun s1_v => SepWPp.exists_elim fun s0_v => ?_
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hret _ (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by epochEncLen_cc_close) (hinv0.trans hinv1)))
  refine sepConj_mono_left ?_
  refine Entails.trans ?_
    (sepConj_mono_right (stackAt_encodeToVec_recombine hres sp v0 v1 v2 cap ptr (BitVec.ofNat 64 bs.length) s0))
  unfold vecU8 encodeToVecLocalSlots encodeToVecSavedRegs
  refine Entails.trans ?_
    (sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))))
  rw [vecU8At_expose_header A sret cap ptr bs]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Initial Buffer Allocation (`0x6d214..0x6d250` and `0x6d328..0x6d338`) -/

/-- Stack-equipped no-op shim contract at `s.sp = sp - 144#64`. -/
def shimStackSpecOf (resStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Stack-equipped `__rust_alloc(sz, 1)` contract at `s.sp = sp - 144#64`. -/
def rustAllocStackSpecOf (resStack : Nat) (A : RustAlloc) : Spec Nat where
  pre := fun sz s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63⌝ ∗
      A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun sz s0 sf =>
    (if sf.readReg64 .x0 = 0#64 then
      ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

private theorem allocFailedIn_of_eq_trace {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem encodeToVecOnPanic_of_trace {s0 sf : State} {P R : SepProp}
    (htr : sf.trace = s0.trace ++ [allocFailedEvent])
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R := by
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold encodeToVecOnPanic
  have hp : (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) = True :=
    eq_true (allocFailedIn_of_eq_trace htr)
  rw [hp, pure_true, emp_sepConj]
  exact entails_anyHeap P

theorem step_encodeToVec_alloc {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    {s0 s : State}
    (hshim : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (rustAllocStackSpecOf resStack A)))
    (hhandle : (spqrProgAtExt b ext).externAt?
      (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) = some Rust.panicked)
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 516#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then entry + 580#64 else entry + 1212#64) →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      (st.versionNegotiation.isSome → sm.readReg64 .x0 = ptr) →
      sm.readReg64 .x19 = optChainCap g.chain st.chain →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = sret →
      sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  etv_fetches b (Rust.withPanics ext) hfn 516 580
  etv_fetches b (Rust.withPanics ext) hfn 792 812
  examples_hide_fetches; subst hP
  have hbit63 := getLsbD_63_ofNat_eq_false hlen
  have helem63 := getElem_63_ofNat_eq_false hlen
  refine sepWPp_extract_pure
    ((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
     (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optVersionNegotiationPBPinnedAt_eq] at hm
      have hm' : s.mem ⊨ optVersionNegRest A g.vn a st.versionNegotiation ∗
          ((a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
           optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
           optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗
           A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
           encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
           encodeToVecSavedRegs sp s0 ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact optVersionNegRest_cap_bounds hm')
    fun ⟨hvn_eq, hvn_ne⟩ => ?_
  by_cases hzero : pqRatchetStatePBEncodedLen st = 0
  · obtain ⟨hvn_none, _, _, _⟩ := pqRatchetState_fields_none_of_encodedLen_zero hzero
    have hx23_0 : s.readReg64 .x23 = 0#64 := by rw [hx23, hzero]
    rw [hvn_none] at hvn_eq hvn_ne
    simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
    unfold encodeToVecLocalSlots
    apply SepWPp.of_sepWP_cs (mid := entry + 1212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (hnext _ 1#64
        (by rw [hvn_none]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (fun h => by rw [hvn_none] at h; cases h)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    rw [hzero, ← vecU8At_empty_zero A (sp - 120#64)]
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    rw [h112, h104]
    exact Entails.of_eq (by ac_rfl)
  · have hpos : 0 < pqRatchetStatePBEncodedLen st := Nat.pos_of_ne_zero hzero
    have hcbz_f := ofNat_beq_zero_false_of_pos hpos hlen
    apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.call_cs (x := ())
      (F := pqRatchetStatePBPinnedAt A g a st ∗ A.pool ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
      hshim (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := entry + 544#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
    · intro R' hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, shimStackSpecOf, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hinv0.trans hinv1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    · intro sf code R' _ hm; exact allowPanic_not_exited hm
    · intro sf _ hm
      simp only [withStepInv, shimStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro s1 hpcs1 hruns1 hsps1 hcss1 hinv_s1
      simp only [arm64_norm, hsp] at hsps1
      obtain ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩ :=
        calleeSavedPreserved_writeLr_setPC hcss1
      rw [hx19] at hs1_19; rw [hx20] at hs1_20; rw [hx21] at hs1_21; rw [hx22] at hs1_22; rw [hx23] at hs1_23
      rw [hx25] at hs1_25; rw [hx27] at hs1_27; rw [hx28] at hs1_28; rw [hfp] at hs1_fp
      dsimp only [withStepInv, shimStackSpecOf]
      simp only [arm64_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_elim fun htrs1 => ?_
      have htrs1' : s1.trace = s0.trace := htrs1.trans htr
      apply SepWPp.of_sepWP_cs (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      have htoNat_len : (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)).toNat = pqRatchetStatePBEncodedLen st := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.call_cs (x := pqRatchetStatePBEncodedLen st)
        (F := pqRatchetStatePBPinnedAt A g a st ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
        halloc (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsps1, beq_iff_eq]; exact halign)
        (ret_pc := entry + 560#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
      · intro R' hm
        simp only [arm64_norm] at hm
        simp only [withStepInv, rustAllocStackSpecOf, arm64_norm, hsps1, htoNat_len,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨(hinv0.trans hinv1).trans (hinv_s1.trans hinv2), hpos, hlen⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
      · intro sf code R' _ hm; exact allowPanic_not_exited hm
      · intro sf _ hm
        simp only [withStepInv, rustAllocStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro s2 hpcs2 hruns2 hsps2 hcss2 hinv_s2
        simp only [arm64_norm, hsps1] at hsps2
        obtain ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩ :=
          calleeSavedPreserved_writeLr_setPC hcss2
        simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_25, hs1_27, hs1_28, hs1_fp]
          at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp
        have hinv_s2' : StepInv s0 s2 :=
          ((hinv0.trans hinv1).trans (hinv_s1.trans hinv2)).trans hinv_s2
        dsimp only [withStepInv, rustAllocStackSpecOf]
        simp only [arm64_norm, hsps1]
        by_cases hoom : s2.readReg64 .x0 = 0#64
        · simp only [hoom, ↓reduceIte]
          refine SepWPp.pure_elim fun htrs2 => ?_
          have htrs2' : s2.trace = s0.trace ++ [allocFailedEvent] := by rw [htrs2, htrs1']
          apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")); wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm_pan => ?_
          exact encodeToVecOnPanic_of_trace
            (by simpa only [Rust.panicked, wp_norm, arm64_norm] using htrs2') hm_pan
        · have hoom_f : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
          simp only [hoom, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_elim fun htrs2 => ?_
          have htrs2' : s2.trace = s0.trace := htrs2.trans htrs1'
          unfold encodeToVecLocalSlots
          cases hvn_case : st.versionNegotiation with
          | none =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
            apply SepWPp.of_sepWP_cs (mid := entry + 1212#64); wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun h => by rw [hvn_case] at h; cases h)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
            rw [← vecU8At_empty_of_alloc A (sp - 120#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            exact Entails.of_eq (by ac_rfl)
          | some vn =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_some, Bool.not_true] at hvn_eq hvn_ne
            apply SepWPp.of_sepWP_cs (mid := entry + 580#64); wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun _ => by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
            rw [← vecU8At_empty_of_alloc A (sp - 120#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            exact Entails.of_eq (by ac_rfl)

/-! ## 5. Exact-Capacity Callee Specs & Call Wrappers at `s.sp = sp - 144#64` -/

/-- Ghost state for exact-capacity `encode_varint [local#4]` (`0x4d710`) calls in `encode_to_vec`. -/
structure EtvEncodeVarintGhost where
  val : BitVec 64
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode_varint [local#4]` (`0x4d710`) contract at `s.sp = sp - 144#64`:
requires `bs.length + (Proto.encodeVarint val).length ≤ cap.toNat` and preserves `(cap, ptr)`. -/
def encodeVarintExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeVarint x.val) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Execute `bl encode_varint` (`0x4d710`, `entry + 18446744073709422336#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_encode_varint_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeVarint val).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨val, v, cap, ptr, bs⟩) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeVarintExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeVarintExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeVarintExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- Trace-preserving `memcpy` specification (definitionally equal to `sessionMemcpyRegionSpec`). -/
def etvMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun ⟨dst, src, bs⟩ s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun ⟨dst, src, bs⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

/-- Execute `bl memcpy` (`0x78a48`, `entry + 47672#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_memcpy_call
    (b : BitVec 64) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok (spqrProgAtExt b ext) call_pc etvMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [etvMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- Ghost state for exact-capacity `encode<ChainParams> [local#2]` (`0x52170`) calls in `encode_to_vec`. -/
structure EtvEncodeChainParamsGhost where
  tag : BitVec 32
  p : ChainParamsPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<ChainParams> [local#2]` (`0x52170`) contract at `s.sp = sp - 144#64`. -/
def encodeChainParamsExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeChainParamsGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      x.bs.length + (Proto.encodeMessage ChainParamsPB.encodeRaw x.tag x.p).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage ChainParamsPB.encodeRaw x.tag x.p) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Execute `bl encode<ChainParams> [local#2]` (`0x52170`, `entry + 18446744073709441376#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_encode_chainParams_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hcp : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hfit : bs.length + (Proto.encodeMessage ChainParamsPB.encodeRaw tag p).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeMessage ChainParamsPB.encodeRaw tag p) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨tag, p, v, cap, ptr, bs⟩) (F := F)
    hcp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeChainParamsExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeChainParamsExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- `Epoch::encoded_len [local#2]` (`0x664fc`) contract at `s.sp = sp - 144#64`. -/
def epochEncLenStackSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (BitVec 64 × ChainEpochPBGhost × ChainEpochPB) where
  pre := fun ⟨a, g, ep⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ chainEpochPBEncodedLen ep < 2 ^ 64⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun ⟨a, g, ep⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) ∧ sf.trace = s0.trace⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Execute `bl Epoch::encoded_len [local#2]` (`0x664fc`, `entry + 18446744073709524204#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_epoch_encLen_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hep : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (a sp ret_pc : BitVec 64) (g : ChainEpochPBGhost) (ep : ChainEpochPB)
    (hlen : chainEpochPBEncodedLen ep < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainEpochPBPinnedAt A g a ep ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((chainEpochPBPinnedAt A g a ep ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (a, g, ep)) (F := F)
    hep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, epochEncLenStackSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hlen⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, epochEncLenStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, epochEncLenStackSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))

/-- Ghost state for exact-capacity `encode<EpochDirection> [local#2]` (`0x527c0`) calls. -/
structure EtvEncodeEpochDirectionGhost where
  tag : BitVec 32
  dirA : BitVec 64
  g : EpochDirectionPBGhost
  dir : EpochDirectionPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<EpochDirection> [local#2]` (`0x527c0`) contract at `s.sp = sp - 144#64`. -/
def encodeEpochDirectionExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvEncodeEpochDirectionGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧ s.readReg64 .x1 = x.dirA ∧ s.readReg64 .x2 = x.v ∧
      x.bs.length + (Proto.encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir).length ≤ x.cap.toNat⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ Proto.encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Execute `bl encode<EpochDirection> [local#2]` (`0x527c0`, `entry + 18446744073709442992#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_encode_epochDirection_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hed : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (tag : BitVec 32) (dirA v cap ptr sp ret_pc : BitVec 64)
    (g : EpochDirectionPBGhost) (dir : EpochDirectionPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage EpochDirectionPB.encodeRaw tag dir).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA)
    (hx2 : s.readReg64 .x2 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (epochDirectionPBPinnedAt A g dirA dir ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((epochDirectionPBPinnedAt A g dirA dir ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage EpochDirectionPB.encodeRaw tag dir) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨tag, dirA, g, dir, v, cap, ptr, bs⟩) (F := F)
    hed hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeEpochDirectionExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeEpochDirectionExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

/-- Ghost state for exact-capacity `encode<Authenticator> [local#2]` (`0x522c0`) calls. -/
structure EtvEncodeAuthGhost where
  authA : BitVec 64
  g : AuthenticatorPBGhost
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<Authenticator> [local#2]` (`0x522c0`) contract at `s.sp = sp - 144#64`. -/
def authEncodeExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeAuthGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth).length ≤ x.cap.toNat⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Execute `bl encode<Authenticator> [local#2]` (`0x522c0`, `entry + 18446744073709441712#64`) at `s.sp = sp - 144#64`. -/
theorem step_etv_encode_auth_call {resStack : Nat}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {call_pc : BitVec 64} {s0 s : State}
    (hauth : subroutine_ok (spqrProgAtExt b ext) call_pc
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (authA v cap ptr sp ret_pc : BitVec 64)
    (g : AuthenticatorPBGhost) (auth : AuthenticatorPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (authenticatorPBPinnedAt A g authA auth ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp (spqrProgAtExt b ext) ret sm
        ((authenticatorPBPinnedAt A g authA auth ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp (spqrProgAtExt b ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨authA, g, auth, v, cap, ptr, bs⟩) (F := F)
    hauth hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, authEncodeExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, authEncodeExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, authEncodeExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem encodeVarint_length_pos (v : BitVec 64) : 0 < (Proto.encodeVarint v).length := by
  have h := protoEncodedLenVarint_eq_varintLen v
  unfold Proto.encodedLenVarint at h
  have hb := (varintLen_bounds v).1
  omega

theorem memRegion_four_eq (a : BitVec 64) : memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4)
    (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem exists_pointsTo64_eq_pointsTo32 (a : BitVec 64) :
    (∃∗ v : BitVec 64, a ↦₆₄ v) =
      (∃∗ v_hi : BitVec 32, ∃∗ v_lo : BitVec 32, (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi)) := by
  rw [← memRegion_eight_eq a,
    memRegion_split' (b := a) (b' := a + 4#64) (n := 4) (k := 4) (by decide) rfl (by decide),
    memRegion_four_eq a, memRegion_four_eq (a + 4#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem pointsTo64_entails_pointsTo32_pair (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ v_hi : BitVec 32, ∃∗ v_lo : BitVec 32, (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) := by
  rw [← exists_pointsTo64_eq_pointsTo32 a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem pointsTo32_pair_entails_exists_pointsTo64 (a : BitVec 64) (v_lo v_hi : BitVec 32) :
    (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ⊢ ∃∗ v : BitVec 64, a ↦₆₄ v := by
  rw [exists_pointsTo64_eq_pointsTo32 a]
  exact Entails.sepExists_right v_hi (Entails.sepExists_right v_lo (Entails.refl _))

theorem sepWPp_split_pointsTo64 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (a v : BitVec 64) (F : SepProp)
    (hP : P = (a ↦₆₄ v) ∗ F)
    (h : ∀ v_lo v_hi : BitVec 32,
      SepWPp prog ret s ((a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hP
  refine SepWPp.weaken_pre (sepConj_mono_left (pointsTo64_entails_pointsTo32_pair a v)) ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim fun v_hi => SepWPp.exists_elim fun v_lo =>
    SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (h v_lo v_hi)

theorem sepWPp_merge_pointsTo32 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (a : BitVec 64) (v_lo v_hi : BitVec 32) (F : SepProp)
    (hP : P = (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F)
    (h : ∀ v : BitVec 64, SepWPp prog ret s ((a ↦₆₄ v) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hP
  have hent : (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F ⊢ (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ F := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (pointsTo32_pair_entails_exists_pointsTo64 a v_lo v_hi)
  refine SepWPp.weaken_pre hent ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem vecU8Buf_eq_of_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs.isEmpty = false) (hle : bs.length ≤ cap.toNat) :
    EncodedLen.vecU8Buf A cap ptr bs =
      (ptr ↦ₛ bs) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hne)
  have hcap_ne : cap ≠ 0 := by
    intro heq; subst heq; change bs.length ≤ 0 at hle; omega
  unfold EncodedLen.vecU8Buf
  simp only [hcap_ne, ↓reduceIte]
  ac_rfl

end CryptoVerification.SpqrV1.Prost.EncodeToVec
