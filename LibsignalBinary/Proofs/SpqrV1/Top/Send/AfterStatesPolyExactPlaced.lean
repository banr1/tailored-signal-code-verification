/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedA
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlaced
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated1
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2
import ProofLib.SepLogic.WPp

/-!
# Relocatable `encode_repeated [local#1]` (`< 2 ^ 59`) and Exact-Capacity `PolynomialEncoder::encode [local#1]`

Verifies `encode_repeated_1_59_placed_ok` (Block 145) and
`encode_polyEncoder_1_exact_pinned_placed_ok` (Block 153) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Prost.MessageEncode
  CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## Placed `encode_repeated [local#1]` (Block 145) with `elems.length < 2 ^ 59` -/

section EncodeRepeated1_59Placed

attribute [local irreducible] LibsignalProtoCodec.encodeVarint encodeBytesField encodeRepeatedBytes

theorem step_latch_succ_1_59_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 84#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_145).base + 96#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_145 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht; omega
  have hx24_next := latch_sub24_eq_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_145).base + 96#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_loop_1_59_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 : State}
    (henc : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_145).base + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_145).base + 212#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_145 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_145 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  induction elems generalizing curBase curCap curPtr curBs s P F with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    rcases head with ⟨elemPtr, elemBs⟩
    subst hP
    simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit
    have hfit_head : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
        curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine EncodeRepeated1.step_iter_placed hres A H henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine EncodeRepeated1.step_latch_zero_placed A H sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1))
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 59 := helem_cnt
      set tail := nextHead :: rest'
      refine step_latch_succ_1_59_placed A H v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
        tail.length hrest_pos helem_cnt'
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 ?_
      intro s1' hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
      have hfit_rest : (curBs ++ encodeBytesField tag (some elemBs)).length +
          (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat ∨
          (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length + 10 < 2 ^ 62 := by
        rw [List.length_append]
        rcases hfit with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      refine ih hrest_ne (by omega) (curBase + 24#64) cap1 ptr1
        (curBs ++ encodeBytesField tag (some elemBs)) hfit_rest
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗ F)
        hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
        (by ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 hge2 hpres2
      have hpres_all : curBs.length +
          (encodeRepeatedBytes tag (((elemPtr, elemBs) :: tail).map Prod.snd)).length ≤
          curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap
        simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit_cap
        obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
        have h2 : (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat := by
          rw [hc1, List.length_append]; omega
        obtain ⟨hc2, hp2⟩ := hpres2 h2
        exact ⟨hc2.trans hc1, hp2.trans hp1⟩
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 (by omega) hpres_all)
      clear_value tail
      rw [repeatedBytesSliceAt_cons, List.map_cons, encodeRepeatedBytes_cons, ← List.append_assoc]
      exact Entails.of_eq (by ac_rfl)

theorem encode_repeated_1_59_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (blkPl_145).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59SpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_145 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeated59SpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := step_loop_1_59_placed hres A H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59SpecOf resStack A).pre x s0, hpre, ?_⟩
  dsimp only [encodeRepeated59SpecOf, encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩ => ?_
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit ⊢
  cases elems with
  | nil =>
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap.toNat ∧
        (bs.length +
            (encodeRepeatedBytes tag
              (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).length ≤ cap.toNat →
          cap = cap ∧ ptr = ptr)) = True :=
      eq_true ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨cap, ptr, by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    simpa only [List.map_nil, encodeRepeatedBytes_nil, List.append_nil, sepConj_assoc] using hPR
  | cons head rest =>
    have hne : head :: rest ≠ [] := List.cons_ne_nil _ _
    have hpos : 0 < (head :: rest).length := List.length_pos_of_ne_nil hne
    have hcbz : (BitVec.ofNat 64 (head :: rest).length == 0#64) = false :=
      len_beq_zero_false hpos (by omega)
    have hx24_setup := setup_x24_eq_59 helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
      SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
      SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
      SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
      SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => ?_
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_145).base + 96#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_pro
    have hx20_setup := setup_x20_eq htag2
    set savedCells : SepProp :=
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
      ((s0.sp - 56#64) ↦₆₄ v3) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
    have hpre_loop :
        repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (48 + resStack) ∗ savedCells =
        (repeatedBytesSliceAt base (head :: rest) ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
          stackAt (s0.sp - 80#64) (48 + resStack)) ∗ savedCells := by
      simp only [sepConj_assoc]
    clear_value savedCells
    have halign64 : s0.sp &&& 15#64 = 0#64 := by
      simpa only [State.spAligned, beq_iff_eq] using halign
    refine hloop tag v s0.sp (head :: rest) hne helem_cnt base cap ptr bs hfit
      (F := savedCells)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign64
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      ((EncRepeatedCalleeSavedPlaced.refl s0).step (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv_pro)
      hpre_loop ?_
    intro sm cap' ptr' hpcm hrunm hspm htrm hcsm hge hpres
    rcases hcsm with ⟨hx26m, hx27m, hx28m, hvregsm, _⟩
    rw [hsaved_def]
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
    intro hPR
    have hpure : (cap.toNat ≤ cap'.toNat ∧
        (bs.length + (encodeRepeatedBytes tag ((head :: rest).map Prod.snd)).length ≤ cap.toNat →
          cap' = cap ∧ ptr' = ptr)) = True :=
      eq_true ⟨hge, hpres⟩
    simp only [satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 25#5), v3, s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 19#5), cap', ptr',
      by simp only [arm64_norm, *], ?_⟩
    rw [hpure, pure_true, emp_sepConj]
    convert hPR using 1
    ac_rfl

theorem encode_repeated_1_59_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_145 H) (lsmpl.base 148)
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)))
    (hdoReserve0 : subroutine_ok (lsProg_145 H) (lsmpl.base 157)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_145 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_145 H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encode_repeated_1_59_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_59_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_145).rebase (blkPl_145).base H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStack A)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_59_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_145).rebase (blkPl_145).base H) (blkPl_145).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStackX A)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_145 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

end EncodeRepeated1_59Placed

/-! ## Exact-Capacity `PolynomialEncoder::encode [local#1]` (Block 153) -/

private theorem step_pe1_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_153 H) (lsmpl.base 173)
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencVarint : subroutine_ok (lsProg_153 H) (lsmpl.base 148)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8))
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_153).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗
      vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_153).base + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_153 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A encA g ptsElems polysElems ∗
          vecU8At A v cap0 ptr0 (bs0 ++ polyEncoderHeaderBytes pb) ∗ A.pool ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_153 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_153 H) (blkPl_153).base :=
    Or.inr (Or.inl ⟨‹_›, H, rfl, rfl⟩)
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  have hlt0 : bs0.length < cap0.toNat := by omega
  have hcap_f : (cap0 == BitVec.ofNat 64 bs0.length) = false := cap_beq_len_false_of_lt_placed hlt0
  refine step_polyEncoder_prologue_placed hres hfn encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ vecU8At A v cap0 ptr0 bs0 ∗ A.pool ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1
  rw [EncodedLen.vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0, vecHeader]
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_153).base + 40#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v cap0 ptr0 bs0]
  refine step_polyEncoder_push_hdr_tag_placed A hfn encA v cap0 ptr0 sp bs0 hlt0
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (F := stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      Poly.protoPolynomialEncoderPinnedAt A g encA pb ∗ A.pool ∗ F)
    (by ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 173); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_173, *])
    (by simp only [arm64_norm, *]); intro hinv3
  refine step_msg48rep_polyEncLen_call_placed hres128 A hencLen encA sp ((blkPl_153).base + 68#64) g pb hlen_lt
    (F := vecU8At A v cap0 ptr0 (bs0 ++ [0x12#8]) ∗ A.pool ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_173, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv3)
    (by ac_rfl) ?_
  intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4 hcs34 hcs4
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyEncoder_mov_x1_x19_68_placed hfn
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) encA v sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 148); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_148, *])
    (by simp only [arm64_norm, *]); intro hinv5
  have hfit_len : (bs0 ++ [0x12#8]).length +
      (LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  refine step_msg48rep_encode_varint_call_placed hres128 A hencVarint
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_153).base + 76#64)
    (bs0 ++ [0x12#8]) (Or.inl hfit_len)
    (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      polyEncoderRestAt A encA g ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_148, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs5.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv5)
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [bs0_append_polyEncoderHeaderBytes bs0 pb]
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s6 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

private theorem step_pe1_idx_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_153 H) (lsmpl.base 148)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (encA v curCap curPtr sp : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hfit_idx : curBs.length + (Proto.encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_153).base + 76#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_153).base + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_153 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A v curCap curPtr (curBs ++ Proto.encodeUint32Field 1#32 pb.idx) ∗
          A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp (lsProg_153 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_153 H) (blkPl_153).base :=
    Or.inr (Or.inl ⟨‹_›, H, rfl, rfl⟩)
  refine step_polyEncoder_check_idx_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false := cap_beq_len_false_of_lt_placed hlt0
    rw [EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs, vecHeader]
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_153).base + 100#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
    rw [← vecHeader, ← EncodedLen.vecU8At_eq_header_sep_buf A v curCap curPtr curBs]
    refine step_polyEncoder_push_idx_tag_placed A hfn encA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv1)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ A.pool ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3
    apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 148); wp_steps
    apply SepWP.done
      (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_148, *])
      (by simp only [arm64_norm, *]); intro hinv3
    have hfit_v : (curBs ++ [0x08#8]).length +
        (LibsignalProtoCodec.encodeVarint (pb.idx.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_msg48rep_encode_varint_call_placed hres A hencVarint
      (pb.idx.zeroExtend 64) v curCap curPtr sp ((blkPl_153).base + 128#64) (curBs ++ [0x08#8]) (Or.inl hfit_v)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_148, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) hinv3)
      (by ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [bs_append_idx_of_ne_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hidx, ↓reduceIte] at hpc1
    rw [← bs_append_idx_of_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

private theorem step_pe1_pts_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_153 H) (lsmpl.base 145)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A)))
    (encA v curCap curPtr sp sv3 : BitVec 64) (g : Poly.ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))) (curBs : List (BitVec 8))
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts59 : pb.pts.length < 2 ^ 59)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys59 : pb.polys.length < 2 ^ 59)
    (hfit_pts : curBs.length + (Varint.encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat)
    (hfit_polys : (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts).length +
      (Varint.encodeRepeatedBytes 3 pb.polys).length ≤ curCap.toNat)
    {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_153).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        vecU8At A v curCap curPtr
          ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
        A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_153 H) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hfn : IsPolyEncoderEncodeEntryProg (lsProg_153 H) (blkPl_153).base :=
    Or.inr (Or.inl ⟨‹_›, H, rfl, rfl⟩)
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hpolys_len : polysElems.length = pb.polys.length := by rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_pts_placed hfn encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 145); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_145, *])
    (by simp only [arm64_norm, *]); intro hinv1
  refine step_msg48_encode_repeated59_call_placed A hencRep 2 g.pts.ptr v curCap curPtr sp
    ((blkPl_153).base + 144#64) ptsElems curBs (by decide) (by decide) (by omega) (by rw [hpts_eq]; exact Or.inl hfit_pts)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.polys.ptr polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_145, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) hinv1)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 _ hpres2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq] at hpres2 ⊢
  obtain ⟨hcap2, hptr2⟩ := hpres2 hfit_pts
  subst cap2 ptr2
  refine step_polyEncoder_prep_polys_epilogue_placed hfn encA v sp sv3 g pb ptsElems polysElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At A v curCap curPtr (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ∗
      A.pool ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by dsimp only [polyEncoderElemsAt]; ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hw0_3 hx1_3 hx2_3 hx3_3 hcc3 hcs3
  apply SepWPp.of_sepWP_cs_placed (mid := lsmpl.base 145); wp_steps
  apply SepWP.done
    (by simp only [arm64_norm, blkPl_153_ρ, ls_resolve_blk_145, *])
    (by simp only [arm64_norm, *]); intro hinv3
  exact step_msg48_encode_repeated59_tailcall_placed
    (s := s3.setPC (lsmpl.base 145))
    hres A hencRep 3 g.polys.ptr v curCap curPtr sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems
    (curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) (by decide) (by decide) (by omega)
    (by rw [hpolys_eq]; exact Or.inl hfit_polys)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun3)
    ((State.sp_setPC _ _).trans hsp3)
    halign
    ((State.trace_setPC _ _).trans htr3)
    ((State.readReg64_setPC _ _ _).trans hlr3)
    (by dsimp only [State.readReg32] at hw0_3 ⊢; rw [State.readReg64_setPC]; exact hw0_3)
    ((State.readReg64_setPC _ _ _).trans hx1_3)
    (by rw [State.readReg64_setPC, hpolys_len]; exact hx2_3)
    ((State.readReg64_setPC _ _ _).trans hx3_3)
    (calleeSavedPreserved_setPC_placed _ hcc3)
    (msgEnc48CalleeSavedPlaced_setPC _ hcs3 hinv3)
    (by dsimp only [polyEncoderElemsAt]; try ac_rfl)
    (fun sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf _ hpres3 => by
      rw [hpolys_eq] at hpres3 ⊢
      obtain ⟨hncap, hnptr⟩ := hpres3 hfit_polys
      subst nextCap nextPtr
      have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
      have hEq :
          ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
            vecU8At A v curCap curPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
          ((repeatedBytesSliceAt g.polys.ptr polysElems ∗
            vecU8At A v curCap curPtr
              ((curBs ++ Varint.encodeRepeatedBytes 2 pb.pts) ++ Varint.encodeRepeatedBytes 3 pb.polys) ∗
            A.pool ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
            (((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
              ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)) := by
        dsimp only [polyEncoderElemsAt]; ac_rfl
      rw [hEq] at hq
      exact hq)

theorem polyEncoder1_exact_gen_placed_ok [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    {x : EncodePolyEncoderPinnedGhost} {R : SepProp} {s0 : State}
    (hencLen : subroutine_ok (lsProg_153 H) (lsmpl.base 173)
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A)))
    (hencV : subroutine_ok (lsProg_153 H) (lsmpl.base 148)
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hencR : subroutine_ok (lsProg_153 H) (lsmpl.base 145)
      (withMsgEnc48CSPlaced s0 (encodeRepeated59SpecOf resStack A)))
    (hpc : s0.pc = (blkPl_153).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).pre x s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_153 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodePolyEncoderExactSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodePolyEncoderExactSpecOf] at hpre_pure
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hx0, hx1, hfit⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s0.sp (msgEnc48RepeatedStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodePolyEncoderMsg_len_split x.enc
  have hlen_le_msg := polynomialEncoderPBEncodedLen_le_msg_len x.enc
  have hcap_lt : x.cap.toNat < 2 ^ 64 := BitVec.isLt x.cap
  have hlen_lt : polynomialEncoderPBEncodedLen x.enc < 2 ^ 64 := by omega
  refine step_pe1_hdr_exact_placed hres A H hencLen hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc x.bs
    hlen_lt (by omega) (F := emp) rfl hpc hrun rfl halign rfl hx0 hx1 (MsgEnc48CalleeSavedPlaced.refl s0) rfl ?_
  intro s1 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
  have hfit_idx : (x.bs ++ polyEncoderHeaderBytes x.enc).length +
      (Proto.encodeUint32Field 1#32 x.enc.idx).length ≤ x.cap.toNat := by
    rw [List.length_append]; omega
  refine step_pe1_idx_exact_placed hres128 A H hencV x.encA x.v x.cap x.ptr s0.sp x.g x.enc
    ptsElems polysElems (x.bs ++ polyEncoderHeaderBytes x.enc) hfit_idx
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hcs1
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗
      msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
  let bs_idx := (x.bs ++ polyEncoderHeaderBytes x.enc) ++ Proto.encodeUint32Field 1#32 x.enc.idx
  have hfit_pts : bs_idx.length + (Varint.encodeRepeatedBytes 2 x.enc.pts).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append]; omega
  have hfit_polys : (bs_idx ++ Varint.encodeRepeatedBytes 2 x.enc.pts).length +
      (Varint.encodeRepeatedBytes 3 x.enc.polys).length ≤ x.cap.toNat := by
    dsimp [bs_idx]; rw [List.length_append, List.length_append, List.length_append]; omega
  refine step_pe1_pts_polys_exact_placed hres A H hencR x.encA x.v x.cap x.ptr s0.sp sv3 x.g x.enc
    ptsElems polysElems bs_idx hpts_eq (by omega) hpolys_eq (by omega) hfit_pts hfit_polys
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := polyEncoderRestAt A x.encA x.g ptsElems polysElems ∗ emp) (by dsimp [bs_idx]; ac_rfl) ?_
  intro sf _ _ hspf htrf hccf _
  refine ⟨fun hm => ?_, hspf, hccf⟩
  have hm_pack : sf.mem ⊨ (polyEncoderElemsAt x.encA x.g x.enc ptsElems polysElems ∗
      polyEncoderRestAt A x.encA x.g ptsElems polysElems) ∗
      (vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
        A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack) ∗ R) := by
    rw [bs0_append_encodePolyEncoderMsg x.bs x.enc]
    convert hm using 1; dsimp [bs_idx]; ac_rfl
  have hm_pinned := (satisfies_protoPolynomialEncoderPinnedAt_iff A x.g x.encA x.enc _ sf.mem).mpr
    ⟨ptsElems, polysElems, hpts_eq, hpts_lt, hpolys_eq, hpolys_lt, hm_pack⟩
  dsimp only [encodePolyEncoderExactSpecOf]; rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  convert hm_pinned using 1; ac_rfl

theorem encode_polyEncoder_1_exact_pinned_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_153 H) (blkPl_153).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStack A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyEncoder1_exact_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_59_placed_ok h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

theorem encode_polyEncoder_1_exact_pinned_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_153 H) (blkPl_153).base
      (withLsCodeLoaded lsmpl (encodePolyEncoderExactSpecOf doReserveStackX A)) := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := polyEncoder1_exact_gen_placed_ok (by decide)
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (subroutine_ok_withLsCodeLoaded
        (subroutine_ok_polyEncLenElemsOut_of_pinned
          (polynomialEncoderEncodedLen_local1_pinned_placed_ok_ext A H))))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (subroutine_ok_withMsgEnc48CSPlaced_placed_blk s0 hcl0
      (encode_repeated_1_59_placed_ok_x h_panic hshim halloc hrealloc
        (show HookSat H spqrMemcpySym framelessMemcpySpec from hmc)))
    hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

end CryptoVerification.SpqrV1.Top.Send
