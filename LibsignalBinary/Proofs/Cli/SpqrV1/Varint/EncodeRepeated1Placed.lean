/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommon
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2Placed
import ProofLib.SepLogic.WPp

/-!
# Relocatable Verification of `prost::encoding::bytes::encode_repeated [local#3]` (Block `448`)

Proves `[LibsignalPlacement]` per-block contracts (`< 2 ^ 58` and `< 2 ^ 59` element bounds)
for `encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` (Block `448`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.SpqrV1.Varint

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (encodeRepeated59SpecOf setup_x24_eq_59 latch_sub24_eq_59)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed
open CryptoVerification.Cli.SpqrV1.Varint.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  LibsignalProtoCodec.encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

/-! ## 1. `< 2 ^ 58` Loop and General Block Contract (`encodeRepeatedSpecOf`) -/

/-- Loop over non-empty `elems` (`96 → 212`, `elems.length < 2 ^ 58`) on Block `448`. -/
theorem step_loop_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks)
    {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ [])
    (helem_cnt : elems.length < 2 ^ 58)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
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
    refine step_iter_placed hres A H henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine step_latch_zero_placed A H sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1))
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 58 := helem_cnt
      set tail := nextHead :: rest'
      refine step_latch_succ_placed A H v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
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

/-- Generalized `encode_repeated [local#3]` (`Block 448`) placed correctness (`< 2 ^ 58`). -/
theorem encode_repeated_1_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (blkPl_448).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeatedSpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_448 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeatedSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := step_loop_placed hres A H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeatedSpecOf resStack A).pre x s0, hpre, ?_⟩
  dsimp only [encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩ => ?_
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit ⊢
  cases elems with
  | nil =>
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
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
    have hx24_setup := setup_x24_eq helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => ?_
    refine SepWPp.exists_elim fun v1 => ?_
    refine SepWPp.exists_elim fun v2 => ?_
    refine SepWPp.exists_elim fun v3 => ?_
    refine SepWPp.exists_elim fun v4 => ?_
    refine SepWPp.exists_elim fun v5 => ?_
    refine SepWPp.exists_elim fun v6 => ?_
    refine SepWPp.exists_elim fun v7 => ?_
    refine SepWPp.exists_elim fun v8 => ?_
    refine SepWPp.exists_elim fun v9 => ?_
    apply (SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 96#64))
    wp_steps
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
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
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

/-! ## 2. `< 2 ^ 59` Exact-Capacity Loop and General Block Contract (`encodeRepeated59SpecOf`) -/

/-- Latch block when `k > 0` elements remain (`84..92 → 96`, `k + 1 < 2 ^ 59`) on Block `448`. -/
theorem step_latch_succ_59_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 96#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_448 H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R)) := by
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 96#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

/-- Loop over non-empty `elems` (`96 → 212`, `elems.length < 2 ^ 59`) on Block `448`. -/
theorem step_loop_59_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    (A : RustAlloc) (H : LibsignalHooks) {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (tag : Nat) (v sp : BitVec 64)
    (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    {s : State} {x0 : EncodeRepeatedGhost} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 212#64 →
      sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A v nextCap nextPtr (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool ∗ stackAt (sp - 80#64) (48 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x0 s0 sf ∗ R))) :
    SepWPp (lsProg_448 H) ret s P Q
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
    refine step_iter_placed hres A H henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs hfit_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine step_latch_zero_placed A H sp curBase hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 ?_
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
      refine step_latch_succ_59_placed A H v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
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

/-- Generalized `encode_repeated [local#3]` (`Block 448`) placed correctness (`< 2 ^ 59`). -/
theorem encode_repeated_1_59_gen_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks} {x : EncodeRepeatedGhost} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec)
    (hpc : s0.pc = (blkPl_448).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59SpecOf resStack A).pre x s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_448 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeRepeated59SpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeRepeatedSpec A).onPanic x s0 sf ∗ R)) := by
  have hloop := step_loop_59_placed hres A H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59SpecOf resStack A).pre x s0, hpre, ?_⟩
  dsimp only [encodeRepeated59SpecOf, encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit⟩ => ?_
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit ⊢
  cases elems with
  | nil =>
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
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
    apply SepWPp.of_sepWP_cs_placed (mid := (blkPl_448).base + 96#64)
    wp_steps
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
    apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
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

end EncodeRepeated1

/-! ## 3. Top-Level Placed Contracts for Block `448` (`< 2 ^ 58` and `< 2 ^ 59`) -/

theorem encode_repeated_1_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)))
    (hdoReserve0 : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_448 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_1_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpec A)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecX A)) :=
  encode_repeated_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_59_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {A : RustAlloc} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A)))
    (hdoReserve0 : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_448 H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf resStack A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := EncodeRepeated1.encode_repeated_1_59_gen_placed_ok hres
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
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStack A)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (encode_varint2_fit_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

theorem encode_repeated_1_59_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat H spqrRustReallocSym (rustReallocSpec A))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_448).rebase (blkPl_448).base H) (blkPl_448).base
      (withLsCodeLoaded lsmpl (encodeRepeated59SpecOf doReserveStackX A)) :=
  encode_repeated_1_59_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (encode_varint2_fit_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_448 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))
    (spqr_hook_ok_of_mem (show HookSat H spqrMemcpySym sessionMemcpyRegionSpec from hmc))

abbrev encodeRepeated1_placed_ok_of_callees := @encode_repeated_1_placed_ok_of_callees
abbrev encodeRepeated1_placed_ok := @encode_repeated_1_placed_ok
abbrev encodeRepeated1_placed_ok_x := @encode_repeated_1_placed_ok_x
abbrev encodeRepeated1_59_placed_ok_of_callees := @encode_repeated_1_59_placed_ok_of_callees
abbrev encodeRepeated1_59_placed_ok := @encode_repeated_1_59_placed_ok
abbrev encodeRepeated1_59_placed_ok_x := @encode_repeated_1_59_placed_ok_x
abbrev step_latch_succ_1_59_placed := @EncodeRepeated1.step_latch_succ_59_placed
abbrev step_loop_1_59_placed := @EncodeRepeated1.step_loop_59_placed
abbrev encode_repeated_1_59_gen_placed_ok := @EncodeRepeated1.encode_repeated_1_59_gen_placed_ok

end CryptoVerification.Cli.SpqrV1.Varint
