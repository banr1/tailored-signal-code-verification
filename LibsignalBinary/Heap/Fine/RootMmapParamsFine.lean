/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupProof
public import LibsignalBinary.Heap.Fine.Inv

/-!
# Fine Root `mmap` Size and Count Selection Lemmas

Strengthens `RootMmapParamsOk sc cnt_f len` on `alloc_group`'s root `mmap` path (`blk08`) to
`RootMmapParamsFine sc cnt_f len`, recording `cnt_f = 1 → 24 ≤ sc`,
`len ≤ pageAlignUp (cnt_f * slotStride sc + 16)`, and `len ≤ Cost.grpMax sc 128`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

arm64_proof_prelude

def RootMmapParamsFineBase (sc cnt_f len : Nat) : Prop :=
  VerifiedLibraries.Mallocng.Proofs.RootMmapParamsOk sc cnt_f len ∧
  (cnt_f = 1 → 24 ≤ sc) ∧
  len ≤ Arm64.pageAlignUp (cnt_f * VerifiedLibraries.Mallocng.Proofs.slotStride sc + 16)

def RootMmapParamsFine (sc cnt_f len : Nat) : Prop :=
  VerifiedLibraries.Mallocng.Proofs.RootMmapParamsOk sc cnt_f len ∧
  (cnt_f = 1 → 24 ≤ sc) ∧
  len ≤ Arm64.pageAlignUp (cnt_f * VerifiedLibraries.Mallocng.Proofs.slotStride sc + 16) ∧
  len ≤ VerifiedLibraries.Mallocng.Proofs.Cost.grpMax sc 128

private theorem pageAlignUp_mono_fine {a b : Nat} (h : a ≤ b) :
    pageAlignUp a ≤ pageAlignUp b := by
  unfold pageAlignUp PAGE_SIZE
  exact Nat.mul_le_mul_right 4096 (Nat.div_le_div_right (by omega))

private theorem lsl1_32_fine {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 32 cnt)[30] = false ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) &&& 4294967295#64 = BitVec.ofNat 64 (2 * cnt) := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
    change Nat.testBit (cnt % (2 ^ 32)) 30 = false
    rw [Nat.mod_eq_of_lt (by omega)]
    exact Nat.testBit_lt_two_pow (by omega)
  · have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) = BitVec.ofNat 64 (2 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (2 * cnt)).ult 65#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change (2 * cnt) % (2 ^ 64) < 65
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

private theorem mul_stride_cnt_fine {cnt stride : Nat} :
    BitVec.ofNat 64 stride * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * stride) := by
  rw [Nat.mul_comm]; exact (BitVec.ofNat_mul stride cnt).symm

private theorem root_small5_check_fine :
    ((List.range 26).all fun sc => 5 * slotStride sc + 16 ≤ 65536) = true := by decide +kernel

private theorem rootMmapParamsFineBase_of_cnt {sc cnt : Nat}
    (hm0 : 0 < cnt * slotStride sc + 16)
    (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32)
    (h1M : cnt * slotStride sc + 16 ≤ 1048576)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 16 ≤ 65536)
    (hc1_24 : cnt = 1 → 24 ≤ sc) :
    RootMmapParamsFineBase sc cnt (pageAlignUp (cnt * slotStride sc + 16)) :=
  ⟨rootMmapParams_of_cnt hm0 hlo hhi h1M h25 hc1_24, hc1_24, Nat.le_refl _⟩

private theorem wp_root_req_round_core [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req cnt_cur len_cur : Nat) (Frame : SepProp) (Q : Nat → Nat → Prop)
    (_hw768 : Blk08HasWords768 svc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (h25_stride : sc ≤ 25 → slotStride sc + 16 ≤ 65536)
    (hCur : RootMmapParamsFineBase sc cnt_cur len_cur)
    (hCurLen : len_cur = pageAlignUp (cnt_cur * slotStride sc + 16))
    (hQ_cur : Q cnt_cur len_cur) (hQ_1 : Q 1 (pageAlignUp (req + 20)))
    (hpc : s.pc = mbase 8 + allocSlotOff_req_round) (hrun : s.status = .Running)
    (hx3 : s.readReg64 .x3 = 4095#64) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt_cur)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 len_cur) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsFineBase sc cnt_f len ∧ Q cnt_f len ∧
        (∀ x5, Cost.RootLenOk sc cnt_cur len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_req_round, allocSlotOff_mmap_go] at hpc ⊢
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have hreq_hi : req + 20 ≤ slotStride sc + 16 := by
    unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
  obtain ⟨hbv_req, h4096_req, hdvd_req, hle1M_req, hle64_req⟩ :=
    align4096_bv_eq (m := req + 20) (by omega) (by omega)
  have hge_req := pageAlignUp_le (req + 20)
  have hlt_req := pageAlignUp_lt (req + 20)
  have h4_req : 0 < pageAlignUp (req + 20) / 4096 := Nat.div_pos h4096_req (by omega)
  have hcap_req :
      12 + 1 * (if (1 : Nat) - 1 == 0 && 0 < pageAlignUp (req + 20) / 4096
        then pageAlignUp (req + 20) - 16 else slotStride sc) < pageAlignUp (req + 20) := by
    simp only [Nat.sub_self, beq_self_eq_true, Bool.true_and, decide_eq_true h4_req, ↓reduceIte]
    omega
  have hr20 : BitVec.ofNat 64 req + 20#64 = BitVec.ofNat 64 (req + 20) := (BitVec.ofNat_add req 20).symm
  have hx25_eq : ∀ (c_neg : BitVec 64), c_neg + 20#64 = 0#64 →
      ((c_neg - BitVec.ofNat 64 req) &&& 4095#64) + BitVec.ofNat 64 (req + 20) =
        BitVec.ofNat 64 (pageAlignUp (req + 20)) := fun c_neg hc => by
    rw [neg_k_sub 20#64 _ _ hc, hr20, hbv_req]
  have hx0_nat : (BitVec.ofNat 64 (slotStride sc) + 16#64).toNat = slotStride sc + 16 := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  wp_sym_steps
  wp_if hlo1
  · have hlt_str : pageAlignUp (req + 20) < slotStride sc + 16 := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1
      exact hlo1
    have hsc24_1 : 24 ≤ sc := by
      apply Classical.byContradiction; intro hlt24
      have := slotStride_le_2336_of_le_24 (by omega : sc ≤ 24)
      omega
    have hlen_le_1 : pageAlignUp (req + 20) ≤ pageAlignUp (1 * slotStride sc + 16) :=
      pageAlignUp_mono_fine (by omega)
    have hFine1 : RootMmapParamsFineBase sc 1 (pageAlignUp (req + 20)) :=
      ⟨⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req,
        fun hs => hle64_req (by have := h25_stride hs; omega),
        fun _ => Or.inl (by omega), hcap_req⟩,
       fun _ => hsc24_1, hlen_le_1⟩
    have hLen1 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
      fun _ => Or.inl (by have := pageAlignUp_le (slotStride sc + 16); omega)
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hFine1, hQ_1, hLen1,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp, ?_, ?_, rfl⟩
    · simp; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req]
    · intro r h0 h20 h25 h26
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
        State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
  · have hge_str : slotStride sc + 16 ≤ pageAlignUp (req + 20) := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1
      omega
    wp_sym_steps
    wp_if hlo2
    · have hlt16k : pageAlignUp (req + 20) < 16384 := by
        rw [hx25_eq _ (by decide)] at hlo2
        have h16k : ∀ (rhs : BitVec 64), rhs.toNat = 16384 →
            ((BitVec.ofNat 64 (pageAlignUp (req + 20))).ult rhs = true) →
            pageAlignUp (req + 20) < 16384 := fun rhs hrhs hn => by
          rw [BitVec.ult, decide_eq_true_eq, hrhs, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hn
          exact hn
        exact h16k _ (by decide) hlo2
      have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
        fun _ => Or.inr ⟨hCurLen, fun _ _ h => absurd h (by omega)⟩
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hQ_cur, hLenCur,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
        by simpa using hx20, by simpa using hx26, ?_, rfl⟩
      intro r h0 _ h25 _
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
    · have hge16k : 16384 ≤ pageAlignUp (req + 20) := by
        rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo2
        change ¬ pageAlignUp (req + 20) < 16384 at hlo2; omega
      have hsc24 : 24 ≤ sc := by
        apply Classical.byContradiction; intro hlt24
        have := slotStride_le_2336_of_le_24 (by omega : sc ≤ 24)
        omega
      have hAlignEq : pageAlignUp (req + 20) = pageAlignUp (slotStride sc + 16) := by
        obtain ⟨qr, hqr⟩ := hdvd_req
        obtain ⟨qs, hqs⟩ := pageAlignUp_dvd (slotStride sc + 16)
        have hle_s := pageAlignUp_le (slotStride sc + 16)
        have hlt_s := pageAlignUp_lt (slotStride sc + 16)
        omega
      have hFine2 : RootMmapParamsFineBase sc 1 (pageAlignUp (req + 20)) :=
        ⟨⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req,
          fun hs => hle64_req (by have := h25_stride hs; omega),
          fun _ => Or.inr ⟨hsc24, hAlignEq⟩, hcap_req⟩,
         fun _ => hsc24, by simp [hAlignEq]⟩
      wp_sym_steps
      have hhi_cur : cnt_cur ≤ 32 := hCur.1.2.1
      have hw20 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt_cur) = BitVec.ofNat 64 cnt_cur := by bv_omega
      have ⟨hc30, hlsl1⟩ := lsl1_32_fine hhi_cur
      by_cases hcond : (BitVec.ofNat 64 (2 * cnt_cur)).ule (s.readReg64 (Reg.gpr 2#5)) = true
      · have hLenCur : ∀ x5, Cost.RootLenOk sc cnt_cur len_cur (s.readReg64 .x2) x5 :=
          fun _ => Or.inr ⟨hCurLen, fun _ _ _ => hcond⟩
        refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hQ_cur, hLenCur,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp [hc30, hlsl1, hcond, hw20], by simp [hc30, hlsl1, hcond, hCurLen], ?_, rfl⟩
        intro r h0 h20 h25 h26
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
          State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]
      · have hLen2 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 :=
          fun _ => Or.inl (Nat.le_of_eq hAlignEq)
        refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hFine2, hQ_1, hLen2,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl,
          by simp [hc30, hlsl1, hcond],
          by simp [hc30, hlsl1, hcond]; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req], ?_, rfl⟩
        intro r h0 h20 h25 h26
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h20, State.readReg64_writeReg64_ne _ _ _ _ h26,
          State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25]

private theorem wp_root_cnt_mul_core [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req c : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 svc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hclo : 2 ≤ c) (hchi : c ≤ 5)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_mul) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 c) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 c)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsFineBase sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        (∀ x5, Cost.RootLenOk sc c len (s.readReg64 .x2) x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have h5_25 : sc ≤ 25 → 5 * slotStride sc + 16 ≤ 65536 := fun hs => by
    simpa [decide_eq_true_eq] using
      List.all_eq_true.mp root_small5_check_fine sc (List.mem_range.mpr (by omega))
  have hc_25 : sc ≤ 25 → c * slotStride sc + 16 ≤ 65536 := fun hs => by
    have : c * slotStride sc ≤ 5 * slotStride sc := Nat.mul_le_mul_right _ hchi
    have := h5_25 hs; omega
  have h1_25 : sc ≤ 25 → slotStride sc + 16 ≤ 65536 := fun hs => by have := h5_25 hs; omega
  have h1M : c * slotStride sc + 16 ≤ 1048576 := by
    have : c * slotStride sc ≤ 5 * 131056 := Nat.mul_le_mul hchi hshi; omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := c * slotStride sc + 16) (by omega) h1M
  have hFine_c := rootMmapParamsFineBase_of_cnt (by omega) (by omega) (by omega) h1M hc_25 (by omega)
  have hadd16 : BitVec.ofNat 64 (c * slotStride sc) + 16#64 =
      BitVec.ofNat 64 (c * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
    (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
      sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
      sj.readReg64 .x20 = BitVec.ofNat 64 c ∧
      sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
      sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
      sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (c * slotStride sc + 16)) ∧
      ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x26 → sj.readReg64 r = s.readReg64 r) ?_ ?_
  · dsimp only [allocSlotOff_cnt_mul, allocSlotOff_req_round] at hpc ⊢
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
      by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24,
      by simpa using hx25, ?_, ?_⟩, by sep_entail⟩
    · rw [mul_stride_cnt_fine]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
    · intro r h0 h3 h26
      simp only [State.readReg64_setPC,
        State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0,
        State.readReg64_writeReg64_ne _ _ _ _ h3]
  · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
    have hr := wp_root_req_round_core sj sc req c
      (pageAlignUp (c * slotStride sc + 16)) Frame (fun cnt_f len => cnt_f = 1 → req + 20 ≤ len)
      hw768 hsc hReq h1_25 hFine_c rfl (by omega) (fun _ => pageAlignUp_le (req + 20))
      hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
    refine SepWP.mono hr ?_
    intro sf P_f _ _ ⟨cnt_f, len, hFine, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    have hx2j : sj.readReg64 .x2 = s.readReg64 .x2 := hjr _ (by decide) (by decide) (by decide)
    exact ⟨cnt_f, len, hFine, hRq, by rw [← hx2j]; exact hLen,
      h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
      h6, h7, fun r r0 r3 r20 r25 r26 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r3 r26), hPf⟩

private theorem wp_root_mmap_prep_core [MallocngMultiPlacement] {svc : State → State}
    (s : State) (sc req cnt' : Nat) (Frame : SepProp)
    (hw768 : Blk08HasWords768 svc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hc1_24 : cnt' = 1 → 24 ≤ sc)
    (hprod : cnt' * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hpc : s.pc = mbase 8 + allocSlotOff_mmap_prep) (hrun : s.status = .Running)
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc svc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsFineBase sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        Cost.RootLenOk sc cnt' len (s.readReg64 .x2) (s.readReg64 .x5) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
          sf.readReg64 r = s.readReg64 r) ∧
        P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have h1M := stride_prod_plus16_le hsc hprod
  have hc_25 : sc ≤ 25 → cnt' * slotStride sc + 16 ≤ 65536 := fun hs => by have := h25 hs; omega
  have h1_25 : sc ≤ 25 → slotStride sc + 16 ≤ 65536 := fun hs => by
    have : 1 * slotStride sc ≤ cnt' * slotStride sc := Nat.mul_le_mul hlo (Nat.le_refl _)
    have := h25 hs; omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := cnt' * slotStride sc + 16) (by omega) h1M
  have hFine_c := rootMmapParamsFineBase_of_cnt (by omega) hlo hhi h1M hc_25 hc1_24
  have hCurReq : cnt' = 1 → req + 20 ≤ pageAlignUp (cnt' * slotStride sc + 16) := fun hc1 => by
    subst hc1
    have : req + 20 ≤ 1 * slotStride sc + 16 := by
      unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
    have := pageAlignUp_le (1 * slotStride sc + 16); omega
  have hadd16 : BitVec.ofNat 64 (cnt' * slotStride sc) + 16#64 =
      BitVec.ofNat 64 (cnt' * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  dsimp only [allocSlotOff_mmap_prep, allocSlotOff_mmap_go] at hpc ⊢
  wp_sym_steps
  wp_if hne
  · refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
      (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧
        sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
        sj.readReg64 .x20 = BitVec.ofNat 64 cnt' ∧
        sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
        sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (cnt' * slotStride sc + 16)) ∧
        ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x26 → r ≠ .x27 → sj.readReg64 r = s.readReg64 r) ?_ ?_
    · dsimp only [allocSlotOff_req_round]
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl,
        by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24,
        by simpa using hx25, ?_, ?_⟩, by sep_entail⟩
      · rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
      · intro r r0 r1 r3 r26 r27
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ r26, State.readReg64_writeReg64_ne _ _ _ _ r27,
          State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1,
          State.readReg64_writeReg64_ne _ _ _ _ r3]
    · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
      have hr := wp_root_req_round_core sj sc req cnt'
        (pageAlignUp (cnt' * slotStride sc + 16)) Frame (fun cnt_f len => cnt_f = 1 → req + 20 ≤ len)
        hw768 hsc hReq h1_25 hFine_c rfl hCurReq (fun _ => pageAlignUp_le (req + 20))
        hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
      dsimp only [allocSlotOff_mmap_go] at hr
      refine SepWP.mono hr ?_
      intro sf P_f _ _ ⟨cnt_f, len, hFine, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
      have hx2j : sj.readReg64 .x2 = s.readReg64 .x2 :=
        hjr _ (by decide) (by decide) (by decide) (by decide) (by decide)
      exact ⟨cnt_f, len, hFine, hRq, by rw [← hx2j]; exact hLen _,
        h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2,
        h6, h7, fun r r0 r1 r3 r20 r25 r26 r27 =>
          (hregs r r0 r20 r25 r26).trans (hjr r r0 r1 r3 r26 r27), hPf⟩
  · refine SepWP.done rfl (by simp [hrun]) ⟨cnt', pageAlignUp (cnt' * slotStride sc + 16), hFine_c, hCurReq,
      Or.inr ⟨rfl, fun hc hx5 _ => (root_skip_x5_ne hc hx5 hne).elim⟩,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20, ?_, ?_, rfl⟩
    · rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c]
    · intro r r0 r1 r3 _ _ r26 r27
      simp only [State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64_ne _ _ _ _ r26, State.readReg64_writeReg64_ne _ _ _ _ r27,
        State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1,
        State.readReg64_writeReg64_ne _ _ _ _ r3]

set_option maxHeartbeats 800000 in
theorem wp_root_size_select_req_fine [MallocngMultiPlacement]
    (s : State) (sc req cnt' : Nat) (use : BitVec 64) (Frame : SepProp)
    (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hgt2048 : 2048 < cnt' * slotStride sc + 16) (hprod : cnt' * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hcnt' : cnt' = Cost.cntSel sc use.toNat)
    (hpc : s.pc = mbase 8 + allocSlotOff_bounces_cap) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc))
    (hx4 : s.readReg64 .x4 = 4096#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt'))
    (hx7 : 38 < sc → s.readReg64 .x7 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc))
    (hx25_38 : 38 < sc → (s.readReg64 .x2).toNat = use.toNat ∧ s.readReg64 .x5 = 0#64) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsFine sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
          sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame)
      (fun _ => ⌜False⌝) := by
  have hc1_24 : cnt' = 1 → 24 ≤ sc := fun hc1 => by
    subst hc1; apply Classical.byContradiction; intro hlt24
    have := slotStride_le_2032_of_le_23 (by omega : sc ≤ 23)
    omega
  let Post : State → SepProp → Prop := fun sf P_f =>
    ∃ cnt_f len, RootMmapParamsFineBase sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
      (∃ c, Cost.RootCntRel sc cnt' c (s.readReg64 .x2) ∧
        Cost.RootLenOk sc c len (s.readReg64 .x2) (s.readReg64 .x5)) ∧
      sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
      sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
        sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame
  have hCore : SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_mmap_go) s Frame Post (fun _ => ⌜False⌝) := by
    refine wp_root_size_select_core s sc cnt' Frame Post hw768 hsc hhi hprod hpc hrun
      hx0 hx4 hx6 hx7 hx21 ?_ ?_
    · intro hrel sm hmp hmrun hsp hal hpsp hmr
      refine SepWP.mono (wp_root_mmap_prep_core sm sc req cnt' Frame hw768 hsc hReq
        hlo hhi hc1_24 hprod h25 hmp hmrun (by rw [hmr .x4 (by decide), hx4])
        (by rw [hmr .x20 (by decide), hx20]) (by rw [hmr .x24 (by decide), hx24])
        (by rw [hmr .x25 (by decide), hx25]) (by rw [hmr .x27 (by decide), hx27])) ?_
      rintro sf P_f _ _ ⟨cnt_f, len, hBase, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
      refine ⟨cnt_f, len, hBase, hRq, ⟨cnt', hrel, ?_⟩, h1, h2.trans hsp, h3.trans hal,
        hpsp.trans hpsp2, h6, h7,
        fun r r0 r1 r3 r20 r25 r26 r27 => (hregs r r0 r1 r3 r20 r25 r26 r27).trans (hmr r r1), hPf⟩
      rw [← hmr .x2 (by decide), ← hmr .x5 (by decide)]; exact hLen
    · intro c sm hclo hchi hrel hmp hmrun hsp hal hpsp hm0 hm20 hmr
      refine SepWP.mono (wp_root_cnt_mul_core sm sc req c Frame hw768 hsc hReq hclo hchi
        hmp hmrun hm0 (by rw [hmr .x4 (by decide) (by decide) (by decide), hx4]) hm20
        (by rw [hmr .x24 (by decide) (by decide) (by decide), hx24])
        (by rw [hmr .x25 (by decide) (by decide) (by decide), hx25])) ?_
      rintro sf P_f _ _ ⟨cnt_f, len, hBase, hRq, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
      refine ⟨cnt_f, len, hBase, hRq, ⟨c, hrel, ?_⟩, h1, h2.trans hsp, h3.trans hal,
        hpsp.trans hpsp2, h6, h7,
        fun r r0 r1 r3 r20 r25 r26 _ => (hregs r r0 r3 r20 r25 r26).trans (hmr r r0 r1 r20), hPf⟩
      rw [← hmr .x2 (by decide) (by decide) (by decide)]; exact hLen _
  refine SepWP.mono hCore ?_
  rintro sf P_f _ _ ⟨cnt_f, len, ⟨hOk, hc1, hPage⟩, hRq, ⟨c, hrel, hLen⟩, rest⟩
  have hRB : len ≤ Cost.rootBytesAt sc use.toNat :=
    Cost.rootLen_le_rootBytesAt' hsc hcnt' hgt2048 hrel hx25_38 hLen
  have hGrp : len ≤ Cost.grpMax sc 128 :=
    Nat.le_trans hRB (rootBytesAt_le_grpMax_128 hsc use.toNat)
  exact ⟨cnt_f, len, ⟨hOk, hc1, hPage, hGrp⟩, hRq, rest⟩

end LibsignalBinary.Heap.Fine
