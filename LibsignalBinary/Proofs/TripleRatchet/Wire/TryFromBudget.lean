/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<SignalMessage>::try_from` Composition

Composes the budget-threaded prologue, protobuf decode loop (`+0x088 → +0x3b0`), post-loop
contract interface (`TryFromPostOkGen_placed`), and shared epilogue into the relocatable
`[LibsignalPlacement]` `subroutine_ok` theorem on Block `85`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp pointsToBytes_split_last
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (protoSignalCodec decode decodeLoop emptyProtoSignalMessage)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (blkPl_85 LibsignalCodeRoLoaded withLsCodeRoLoaded logOff smallRootStack TryFromGhost)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (sliceCursorAt skipFieldStackX wireSignalMessageOf)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (SepWPp tryFromPlacedImg tryFromPlacedProg tryFromSubStack
   EpilogueStatePlaced LoopExitStatePlaced calleeSavedAt pointsToBytes_take_drop
   stackAt_smallRoot_split stackAt_sub_split tryFrom_loop_slice_eq bv_ofNat_sub9
   memRegion352_split_len9 memRegion352_split_loop
   loopExitMem loopPostMem entails_of_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (TripleRatchetHooksWPlaced DecodeVarintSliceOkWPlaced Int32MergeOkWPlaced
   SkipFieldOkWPlaced BytesMergeOkWPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (TryFromLoopEnv noPanicQp sepWPp_frame_noPanic sepWPp_bind_frame_entails_noPanic
   sepWPp_mono_post)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBodyBudget
  (decodeLoop_f0_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
  (EpilogueStateBudgetPlaced TryFromEnvGen fitsEnv_tryFrom_loop fitsEnv_tryFrom_post
   tryFromPlacedSpecGen epilogue_440_wp_placed prologue_tooShort_wp_placed
   prologue_entry_ge9_wp_placed prologue_44_legacyVer_wp_placed
   prologue_44_unrecognizedVer_wp_placed prologue_44_validVer_wp_placed
   prologue_88_init_wp'_placed prologue_b8_gt9_to_f0_wp_placed
   prologue_88_len9_wp_placed)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Loop segment (`+0x088 → +0x3b0`) and post-loop contract (`TryFromPostOkGen_placed`) -/

theorem prologue_88_gt9_loop_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hfit : FitsEnv M lim st (TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length))
    (hbs : x.bytes = b0 :: rest)
    (hgt9 : 9 < x.bytes.length) (hlt : x.bytes.length < 2 ^ 63)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x3b0#64) s
      (memRegion (s0.sp - 448#64) 176 ∗
        memRegion (s0.sp - 448#64 + 176#64) 112 ∗
        memRegion (s0.sp - 448#64 + 288#64) 64 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.bytesA (b0.zeroExtend 64) sf ∧
        ∃ evs₁ : List AllocEvent,
          TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length evs₁ ∧
          (Pf ⊢ loopPostMem (A.atState lim (M.stepEvents evs₁ st) sf)
            (s0.sp - 448#64) x (sf.readReg64 .x24)))
      (noPanicQp s0) := by
  set sp' := s0.sp - 448#64
  set bs := (x.bytes.take (x.bytes.length - 8)).drop 1
  have hrest_len : rest.length + 1 = x.bytes.length := by
    have := congrArg List.length hbs; simpa using this.symm
  have hrest_gt8 : 8 < rest.length := by omega
  have hbs_eq : bs = rest.take (rest.length - 8) := by
    dsimp only [bs]; rw [hbs]; exact tryFrom_loop_slice_eq hrest_gt8
  have hbs_len : bs.length = x.bytes.length - 9 := by
    rw [hbs_eq, List.length_take, Nat.min_eq_left (by omega)]; omega
  have hbs_pos : 0 < bs.length := by omega
  rcases hcons : bs with _ | ⟨b1, bs1⟩
  · simp [hcons] at hbs_pos
  have hlen_cons : (b1 :: bs1).length = x.bytes.length - 9 := hcons ▸ hbs_len
  have hfuel_eq : 2 * (bs1.length + 1) + 2 = 2 * (x.bytes.length - 9) + 2 := by
    simp only [List.length_cons] at hlen_cons; omega
  have hbv_len : BitVec.ofNat 64 (b1 :: bs1).length = BitVec.ofNat 64 x.bytes.length - 9#64 := by
    rw [hlen_cons]; exact bv_ofNat_sub9 (by omega)
  have h176_split : memRegion sp' 176 = memRegion sp' 160 ∗ memRegion (sp' + 160#64) 16 :=
    memRegion_split' (n := 160) (k := 16) rfl rfl (by decide)
  have h64_split : memRegion (sp' + 288#64) 64 =
      memRegion (sp' + 288#64) 8 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 := by
    rw [memRegion_split' (n := 8) (k := 56) rfl rfl (by decide),
      memRegion_split' (b := sp' + 288#64 + 8#64) (n := 48) (k := 8) rfl rfl (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [h176_split, h64_split]
  set F1 := memRegion sp' 160 ∗ memRegion (sp' + 296#64) 48 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
    A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)
  refine SepWPp.mono_pre (P' :=
      (memRegion (sp' + 160#64) 16 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8) ∗ F1)
    (by dsimp only [F1, sp']; apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_entails_noPanic
    (prologue_88_init_wp'_placed (A := A.repAlloc) hst hpc hrun
      hx19 hx20 hx21 hx23 hx26 hx29) ?_
  intro s3 hpc3 hrun3 ⟨hst3, hpstate3, hx2_3, hx8_3, hx19_3, hx20_3, hx21_3, hx23_3, hx26_3, hx29_3⟩
  set P3 := ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
    ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
    wireSignalMessageOf A.repAlloc (sp' + 176#64) emptyProtoSignalMessage ∗
    ((sp' + 288#64) ↦₆₄ (sp' + 160#64))
  refine SepWPp.mono_pre (P' := emp ∗ (P3 ∗ F1))
    (by rw [emp_sepConj]; exact Entails.refl _) ?_
  refine sepWPp_bind_frame_entails_noPanic
    (prologue_b8_gt9_to_f0_wp_placed hgt9 hlt hst3 hpc3 hrun3
      hpstate3 hx2_3 hx8_3 hx19_3 hx20_3 hx21_3 hx23_3 hx26_3 hx29_3) ?_
  intro s4 hpc4 hrun4 ⟨hregs4, ⟨⟨_, hsp4, hcl4, htr4⟩, hvm4⟩, hx28_4, hx27_4, hx2_4⟩
  rw [emp_sepConj]
  dsimp only [P3, F1]
  have hpool4 : A.pool lim st s = A.pool lim st s4 :=
    (A.pool_transport lim st s0 s hst.2).trans (A.pool_transport lim st s0 s4 hvm4).symm
  have hrest_split : ((x.bytesA + 1#64) ↦ₛ rest) =
      ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    have hs := (pointsToBytes_take_drop (x.bytesA + 1#64) rest (rest.length - 8) (by omega)).symm
    rw [← hbs_eq, hcons] at hs
    exact hs
  have hcursor : sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) =
      ((sp' + 160#64) ↦₆₄ (x.bytesA + 1#64)) ∗
        ((sp' + 168#64) ↦₆₄ (BitVec.ofNat 64 x.bytes.length - 9#64)) ∗
        ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) := by
    unfold sliceCursorAt
    rw [hbv_len]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  set F2 := memRegion sp' 160 ∗ memRegion (sp' + 344#64) 8 ∗
    (x.bytesA ↦₈ b0) ∗
    ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8))
  refine SepWPp.mono_pre (P' :=
      (sliceCursorAt (sp' + 160#64) (x.bytesA + 1#64) (b1 :: bs1) ∗
        ((sp' + 288#64) ↦₆₄ (sp' + 160#64)) ∗
        memRegion (sp' + 296#64) 48 ∗
        A.pool lim st s4 ∗ stackAt sp' (skipFieldStackX 100) ∗
        wireSignalMessageOf A.repAlloc (sp' + 176#64) emptyProtoSignalMessage) ∗ F2)
    (by
      rw [hpool4, hrest_split, hcursor]
      dsimp only [F2]
      apply entails_of_eq; sep_ac_rfl) ?_
  have hx2_4' : s4.readReg64 .x2 = BitVec.ofNat 64 (b1 :: bs1).length := by
    rw [hx2_4, hbv_len]
  have hfit_loop : FitsEnv M lim st (TryFromLoopEnv (2 * (bs1.length + 1) + 2) x.bytes.length) := by
    rwa [hfuel_eq]
  have hloop := decodeLoop_f0_wp_placed hS hvarint hint32 hskip hbytes (fuel := bs1.length)
    (m := emptyProtoSignalMessage) (ptr := x.bytesA + 1#64)
    hfit_loop (by omega) hpc4 hrun4 hregs4 hx28_4 hx27_4 hx2_4' hsp4 hcl4 htr4
    (Nat.le_refl _) (by omega)
  refine sepWPp_frame_noPanic hloop fun sf Pf ⟨hstf, evs₁, hevs₁, hentf⟩ =>
    ⟨hstf, evs₁, hevs₁, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hdec : decodeLoop (bs1.length + 1) emptyProtoSignalMessage (b1 :: bs1) = decode bs := by
    rw [hcons]; rfl
  rw [hdec]
  dsimp only [loopExitMem, loopPostMem, bs, F2]
  have hbytes_eq : (x.bytesA ↦ₛ x.bytes) =
      (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ (b1 :: bs1)) ∗
        ((x.bytesA + 1#64 + BitVec.ofNat 64 (rest.length - 8)) ↦ₛ rest.drop (rest.length - 8)) := by
    rw [hbs, pointsToBytes_cons, hrest_split]
  rw [h176_split, h64_split, hbytes_eq]
  have h288 := pointsTo64_entails_memRegion (sp' + 288#64) (sp' + 160#64)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left h288)))
  dsimp only [sp']
  apply entails_of_eq; sep_ac_rfl

/-- Post-loop (`+0x3b0 → +0x440`) budget contract interface, parameterized by `PostEnv`. -/
def TryFromPostOkGen_placed [LibsignalPlacement] {M : AllocCostModel}
    (PostEnv : TryFromGhost → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ {st : M.σ} {x : TryFromGhost} {s0 s : State},
    FitsEnv M lim st (PostEnv x) →
    9 < x.bytes.length →
    x.bytes.length < 2 ^ 32 →
    ¬ ((x.bytes.headD 0#8) >>> 4) < 3#8 →
    ¬ 4#8 < ((x.bytes.headD 0#8) >>> 4) →
    s.pc = (blkPl_85).base + 0x3b0#64 →
    s.status = .Running →
    LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s →
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (loopPostMem (A.atState lim st s) (s0.sp - 448#64) x (s.readReg64 .x24) ∗
        memRegion x.ret 120 ∗ logOff tryFromPlacedImg)
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, PostEnv x evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret
              (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (noPanicQp s0)

/-! ## Prologue-to-epilogue composition and top-level `subroutine_ok` -/

theorem prologue_88_to_440_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {PostEnv : TryFromGhost → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hpost : TryFromPostOkGen_placed PostEnv A lim H)
    {x : TryFromGhost} {s0 s : State} {b0 : BitVec 8} {rest : List (BitVec 8)}
    (hfit : FitsEnv M lim st (TryFromEnvGen PostEnv x))
    (hbs : x.bytes = b0 :: rest)
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hge3 : ¬ (b0 >>> 4) < 3#8) (hle4 : ¬ 4#8 < (b0 >>> 4))
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x088#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx21 : s.readReg64 .x21 = x.bytesA)
    (hx23 : s.readReg64 .x23 = b0.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = 0x8000000000000002#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromEnvGen PostEnv x evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret
              (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (noPanicQp s0) := by
  set sp' := s0.sp - 448#64
  by_cases hlen9 : x.bytes.length = 9
  · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
      rw [hbs, pointsToBytes_cons]
    set F9 := memRegion sp' 88 ∗ memRegion (sp' + 104#64) 56 ∗ memRegion (sp' + 296#64) 56 ∗
      (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗ A.pool lim st s ∗
      stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' :=
        (memRegion (sp' + 88#64) 16 ∗
          memRegion (sp' + 160#64) 16 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 8 ∗
          memRegion x.ret 120) ∗ F9)
      (by
        dsimp only [F9, sp']
        rw [memRegion352_split_len9, hbytes_eq]
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (prologue_88_len9_wp_placed (A := A.repAlloc) hbs hlen9 hge3 hle4 hst hpc hrun
        hx19 hx20 hx21 hx23 hx26 hx29)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf.1, [], .nil, ?_⟩
    have hpool : A.pool lim st s = A.pool lim (M.stepEvents [] st) sf := by
      simpa using (A.pool_transport lim st s0 s hst.2).trans
        (A.pool_transport lim st s0 sf hstf.2).symm
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [memRegion352_split_len9 sp']
    dsimp only [F9, sp']
    rw [hpool]
    apply entails_of_eq; sep_ac_rfl
  · have hgt9 : 9 < x.bytes.length := by omega
    have hhead : x.bytes.headD 0#8 = b0 := by simp [hbs]
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 176 ∗
          memRegion (sp' + 176#64) 112 ∗
          memRegion (sp' + 288#64) 64 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (memRegion x.ret 120 ∗ logOff tryFromPlacedImg))
      (by
        rw [memRegion352_split_loop sp']
        dsimp only [sp']
        apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.bind
      (Qm := fun s5 P5 =>
        LoopExitStatePlaced s0 sp' x.ret
          (BitVec.ofNat 64 x.bytes.length) x.bytesA (b0.zeroExtend 64) s5 ∧
        ∃ evs₁ : List AllocEvent,
          TryFromLoopEnv (2 * (x.bytes.length - 9) + 2) x.bytes.length evs₁ ∧
          (P5 ⊢ loopPostMem (A.atState lim (M.stepEvents evs₁ st) s5)
            sp' x (s5.readReg64 .x24) ∗
            (memRegion x.ret 120 ∗ logOff tryFromPlacedImg)))
      (sepWPp_frame_noPanic
        (prologue_88_gt9_loop_wp_placed hS hvarint hint32 hskip hbytes
          (fitsEnv_tryFrom_loop hfit) hbs hgt9 (by omega) hst hpc hrun
          hx19 hx20 hx21 hx23 hx26 hx29)
        fun s5 P5 ⟨hst5, evs₁, hevs₁, hent5⟩ => ⟨hst5, evs₁, hevs₁, sepConj_mono_left hent5⟩) ?_
    intro s5 P5 hpc5 hrun5 ⟨hst5, evs₁, hevs₁, hent5⟩
    have hst5' : LoopExitStatePlaced s0 (s0.sp - 448#64) x.ret
        (BitVec.ofNat 64 x.bytes.length) x.bytesA ((x.bytes.headD 0#8).zeroExtend 64) s5 :=
      hhead.symm ▸ hst5
    refine SepWPp.mono_pre ?_
      (sepWPp_mono_post
        (fun sf Pf ⟨hstf, evs₂, hevs₂, hentf⟩ =>
          ⟨hstf, evs₁ ++ evs₂, .loopPost hevs₁ hevs₂, by rwa [M.stepEvents_append]⟩)
        (hpost (fitsEnv_tryFrom_post hevs₁ hfit) hgt9 hlt (hhead ▸ hge3) (hhead ▸ hle4)
          hpc5 hrun5 hst5'))
    refine Entails.trans hent5 ?_
    dsimp only [sp']
    apply entails_of_eq; sep_ac_rfl

theorem prologue_44_to_440_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {PostEnv : TryFromGhost → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hpost : TryFromPostOkGen_placed PostEnv A lim H)
    {x : TryFromGhost} {s0 s : State}
    (hfit : FitsEnv M lim st (TryFromEnvGen PostEnv x))
    (hge9 : 9 ≤ x.bytes.length) (hlt : x.bytes.length < 2 ^ 32)
    (hst : EpilogueStateBudgetPlaced s0 (s0.sp - 448#64) s)
    (hpc : s.pc = (blkPl_85).base + 0x044#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = x.bytesA)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 448#64 + 352#64) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s
      (memRegion (s0.sp - 448#64) 352 ∗
        memRegion x.ret 120 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
        A.pool lim st s ∗ stackAt (s0.sp - 448#64) (skipFieldStackX 100))
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromEnvGen PostEnv x evs ∧
          (Pf ⊢ memRegion (s0.sp - 448#64) 352 ∗
            signalMessageResultAt A.repAlloc [] x.ret
              (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt (s0.sp - 448#64) (skipFieldStackX 100)))
      (noPanicQp s0) := by
  set sp' := s0.sp - 448#64
  rcases hbs : x.bytes with _ | ⟨b0, rest⟩
  · simp [hbs] at hge9
  have hge9' : 9 ≤ x.bytes.length := hge9
  rw [← hbs]
  by_cases hlt3 : (b0 >>> 4) < 3#8
  · set Fv := memRegion sp' 352 ∗ logOff tryFromPlacedImg ∗ A.pool lim st s ∗
      stackAt sp' (skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
      (by dsimp only [Fv, sp']; apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (prologue_44_legacyVer_wp_placed (A := A.repAlloc) hbs hge9' hlt3 hst hpc hrun hx0 hx19)
      fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf.1, [], .nil, ?_⟩
    have hpool : A.pool lim st s = A.pool lim (M.stepEvents [] st) sf := by
      simpa using (A.pool_transport lim st s0 s hst.2).trans
        (A.pool_transport lim st s0 sf hstf.2).symm
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [Fv, sp']
    rw [hpool]
    apply entails_of_eq; sep_ac_rfl
  · by_cases hgt4 : 4#8 < (b0 >>> 4)
    · set Fv := memRegion sp' 352 ∗ logOff tryFromPlacedImg ∗ A.pool lim st s ∗
        stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120) ∗ Fv)
        (by dsimp only [Fv, sp']; apply entails_of_eq; sep_ac_rfl) ?_
      refine sepWPp_frame_noPanic
        (prologue_44_unrecognizedVer_wp_placed (A := A.repAlloc) hbs hge9' hlt3 hgt4
          hst hpc hrun hx0 hx19)
        fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf.1, [], .nil, ?_⟩
      have hpool : A.pool lim st s = A.pool lim (M.stepEvents [] st) sf := by
        simpa using (A.pool_transport lim st s0 s hst.2).trans
          (A.pool_transport lim st s0 sf hstf.2).symm
      refine Entails.trans (sepConj_mono_left hentf) ?_
      dsimp only [Fv, sp']
      rw [hpool]
      apply entails_of_eq; sep_ac_rfl
    · have hbytes_eq : (x.bytesA ↦ₛ x.bytes) = (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) := by
        rw [hbs, pointsToBytes_cons]
      set Fv := memRegion sp' 352 ∗ memRegion x.ret 120 ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
        logOff tryFromPlacedImg ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100)
      refine SepWPp.mono_pre (P' := (x.bytesA ↦₈ b0) ∗ Fv)
        (by dsimp only [Fv, sp']; rw [hbytes_eq]; apply entails_of_eq; sep_ac_rfl) ?_
      refine sepWPp_bind_frame_entails_noPanic
        (prologue_44_validVer_wp_placed hlt3 hgt4 hst hpc hrun hx0 hx19 hx20 hx29) ?_
      intro s2 hpc2 hrun2 ⟨hst2, hx19_2, hx20_2, hx21_2, hx23_2, hx26_2, hx29_2⟩
      have hpool2 : A.pool lim st s = A.pool lim st s2 :=
        (A.pool_transport lim st s0 s hst.2).trans (A.pool_transport lim st s0 s2 hst2.2).symm
      refine SepWPp.mono_pre (P' :=
          memRegion sp' 352 ∗ memRegion x.ret 120 ∗
          (x.bytesA ↦₈ b0) ∗ ((x.bytesA + 1#64) ↦ₛ rest) ∗
          logOff tryFromPlacedImg ∗ A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100))
        (by dsimp only [Fv, sp']; rw [hpool2]; apply entails_of_eq; sep_ac_rfl) ?_
      exact prologue_88_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
        hfit hbs hge9' hlt hlt3 hgt4 hst2 hpc2 hrun2
        hx19_2 hx20_2 hx21_2 hx23_2 hx26_2 hx29_2

theorem tryFrom_entry_to_440_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {PostEnv : TryFromGhost → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hpost : TryFromPostOkGen_placed PostEnv A lim H)
    {x : TryFromGhost} {s0 : State}
    (hfit : FitsEnv M lim st (TryFromEnvGen PostEnv x))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_85).base)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (tryFromPlacedProg H)
      ((blkPl_85).base + 0x440#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        EpilogueStatePlaced s0 (s0.sp - 448#64) sf ∧
        ∃ evs : List AllocEvent, TryFromEnvGen PostEnv x evs ∧
          (Pf ⊢ stackAt (s0.sp - 448#64) tryFromSubStack ∗
            memRegion (s0.sp - 448#64) 352 ∗
            calleeSavedAt (s0.sp - 448#64) s0 ∗
            signalMessageResultAt A.repAlloc [] x.ret
              (SignalMessage.tryFrom protoSignalCodec x.bytes) ∗
            (x.bytesA ↦ₛ x.bytes) ∗ logOff tryFromPlacedImg ∗
            A.pool lim (M.stepEvents evs st) sf))
      (noPanicQp s0) := by
  by_cases hlt9 : x.bytes.length < 9
  · exact sepWPp_mono_post
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, [], .nil, by simpa using hentf⟩)
      (prologue_tooShort_wp_placed hlt9 hpc hrun hsp hcl hx0 hx1 hx8)
  · have hge9 : 9 ≤ x.bytes.length := by omega
    set sp' := s0.sp - 448#64
    have hstk1 := stackAt_smallRoot_split s0.sp
    have hstk2 := stackAt_sub_split sp' (skipFieldStackX 100) tryFromSubStack
    set Fe := (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
      logOff tryFromPlacedImg ∗ A.pool lim st s0 ∗ stackAt sp' (skipFieldStackX 100)) ∗
      memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)
    refine SepWPp.mono_pre (P' := memRegion (sp' + 352#64) 96 ∗ Fe)
      (by
        rw [hstk1, hstk2]
        dsimp only [Fe, sp']
        apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_entails_noPanic
      (prologue_entry_ge9_wp_placed hge9 (by omega) hpc hrun hsp hcl hx0 hx1 hx8) ?_
    intro s1 hpc1 hrun1 ⟨hst1, hx0_1, hx19_1, hx20_1, hx29_1⟩
    dsimp only [Fe]
    have hpool1 : A.pool lim st s0 = A.pool lim st s1 :=
      (A.pool_transport lim st s0 s1 hst1.2).symm
    refine SepWPp.mono_pre (P' :=
        (memRegion sp' 352 ∗ memRegion x.ret 120 ∗ (x.bytesA ↦ₛ x.bytes) ∗
          logOff tryFromPlacedImg ∗ A.pool lim st s1 ∗ stackAt sp' (skipFieldStackX 100)) ∗
        (calleeSavedAt sp' s0 ∗
          memRegion (sp' - BitVec.ofNat 64 tryFromSubStack) (tryFromSubStack - skipFieldStackX 100)))
      (by rw [hpool1]; apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (prologue_44_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
        hfit hge9 hlt hst1 hpc1 hrun1 hx0_1 hx19_1 hx20_1 hx29_1)
      fun sf Pf ⟨hstf, evs, hevs, hentf⟩ => ⟨hstf, evs, hevs, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    rw [hstk2]
    dsimp only [sp']
    apply entails_of_eq; sep_ac_rfl

theorem tryFrom_subroutine_ok_of_post_placed [LibsignalPlacement] {M : AllocCostModel}
    {PostEnv : TryFromGhost → List AllocEvent → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H)
    (hvarint : DecodeVarintSliceOkWPlaced A lim H)
    (hint32 : Int32MergeOkWPlaced A lim H)
    (hskip : SkipFieldOkWPlaced A lim H)
    (hbytes : BytesMergeOkWPlaced A lim H)
    (hpost : TryFromPostOkGen_placed PostEnv A lim H) :
    subroutine_ok (tryFromPlacedProg H)
      ((blkPl_85).base)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecGen PostEnv A lim)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp hL
  dsimp only [withLsCodeRoLoaded] at hpre
  rw [sepConj_comm ((tryFromPlacedSpecGen PostEnv A lim).pre (x, st) s0),
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  dsimp only [tryFromPlacedSpecGen] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8, hfit⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0) ∗ R :=
    Satisfies.mono (by apply entails_of_eq; sep_ac_rfl) hmem
  have h1 := tryFrom_entry_to_440_wp_placed hS hvarint hint32 hskip hbytes hpost
    hfit hlt hpc hrun hsp hcl hx0 hx1 hx8
  have hfull : SepWPp (tryFromPlacedProg H)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 120 ∗ logOff tryFromPlacedImg ∗
        stackAt s0.sp smallRootStack ∗ A.pool lim st s0)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (tryFromPlacedSpecGen PostEnv A lim).post (x, st) s0 sf))
      (noPanicQp s0) := by
    refine SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, evs, hevs, hentm⟩
    exact SepWPp.mono_pre hentm
      (epilogue_440_wp_placed hevs hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with
    ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact False.elim hpan
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudget
