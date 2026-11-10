/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Kyber Scatter, `Ok` Branches, and Mismatched-Field Error

Allocation-budget (`RustCliAllocBudget M`) proofs of the `PublicKey` scatter, `both` and
v3 `neither` `Ok` branches (`+0x684 → +0x830`), Kyber buffer deallocation (`+0xa1c → +0xa24`),
and the panic-free 68-byte mismatched-Kyber error branch (`+0x6c8 → +0xa24`) on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlacedBudget

open Arm64 Arm64.Obj ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding
  boxU8Buf intoBoxedSliceStack intoBoxedSliceStackX intoBoxedSliceSpec intoBoxedSliceSpecX
  intoBoxedSliceSpecWithStack noAllocShimSpec rustDeallocExternSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters hiding lsRustDeallocSym
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary hiding CodecHooksPlaced
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open RunProofs.Pksm
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  SepWPp pk_scatter_head_placed_wp kyber_both_ok_placed_wp kyber_neither_v3_ok_placed_wp
  kyber_a80_panic_placed_wp kyber_a1c_to_a24_placed_wp
  kyber_err_alloc68_head_placed_wpE kyber_half_err_placed_wpE
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
  RustLayoutOk VmPreserved rustAllocEvents rustDeallocEvents
  rustCliAllocBudgetSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  freeOnly_rustDeallocEvents preKeyNoPanicQp
)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget (
  hookSat_noAllocShimBudget_of_withVmPreserved
)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (
  PksmCalleesPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  IntoBoxedSliceEnv boxU8Buf intoBoxedSliceEvents intoBoxedSliceSpecWithStack
  intoBoxedSliceSpecX intoBoxedSliceStackX noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget (
  IntoBoxedCapEnv intoBoxedCapEvents
)

private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev sepWPp_bind_noPanic := @Wire.SepWPp.bind
private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev of_sepWP_end_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.of_sepWP_end_noPanic_pk
private abbrev call_noPanic_budget_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.call_noPanic_budget_pk
private abbrev frame_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.frame_noPanic_pk
private abbrev let_state_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.let_state

private theorem sepWPp_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s : State} {P F : SepProp} {Qm : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Qm preKeyNoPanicQp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      SepWPp prog ret sm (Pm ∗ F) Q preKeyNoPanicQp) :
    SepWPp prog ret s (P ∗ F) Q preKeyNoPanicQp := by
  refine Wire.SepWPp.bind (Qm := fun sm Pf => ∃ Pm, Pf = Pm ∗ F ∧ Qm sm Pm)
    (frame_noPanic_pk h1 fun sm Pm hq => ⟨Pm, rfl, hq⟩) ?_
  rintro sm _ hpcm hrunm ⟨Pm, rfl, hq⟩
  exact h2 sm Pm hpcm hrunm hq

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-- Shared `.rodata` symbol for the 68-byte half-Kyber error message in Block 111 (`+0x734`). -/
abbrev lsPksmKyberHalfErrRoSym : String :=
  CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.lsPksmKyberHalfErrRoSym

/-- Shared `.rodata` symbol for the 54-byte missing-Kyber v4 error message in Block 111 (`+0x9ac`). -/
abbrev lsPksmKyberV4ErrRoSym : String :=
  CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.lsPksmKyberV4ErrRoSym

abbrev kyber_a80_panic_placed_wp :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.kyber_a80_panic_placed_wp

theorem sepWPp_anyQp_of_noPanic {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q preKeyNoPanicQp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem w5bw_ule_64_vb_eq_false {vb : BitVec 8} (hvb_lt : vb.toNat < 0x40) :
    (64#64).ule (vb.zeroExtend 64) = false := by
  rw [BitVec.ule_eq_decide]
  exact decide_eq_false (by rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega)

/-! ## 1. `pk_scatter_head_placed_wp`, `kyber_both_ok_placed_wp`, `kyber_neither_v3_ok_placed_wp` -/

/-- (``+0x684 .. +0x6c8`, `+1668 .. +1736``, `[LibsignalPlacement]`):
Loads the 32-byte `PublicKey` from `sp' + 313..345`, scatters `w23, b31, w9, w13, b0..b6`
into `sp' + 112..144`, keeps `b8`, `w15`, `b7` in `x8`, `x11`, `x12`, sets `x24 = sp' + 312#64`,
sets `pstate = subsPState32 kpkTag 1#32` at `+0x6c8` (`1736`), and threads `A.pool lim st`. -/
theorem pk_scatter_head_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {kpkTag : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {pkBytes : List (BitVec 8)} {Qp : State → SepProp → Prop}
    (hpk : pkBytes = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 1736#64) s
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ pkBytes) ∗ memRegion (sp' + 345#64) 15 ∗
        A.pool lim st s)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pstate = subsPState32 kpkTag 1#32 ∧
        sf.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x11 = w15 ∧
        sf.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧ sf.readReg64 .x24 = sp' + 312#64 ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48 ∗ A.pool lim st sf))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (memRegion32_112_unpack sp'))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w112 => SepWPp.exists_pre fun b120 =>
    SepWPp.exists_pre fun w128 => SepWPp.exists_pre fun w132 =>
    SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => ?_
  dsimp only [pkLayoutAt]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 1680#64) ?_
  dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1680#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ A.pool lim st _)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 1704#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1704#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl2 => ?_⟩
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗
      ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' + 132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗
      ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
      pkRestAt (sp' + 313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ A.pool lim st _)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1736#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl3,
      by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm], ?_⟩
  have h136_ent :
      ((sp' + 136#64) ↦₈ b0) ∗ ((sp' + 137#64) ↦₈ b1) ∗ ((sp' + 138#64) ↦₈ b2) ∗
        ((sp' + 139#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
      ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) := by
    have h := (sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6).symm
    dsimp only [sevenBytesTailAt, sevenBytesHeadAt] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact entails_of_eq h
  have hcollapse :
      ((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 320#64) ↦₈ b7) ∗ ((sp' + 321#64) ↦₈ b8) ∗ ((sp' + 322#64) ↦₃₂ w9) ∗
        ((sp' + 326#64) ↦₁₆ w13) ∗ ((sp' + 328#64) ↦₆₄ w15) ∗ ((sp' + 336#64) ↦₆₄ w23) ∗
        ((sp' + 344#64) ↦₈ b31) ∗ memRegion (sp' + 345#64) 15 ⊢
      memRegion (sp' + 312#64) 48 := by
    have hc := deser_ok_entails_memRegion48 sp' b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
    dsimp only [pkRestAt] at hc
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hc
    exact hc
  refine Entails.trans
    (Q := (((sp' + 312#64) ↦₈ 0#8) ∗ sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 320#64) ↦₈ b7) ∗ ((sp' + 321#64) ↦₈ b8) ∗ ((sp' + 322#64) ↦₃₂ w9) ∗
        ((sp' + 326#64) ↦₁₆ w13) ∗ ((sp' + 328#64) ↦₆₄ w15) ∗ ((sp' + 336#64) ↦₆₄ w23) ∗
        ((sp' + 344#64) ↦₈ b31) ∗ memRegion (sp' + 345#64) 15) ∗
      ((((sp' + 136#64) ↦₈ b0) ∗ ((sp' + 137#64) ↦₈ b1) ∗ ((sp' + 138#64) ↦₈ b2) ∗
          ((sp' + 139#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) ∗
        (((sp' + 68#64) ↦₃₂ kpkTag) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗ A.pool lim st _)))
    (by apply entails_of_eq; sep_ac_rfl)
    (Entails.trans (sepConj_mono hcollapse (sepConj_mono_left h136_ent))
      (by apply entails_of_eq; sep_ac_rfl))

/-- (``+0x6c8 .. +0x6fc → +0x830`, `1736 .. 1788 → 2096``, `[LibsignalPlacement]`):
When `kpkTag = 1#32` and `m.kyberCiphertext = some kyberCt` (`kyberCap.toNat < 2 ^ 63`), stores
`b8`, `b7`, `w15` to stack slots `sp' + 68`, `sp' + 12`, `sp' + 72`, converts `kyberCt` via
`into_boxed_slice` under `FitsEnv M lim st (IntoBoxedCapEnv kyberCap kyberCt)`, and branches to
`+0x830` (`2096`) without OOM or panic. -/
theorem kyber_both_ok_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {kyberCt : List (BitVec 8)}
    {bk : List (BitVec 8)} {pk : PublicKey} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (IntoBoxedCapEnv kyberCap kyberCt))
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hky_lt : kyberCap.toNat < 2 ^ 63)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 1#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
        memRegion (sp' + 312#64) 48 ∗
        Wire.vecU8Buf A.repAlloc kyberCap kyberPtr kyberCt ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ kyberBoxPtr : BitVec 64,
          KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr (BitVec.ofNat 64 kyberCt.length)
            ikCap msgCap vb bk pk sf ∧
          kyberBoxPtr ≠ 0#64 ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            memRegion (sp' + 312#64) 48 ∗
            boxU8Buf A.repAlloc kyberBoxPtr kyberCt ∗
            A.pool lim (M.stepEvents (intoBoxedCapEvents kyberCap kyberCt) st) sf ∗
            stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hky_eq := cap_add1_eq_of_lt hky_lt
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStackX
    (Prost.skipFieldStackX 100) (by decide) (by decide)
  have hfits_box :
      FitsEnv M lim st (IntoBoxedSliceEnv ⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩) := hfit
  conv => arg 4; rw [memRegion48_312_split24 sp']
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w328 => SepWPp.exists_pre fun w320 =>
    SepWPp.exists_pre fun w312 => SepWPp.exists_pre fun w12 => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 56) ?_
  wp_steps_sync_111 (lsmpl.base 56)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  refine let_state_pk ?_; intro sc
  have hvec_ky : vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr kyberCt =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
      Wire.vecU8Buf A.repAlloc kyberCap kyberPtr kyberCt := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hsc_sp : sc.sp = sp' := by simp [sc, hsp_eq, arm64_norm]
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
    ((⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩ : VecArg), st) hC.intoBoxedX
    (by simp_all [sc, arm64_norm]) (by simp_all [sc, arm64_norm])
    (by simp only [sc, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1780#64) (by simp_all [sc, arm64_norm])
    (T := vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr kyberCt ∗
      A.pool lim st sc ∗ stackAt sp' intoBoxedSliceStackX)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      FitsEnv M lim st (IntoBoxedSliceEnv ⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩))
    (by simp_all [sc, intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack, VecArg.at,
      intoBoxedSliceStackX, arm64_norm])
    ⟨rfl, hfits_box⟩
    (by rw [hvec_ky, hstackBox]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [intoBoxedSliceSpecX, intoBoxedSliceSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx1_2, htr2⟩ => ?_
  rw [hsc_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hv25_2, hx26_2, hx27_2,
    hv28_2, hx29_2, hv_2⟩
  clear hv25_2 hv28_2 hv_2
  dsimp only [sc] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx29_2
  simp only [htr, hx29, hx27, hx26, hx24, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 hx29_2
  clear hsc_sp
  have hbox_nz : boxU8Buf A.repAlloc (s2.readReg64 .x0) kyberCt ⊢
      ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗ boxU8Buf A.repAlloc (s2.readReg64 .x0) kyberCt := by
    refine Entails.trans (by dsimp only [boxU8Buf,
      CryptoVerification.LibsignalTripleRatchet.boxU8Buf]; exact Entails.refl _) ?_
    refine Entails.pure_left fun ⟨hptr, hlen⟩ => ?_
    have hptr' : s2.readReg64 .x0 ≠ 0#64 := hptr
    rw [pure_true_emp hptr', emp_sepConj]
    dsimp only [boxU8Buf, CryptoVerification.LibsignalTripleRatchet.boxU8Buf]
    rw [pure_true_emp ⟨hptr, hlen⟩, emp_sepConj]
    exact Entails.refl _
  have h48 : vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
      memRegion (sp' + 336#64) 24 ⊢ memRegion (sp' + 312#64) 48 := by
    rw [show (48 : Nat) = 24 + 24 by decide, Prost.memRegion_split (sp' + 312#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr _)
  refine SepWPp.mono_pre
    (P' := ⌜s2.readReg64 .x0 ≠ 0#64⌝ ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        memRegion (sp' + 312#64) 48 ∗
        boxU8Buf A.repAlloc (s2.readReg64 .x0) kyberCt ∗
        A.pool lim (M.stepEvents (intoBoxedCapEvents kyberCap kyberCt) st) s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100)))
    (by
      have hevs_eq : intoBoxedSliceEvents ⟨sp' + 312#64, kyberCap, kyberPtr, kyberCt⟩ =
          intoBoxedCapEvents kyberCap kyberCt := rfl
      refine Entails.trans
        (Q := boxU8Buf A.repAlloc (s2.readReg64 .x0) kyberCt ∗
          ((vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 kyberCt.length) ∗
            memRegion (sp' + 336#64) 24) ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 40#64) ↦₆₄ BitVec.ofNat 64 kyberCt.length) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
            A.pool lim (M.stepEvents (intoBoxedCapEvents kyberCap kyberCt) st) s2 ∗
            stackAt sp' (Prost.skipFieldStackX 100)))
        (by
          rw [hevs_eq, hstackBox]
          simp only [intoBoxedSliceStackX, arm64_norm]
          apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono hbox_nz (sepConj_mono_left h48)) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.pure_pre fun hptr_nz => ?_
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2096#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨s2.readReg64 .x0,
    ⟨⟨by tryFromPost_sp [hsp2], by tryFromPost_sp_align hsp2_align, hcl3,
        by simp [htr2, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29_2, arm64_norm], by simp [arm64_norm],
      by simp [hx27_2, arm64_norm], by simp [hx26_2, arm64_norm],
      by simp [arm64_norm], by simp [hx24_2, arm64_norm],
      by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
      by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
      by simp [hx19_2, arm64_norm]⟩,
    hptr_nz, by apply entails_of_eq; sep_ac_rfl⟩

/-- (``1736 → 1816 → 2072 → 2096``, `[LibsignalPlacement]`):
When `kpkTag = 0#32`, `kyberCap = noneCap`, and `vb.toNat < 0x40`, branches `1736 → 1816 → 2072`,
checks `cmp w22, #64`, sets `x28 = 0#64`, stores `b7`, `b8`, `w15` to stack slots `sp' + 12`,
`sp' + 68`, `sp' + 72`, falls through to `+0x830` (`2096`), and threads `A.pool lim st`. -/
theorem kyber_neither_v3_ok_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberPtr bkLen ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {b7 b8 : BitVec 8} {w15 : BitVec 64}
    {bk : List (BitVec 8)} {pk : PublicKey} {Qp : State → SepProp → Prop}
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hvb_lt : vb.toNat < 0x40)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx8 : s.readReg64 .x8 = (b8.zeroExtend 32).zeroExtend 64)
    (hx11 : s.readReg64 .x11 = w15)
    (hx12 : s.readReg64 .x12 = (b7.zeroExtend 32).zeroExtend 64)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = noneCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗ A.pool lim st s)
      (fun sf Pf =>
        KyberOkStatePlaced s0 sp' sret len ptr0 0#64 kyberPtr ikCap msgCap vb bk pk sf ∧
        (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗ A.pool lim st sf))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcs_vb := w5bw_ule_64_vb_eq_false hvb_lt
  refine SepWPp.mono_pre (sepConj_mono_left (memRegion_four_entails (sp' + 12#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w12 => ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2080#64) ?_
  wp_steps_sync_111 ((blkPl_111).base + 2080#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl1 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2096#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl2 => ?_⟩
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl2,
        by simp [htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes,
      by simp [hx29, arm64_norm], by simp [arm64_norm],
      by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
      by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
      by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
      by simp [hx19, arm64_norm]⟩,
    by apply entails_of_eq; sep_ac_rfl⟩

/-! ## 2. Dealloc Step (`kyber_a1c_to_a24_placed_wp`) -/

/-- Step `+0xa1c .. +0xa20 → +0xa24` (`2588 → 2596`) under `[LibsignalPlacement]`:
deallocates `kyberPtr` (`kyberCap > 0`) and transitions from `KyberExitA1cStatePlaced` at `+0xa1c`
(`2588`) to `KyberExitA24StatePlaced` at `+0xa24` (`2596`) with
`A.pool lim (M.stepEvents (rustDeallocEvents kyberCap.toNat 1) st) sf`. -/
theorem kyber_a1c_to_a24_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {Qp : State → SepProp → Prop}
    (hst : KyberExitA1cStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 2588#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ A.pool lim (M.stepEvents (rustDeallocEvents kyberCap.toNat 1) st) sf ∗
          stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hpos, hlt, _hne,
    hx0, hx1, hx29, hx26, hx23, hx22, hx21, hx20, hx19⟩
  have hstack := stackAt_skipFieldStackX_ext sp'
  have hrlay : RustLayoutOk kyberCap.toNat 1 := ⟨layoutOk_align1 hpos hlt, by decide⟩
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps_sync_111 ((blkPl_111).ρ lsRustDeallocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  refine let_state_pk ?_; intro sc
  have hsc_sp : sc.sp = sp' := by simp [sc, hsp_eq, arm64_norm]
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
    (kyberPtr, kyberCap.toNat, 1, st) hC.deallocX
    (by simp_all [sc, arm64_norm]) (by simp_all [sc, arm64_norm])
    (by simp only [sc, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2596#64) (by simp_all [sc, arm64_norm])
    (T := A.pool lim st sc ∗ A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
      stackAt sp' extHookStack)
    (φ := sc.readReg64 (Reg.gpr 0#5) = kyberPtr ∧
      (sc.readReg64 (Reg.gpr 1#5)).toNat = kyberCap.toNat ∧
      (sc.readReg64 (Reg.gpr 2#5)).toNat = 1 ∧ RustLayoutOk kyberCap.toNat 1 ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 2596#64))
    (by simp_all [sc, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, arm64_norm])
    ⟨by simp [sc, hx0, arm64_norm], by simp [sc, hx1, arm64_norm],
      by simp [sc, arm64_norm], hrlay,
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 2596#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rw [hsc_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, _, hx29_2, _⟩
  dsimp only [sc] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 hx29_2
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  refine ProofLib.SepWP.done hpc2 hrun2 ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨⟨⟨by tryFromPost_sp [hsp2], by tryFromPost_sp_align hsp2_align, hcl3,
        by simp [htr2, htr, arm64_norm]⟩,
      by simp [hx29_2, hx29, arm64_norm],
      by simp [hx26_2, hx26, arm64_norm],
      by simp [hx23_2, hx23, arm64_norm],
      by simp [hx22_2, hx22, arm64_norm],
      by simp [hx21_2, hx21, arm64_norm],
      by simp [hx20_2, hx20, arm64_norm],
      by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  rw [hstack]
  apply entails_of_eq; sep_ac_rfl

/-! ## 3. Placed Shim / Alloc Helpers, `kyber_err_alloc68_head_placed_wpE`, & `kyber_half_err_placed_wpE` -/

theorem w5bw_shim_budget_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (preKeyPlacedProg H) (lsρ lsRustNoAllocShimSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) noAllocShimBudgetSpec) :=
  subroutine_ok_withPreKeyInv_of_plain
    (ls_hook_ok_of_mem (hookSat_noAllocShimBudget_of_withVmPreserved hH.shim))

theorem w5bw_alloc_noOom_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : CodecHooksPlaced M A lim H) :
    subroutine_ok (preKeyPlacedProg H) (lsρ lsRustAllocSym)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack)) :=
  subroutine_ok_withPreKeyInv_of_plain
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem hH.alloc)))

/-- Shared error-allocation head `+0x720 .. +0x780` (`1824 .. 1920`) under `[LibsignalPlacement]`:
under `FitsEvents M lim st (rustAllocEvents 68 1)`, calls `__rust_no_alloc_shim_is_unstable_v2`
and `__rust_alloc(68, 1)` without OOM or panic, copies the 68-byte `.rodata` error string into the
heap buffer, writes `pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext)`, and
reaches `+0x780` (`1920`) with `pstate = addsPState64 (kyberCap - 1#64) 2#64`. -/
theorem kyber_err_alloc68_head_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H)
    (hfit : FitsEvents M lim st (rustAllocEvents 68 1))
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1824#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 1920#64) s
      (memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        sf.pstate = addsPState64 (kyberCap - 1#64) 2#64 ∧
        sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = vb.zeroExtend 64 ∧
        sf.readReg64 .x21 = ptr0 ∧ sf.readReg64 .x20 = len ∧ sf.readReg64 .x19 = sret ∧
        (Pf ⊢ (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 68 1) st) sf ∗
          stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hshim := w5bw_shim_budget_ok hH
  have halloc := w5bw_alloc_noOom_ok hH
  clear hH
  have hstack := stackAt_sub_split sp' allocHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsρ lsRustNoAllocShimSym) ?_
  wp_steps_sync_111 (lsρ lsRustNoAllocShimSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  refine let_state_pk ?_; intro sc1
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded () hshim
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by simp only [sc1, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 1828#64) (by simp_all [sc1, arm64_norm])
    (T := emp)
    (F := memRegion sret 248 ∗ A.pool lim st sc1 ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (φ := True)
    (by simp [noAllocShimBudgetSpec])
    trivial
    (by rw [emp_sepConj]; dsimp only [sc1]; sep_ac_rfl)
    ?_
  clear hshim
  intro s1 hpc1 hrun1 hsp1 hsp1_align hcl1' hcs1
  dsimp only [noAllocShimBudgetSpec]
  refine SepWPp.pure_pre fun ⟨htr1, hvm1⟩ => ?_
  have hpool1 : A.pool lim st sc1 = A.pool lim st s1 := (A.pool_transport lim st sc1 s1 hvm1).symm
  rw [hpool1]
  rw [hsc1_sp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  dsimp only [sc1] at htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  simp only [htr, hx29, hx28, hx27, hx26, hx25, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  clear hpool1 hvm1 hsc1_sp
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl1'
    (mid := lsρ lsRustAllocSym) ?_
  wp_steps_sync_111 (lsρ lsRustAllocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl2 => ?_⟩
  refine let_state_pk ?_; intro sc2
  have hsc2_sp : sc2.sp = sp' := by simp [sc2, hsp1, arm64_norm]
  have hrlay68 : RustLayoutOk 68 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (68, 1, st) halloc
    (by simp_all [sc2, arm64_norm]) (by simp_all [sc2, arm64_norm])
    (by simp only [sc2, State.spAligned, arm64_norm] at hsp1_align ⊢; exact hsp1_align) hcl2
    (ret_pc := (blkPl_111).base + 1840#64) (by simp_all [sc2, arm64_norm])
    (T := A.pool lim st sc2 ∗ stackAt sp' allocHookStack)
    (φ := (sc2.readReg64 .x0).toNat = 68 ∧ (sc2.readReg64 .x1).toNat = 1 ∧
      RustLayoutOk 68 1 ∧ FitsEvents M lim st (rustAllocEvents 68 1) ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 1840#64))
    (by simp_all [sc2, rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
      arm64_norm])
    ⟨by simp [sc2, arm64_norm], by simp [sc2, arm64_norm], hrlay68, hfit,
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 1840#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear halloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2' hcs2
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
  simp only [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨htr2, hoom, _hal⟩ => ?_
  rw [hsc2_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  dsimp only [sc2] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [htr1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, arm64_norm]
    at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  clear hsc2_sp
  have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion68_unpack (s2.readReg64 .x0)))))) ?_
  rw [memRegion248_split_err sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun s0_6 => SepWPp.exists_pre fun s0_5 =>
    SepWPp.exists_pre fun s0_4 => SepWPp.exists_pre fun s0_3 =>
    SepWPp.exists_pre fun s0_2 => SepWPp.exists_pre fun s0_1 =>
    SepWPp.exists_pre fun s0_0 =>
    SepWPp.exists_pre fun w8 => SepWPp.exists_pre fun w7 =>
    SepWPp.exists_pre fun w6 => SepWPp.exists_pre fun w5 =>
    SepWPp.exists_pre fun w4 => SepWPp.exists_pre fun w3 =>
    SepWPp.exists_pre fun w2 => SepWPp.exists_pre fun w1 =>
    SepWPp.exists_pre fun w0 => ?_
  let roBase := lsmpl.ρ "libsignal_protocol:.rodata..Lanon.566"
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2' ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at0 hcl2' "libsignal_protocol:.rodata..Lanon.566" 68) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 8) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 16) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 24) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 32) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 40) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 48) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.566" 68 56) rfl ?_
  wp_steps_sync_111 ((blkPl_111).base + 1920#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨⟨by tryFromPost_sp [hsp2], by tryFromPost_sp_align hsp2_align, hcl3,
      by simp [htr2, arm64_norm]⟩,
    by simp [arm64_norm],
    by simp [hx29_2, arm64_norm],
    by simp [hx28_2, arm64_norm],
    by simp [hx26_2, arm64_norm],
    by simp [hx25_2, arm64_norm],
    by simp [hx23_2, arm64_norm],
    by simp [hx22_2, arm64_norm],
    by simp [hx21_2, arm64_norm],
    by simp [hx20_2, arm64_norm],
    by simp [hx19_2, arm64_norm], ?_⟩
  have hpack68 := memRegion68_pack (s2.readReg64 .x0)
    (s2.mem.read64 roBase)
    (s2.mem.read64 (roBase + 8#64))
    (s2.mem.read64 (roBase + 16#64))
    (s2.mem.read64 (roBase + 24#64))
    (s2.mem.read64 (roBase + 32#64))
    (s2.mem.read64 (roBase + 40#64))
    (s2.mem.read64 (roBase + 48#64))
    (s2.mem.read64 (roBase + 56#64))
    1953391987#32
  have herr := freshString_entails_pksmErrE A.repAlloc sret (s2.readReg64 .x0)
    (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 68
    ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
      ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
      ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
      ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
      ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
      ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
      ((roBase + 48#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 48#64)) ∗
      ((roBase + 56#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 56#64)))
    (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
  have herr' :
      (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
        ((sret + 16#64) ↦₆₄ 68#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
        ((sret + 32#64) ↦₆₄ 68#64) ∗
        ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
        ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
        A.repAlloc.live (s2.readReg64 .x0) 68 1 ∗
        (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 roBase) ∗
          ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (roBase + 8#64)) ∗
          ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (roBase + 16#64)) ∗
          ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (roBase + 24#64)) ∗
          ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (roBase + 32#64)) ∗
          ((s2.readReg64 .x0 + 40#64) ↦₆₄ s2.mem.read64 (roBase + 40#64)) ∗
          ((s2.readReg64 .x0 + 48#64) ↦₆₄ s2.mem.read64 (roBase + 48#64)) ∗
          ((s2.readReg64 .x0 + 56#64) ↦₆₄ s2.mem.read64 (roBase + 56#64)) ∗
          ((s2.readReg64 .x0 + 64#64) ↦₃₂ 1953391987#32)) ∗
        ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
          ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
          ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
          ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
          ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
          ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
          ((roBase + 48#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 48#64)) ∗
          ((roBase + 56#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 56#64))) ⊢
        pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
    Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hpack68))))))))))
      herr
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono_left
        (Q := A.pool lim (M.stepEvents (rustAllocEvents 68 1) st) _ ∗
          stackAt sp' (Prost.skipFieldStackX 100)) herr')
      (by apply entails_of_eq; sep_ac_rfl))
  dsimp only [roBase]
  simp only [hstack, errTag, speWord, arm64_norm]
  apply entails_of_eq; sep_ac_rfl

/-- (``+0x6c8 → +0xa24`, dec `1736 → 2596``):
When `(kpkOpt.isSome != kyberOpt.isSome) = true`, under `FitsEvents M lim st (rustAllocEvents 68 1)`,
branches `+0x6c8` (`1736`) → `+0x720` (`1824`), allocates the 68-byte error string without OOM,
writes `pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext)`, deallocates `kyberPtr`
via `+0xa1c` when `kyberCap > 0`, and reaches `+0xa24` (`2596`). -/
theorem kyber_half_err_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) (hC : PksmCalleesPlaced M A lim H)
    (hfit : FitsEvents M lim st (rustAllocEvents 68 1))
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {kpkTag : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {Qp : State → SepProp → Prop}
    (htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32)
    (hhalf : (kpkOpt.isSome != kyberOpt.isSome) = true)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 kpkTag 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        ∃ evsF : List AllocEvent, FreeOnlyEvs evsF ∧
          (Pf ⊢ (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
            A.pool lim (M.stepEvents (rustAllocEvents 68 1 ++ evsF) st) sf ∗
            stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  subst htag
  cases kpkOpt with
  | some _kpkId =>
    cases kyberOpt with
    | some _ => simp at hhalf
    | none =>
      dsimp only [optVecU8Buf]
      refine SepWPp.pure_pre fun hcap => ?_
      subst hcap
      rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
      have h1 : SepWPp (preKeyPlacedProg H)
          ((blkPl_111).base + 1824#64) s
          (memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueStatePlaced s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = noneCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ memRegion sret 248 ∗ A.pool lim st s1 ∗ stackAt sp' (Prost.skipFieldStackX 100)))
          preKeyNoPanicQp := by
        refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl ?_
        wp_steps_sync_111 ((blkPl_111).base + 1824#64)
        refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          ⟨inferInstance, fun hcl1 => ?_⟩
        exact ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          by apply entails_of_eq; sep_ac_rfl⟩
      refine sepWPp_bind_noPanic h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine SepWPp.mono_pre hent1 ?_; clear hent1
      refine sepWPp_bind_noPanic
        (kyber_err_alloc68_head_placed_wpE hH hfit hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, _hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      refine SepWPp.mono_pre hent2 ?_; clear hent2
      rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
      refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
      wp_steps_sync_111 ((blkPl_111).base + 2596#64)
      refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        ⟨inferInstance, fun hcl3 => ?_⟩
      refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
            by simp [htr2, arm64_norm]⟩,
          by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
          by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
          by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
          by simp [hx19_2, arm64_norm]⟩,
        [], (fun _ h => nomatch h), ?_⟩
      rw [List.append_nil]
      apply entails_of_eq; sep_ac_rfl
  | none =>
    cases kyberOpt with
    | none => simp at hhalf
    | some kyberCt =>
      have hcap_lt :
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen (some kyberCt) ⊢
            ⌜kyberCap.toNat < 2 ^ 63⌝ ∗
              ∃∗ active : Bool, deallocSlot A.repAlloc kyberCap kyberPtr active := by
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨_, hlt, _⟩ => ?_
        have hlt' : kyberCap.toNat < 2 ^ 63 := hlt
        rw [pure_true_emp hlt', emp_sepConj]
        refine Entails.trans ?_ (optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen (some kyberCt))
        dsimp only [optVecU8Buf, Wire.vecU8Buf]
        rw [pure_true_emp hlen, emp_sepConj, pure_true_emp ⟨‹_›, hlt, ‹_›⟩, emp_sepConj]
        exact Entails.refl _
      refine SepWPp.mono_pre (sepConj_mono_left hcap_lt) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_pre fun active => ?_
      refine SepWPp.pure_pre fun hky_lt => ?_
      have hky_eq := cap_add1_eq_of_lt hky_lt
      rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
      have h1 : SepWPp (preKeyPlacedProg H)
          ((blkPl_111).base + 1824#64) s
          (deallocSlot A.repAlloc kyberCap kyberPtr active ∗
            memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
          (fun s1 P1 =>
            PostEpilogueStatePlaced s0 sp' s1 ∧
            s1.readReg64 .x29 = sp' + 512#64 ∧ s1.readReg64 .x28 = kyberCap ∧
            s1.readReg64 .x27 = 0x8000000000000002#64 ∧ s1.readReg64 .x26 = msgCap ∧
            s1.readReg64 .x25 = kyberPtr ∧ s1.readReg64 .x23 = ikCap ∧
            s1.readReg64 .x22 = vb.zeroExtend 64 ∧ s1.readReg64 .x21 = ptr0 ∧
            s1.readReg64 .x20 = len ∧ s1.readReg64 .x19 = sret ∧
            (P1 ⊢ (memRegion sret 248 ∗ A.pool lim st s1 ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
              deallocSlot A.repAlloc kyberCap kyberPtr active))
          preKeyNoPanicQp := by
        refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl ?_
        wp_steps_sync_111 ((blkPl_111).base + 1824#64)
        refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
          ⟨inferInstance, fun hcl1 => ?_⟩
        refine ⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
            by simp [htr, arm64_norm]⟩,
          by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
          by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
          by simp [hx25, arm64_norm], by simp [hx23, arm64_norm],
          by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
          by simp [hx20, arm64_norm], by simp [hx19, arm64_norm],
          by apply entails_of_eq; sep_ac_rfl⟩
      refine sepWPp_bind_noPanic h1 ?_; clear h1
      rintro s1 P1 hpc1 hrun1 ⟨hst1, hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
      refine SepWPp.mono_pre hent1 ?_; clear hent1
      refine sepWPp_bind_frame_noPanic
        (kyber_err_alloc68_head_placed_wpE hH hfit hst1 hpc1 hrun1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hst2, hpstate2, hx29_2, hx28_2, hx26_2, hx25_2, hx23_2, hx22_2, hx21_2, hx20_2, hx19_2, hent2⟩
      refine SepWPp.mono_pre (P' := deallocSlot A.repAlloc kyberCap kyberPtr active ∗
          (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 68 1) st) s2 ∗
          stackAt sp' (Prost.skipFieldStackX 100))
        (Entails.trans (sepConj_mono_left hent2) (by apply entails_of_eq; sep_ac_rfl)) ?_
      clear hent2
      cases active with
      | false =>
        have hdealloc : deallocSlot A.repAlloc kyberCap kyberPtr false = ⌜kyberCap = noneCap ∨ kyberCap = 0#64⌝ := rfl
        rw [hdealloc]
        refine SepWPp.pure_pre fun hcap0 => ?_
        rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
        rcases hcap0 with rfl | rfl
        all_goals
          refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
          wp_steps_sync_111 ((blkPl_111).base + 2596#64)
          refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
            ⟨inferInstance, fun hcl3 => ?_⟩
          refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
                by simp [htr2, arm64_norm]⟩,
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            [], (fun _ h => nomatch h), ?_⟩
          rw [List.append_nil]
          apply entails_of_eq; sep_ac_rfl
      | true =>
        have hdealloc : deallocSlot A.repAlloc kyberCap kyberPtr true =
            (⌜0 < kyberCap.toNat ∧ kyberCap.toNat < 2 ^ 63 ∧ kyberPtr ≠ 0#64⌝ ∗
              A.repAlloc.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat) := rfl
        rw [hdealloc]
        simp only [sepConj_assoc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm]
        refine SepWPp.pure_pre fun ⟨hpos, hlt, hne_ptr⟩ => ?_
        have hhi := cap_sub1_add2_hi_of_pos_lt hpos hlt
        rcases hst2 with ⟨hsp2_eq, hsp2, hcl2, htr2⟩
        let stA := M.stepEvents (rustAllocEvents 68 1) st
        have h3 : SepWPp (preKeyPlacedProg H)
            ((blkPl_111).base + 2588#64) s2
            (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
              pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
              A.pool lim stA s2 ∗ stackAt sp' (Prost.skipFieldStackX 100))
            (fun s3 P3 =>
              KyberExitA1cStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s3 ∧
              (P3 ⊢ (A.live kyberPtr kyberCap.toNat 1 ∗ memRegion kyberPtr kyberCap.toNat ∗
                  A.pool lim stA s3 ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
                (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap)))
            preKeyNoPanicQp := by
          refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl2 (mid := (blkPl_111).base + 1924#64) ?_
          wp_steps_sync_111 ((blkPl_111).base + 1924#64)
          refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
            ⟨inferInstance, fun hcl2' => ?_⟩
          refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2' ?_
          wp_steps_sync_111 ((blkPl_111).base + 2588#64)
          refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
            ⟨inferInstance, fun hcl3 => ?_⟩
          refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2, hcl3,
                by simp [htr2, arm64_norm]⟩,
              hpos, hlt, hne_ptr,
              by simp [arm64_norm], by simp [arm64_norm],
              by simp [hx29_2, arm64_norm], by simp [hx26_2, arm64_norm],
              by simp [hx23_2, arm64_norm], by simp [hx22_2, arm64_norm],
              by simp [hx21_2, arm64_norm], by simp [hx20_2, arm64_norm],
              by simp [hx19_2, arm64_norm]⟩,
            by apply entails_of_eq; sep_ac_rfl⟩
        refine sepWPp_bind_noPanic h3 ?_; clear h3
        rintro s3 P3 hpc3 hrun3 ⟨hst3, hent3⟩
        refine SepWPp.mono_pre hent3 ?_; clear hent3
        refine frame_noPanic_pk (kyber_a1c_to_a24_placed_wp (st := stA) hC hst3 hpc3 hrun3)
          fun sf Pf ⟨hstf, hentf⟩ =>
            ⟨hstf, rustDeallocEvents kyberCap.toNat 1,
              freeOnly_rustDeallocEvents kyberCap.toNat 1, ?_⟩
        dsimp only [stA] at hentf
        rw [M.stepEvents_append]
        refine Entails.trans (sepConj_mono_left hentf) ?_
        apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlacedBudget
