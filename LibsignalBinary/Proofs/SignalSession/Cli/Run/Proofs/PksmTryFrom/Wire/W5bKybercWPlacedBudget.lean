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
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberc
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` Missing-Kyber v4 Error and Full Kyber `Ok` Dispatch

Allocation-budget (`RustCliAllocBudget M`) proofs of panic-free
`kyber_neither_v4_err_placed_wpE` (`+0x6c8 → +0xa24`) and `w5b_kyber_ok_placed_wpW`
(`+0x684 → +0x830`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlacedBudget

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
  w5bc_SepWPp kyber_neither_v4_err_placed_wpE w5b_kyber_ok_placed_wpW
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp
)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (
  PksmCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlacedBudget (
  kyber_both_ok_placed_wp kyber_neither_v3_ok_placed_wp pk_scatter_head_placed_wp
  sepWPp_anyQp_of_noPanic w5bw_alloc_noOom_ok w5bw_shim_budget_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  boxU8Buf noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget (
  IntoBoxedCapEnv IntoBoxedOptCapEnv intoBoxedCapEvents
)

abbrev w5bc_SepWPp := @Wire.SepWPp
private abbrev w5bc_pure_pre := @Wire.SepWPp.pure_pre
private abbrev w5bc_exists_pre := @Wire.SepWPp.exists_pre
private abbrev w5bc_mono_pre := @Wire.SepWPp.mono_pre
private abbrev w5bc_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev w5bc_of_sepWP_end_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.of_sepWP_end_noPanic_pk
private abbrev w5bc_call_noPanic_budget_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.call_noPanic_budget_pk
private abbrev w5bc_frame_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.frame_noPanic_pk
private abbrev w5bc_let_state_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.let_state

private theorem w5bc_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s : State} {P F : SepProp} {Qm : State → SepProp → Prop}
    {Q : State → SepProp → Prop}
    (h1 : w5bc_SepWPp prog mid s P Qm preKeyNoPanicQp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Qm sm Pm →
      w5bc_SepWPp prog ret sm (Pm ∗ F) Q preKeyNoPanicQp) :
    w5bc_SepWPp prog ret s (P ∗ F) Q preKeyNoPanicQp := by
  refine Wire.SepWPp.bind (Qm := fun sm Pf => ∃ Pm, Pf = Pm ∗ F ∧ Qm sm Pm)
    (w5bc_frame_noPanic_pk h1 fun sm Pm hq => ⟨Pm, rfl, hq⟩) ?_
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

/-! ## 1. ``kyber_neither_v4_err_placed_wpE``: (`+0x6c8 → +0xa24`) -/

/-- (``+0x6c8 → +0xa24`, dec `1736 → 2596``):
When `kpkTag = 0#32`, `kyberOpt = none` (`kyberCap = noneCap`), and `0x40 ≤ vb.toNat`,
under `FitsEvents M lim st (rustAllocEvents 54 1)`, branches `+0x6c8` (`1736`) → `+0x718` (`1816`)
→ `+0x818` (`2072`) → `+0x998` (`2456`), allocates the 54-byte `.rodata` error string without OOM
or panic, writes `pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext)`, and
reaches `+0xa24` (`2596`). -/
theorem kyber_neither_v4_err_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H)
    (hfit : FitsEvents M lim st (rustAllocEvents 54 1))
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {Qp : State → SepProp → Prop}
    (hvb_ge : 0x40 ≤ vb.toNat)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1736#64)
    (hrun : s.status = .Running)
    (hpstate : s.pstate = subsPState32 0#32 1#32)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (_hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = vb.zeroExtend 64) (hx21 : s.readReg64 .x21 = ptr0)
    (hx20 : s.readReg64 .x20 = len) (hx19 : s.readReg64 .x19 = sret) :
    w5bc_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen none ∗
        memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
        (Pf ⊢ (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 54 1) st) sf ∗
          stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  dsimp only [optVecU8Buf]
  refine w5bc_pure_pre fun hcap => ?_
  subst hcap
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hshim := w5bw_shim_budget_ok hH
  have halloc := w5bw_alloc_noOom_ok hH
  clear hH
  have hvb_ule := ule_64_vb_eq_true hvb_ge
  have hstack := stackAt_sub_split sp' allocHookStack (Prost.skipFieldStackX 100) (by decide) (by decide)
  refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl
    (mid := lsρ lsRustNoAllocShimSym) ?_
  wp_steps_sync_111 (lsρ lsRustNoAllocShimSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl1 => ?_⟩
  refine w5bc_let_state_pk ?_; intro sc1
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  refine w5bc_call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded () hshim
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by simp only [sc1, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2460#64) (by simp_all [sc1, arm64_norm])
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
  refine w5bc_pure_pre fun ⟨htr1, hvm1⟩ => ?_
  have hpool1 : A.pool lim st sc1 = A.pool lim st s1 := (A.pool_transport lim st sc1 s1 hvm1).symm
  rw [hpool1]
  rw [hsc1_sp] at hsp1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, _, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  dsimp only [sc1] at htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hx29_1
  simp only [htr, hx29, hx28, hx27, hx26, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx26_1 hx27_1 hx28_1 hx29_1
  clear hpool1 hvm1 hsc1_sp
  refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl1'
    (mid := lsρ lsRustAllocSym) ?_
  wp_steps_sync_111 (lsρ lsRustAllocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl2 => ?_⟩
  refine w5bc_let_state_pk ?_; intro sc2
  have hsc2_sp : sc2.sp = sp' := by simp [sc2, hsp1, arm64_norm]
  have hrlay54 : RustLayoutOk 54 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine w5bc_call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded (54, 1, st) halloc
    (by simp_all [sc2, arm64_norm]) (by simp_all [sc2, arm64_norm])
    (by simp only [sc2, State.spAligned, arm64_norm] at hsp1_align ⊢; exact hsp1_align) hcl2
    (ret_pc := (blkPl_111).base + 2472#64) (by simp_all [sc2, arm64_norm])
    (T := A.pool lim st sc2 ∗ stackAt sp' allocHookStack)
    (φ := (sc2.readReg64 .x0).toNat = 54 ∧ (sc2.readReg64 .x1).toNat = 1 ∧
      RustLayoutOk 54 1 ∧ FitsEvents M lim st (rustAllocEvents 54 1) ∧
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 ((blkPl_111).base + 2472#64))
    (by simp_all [sc2, rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
      arm64_norm])
    ⟨by simp [sc2, arm64_norm], by simp [sc2, arm64_norm], hrlay54, hfit,
      LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add 111 2472#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  clear halloc
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2' hcs2
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
  simp only [sepConj_assoc]
  refine w5bc_pure_pre fun ⟨htr2, hoom, _hal⟩ => ?_
  rw [hsc2_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  dsimp only [sc2] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [htr1, hx29_1, hx28_1, hx27_1, hx26_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, arm64_norm]
    at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 hx29_2
  clear hsc2_sp
  have hbeq : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  refine w5bc_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion54_unpack (s2.readReg64 .x0))))))) ?_
  rw [memRegion248_split_err sret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine w5bc_exists_pre fun s0_6 => w5bc_exists_pre fun s0_5 =>
    w5bc_exists_pre fun s0_4 => w5bc_exists_pre fun s0_3 =>
    w5bc_exists_pre fun s0_2 => w5bc_exists_pre fun s0_1 =>
    w5bc_exists_pre fun s0_0 =>
    w5bc_exists_pre fun w5 => w5bc_exists_pre fun w4 =>
    w5bc_exists_pre fun w3 => w5bc_exists_pre fun w2 =>
    w5bc_exists_pre fun w1 => w5bc_exists_pre fun w0 => ?_
  let roBase := lsmpl.ρ "libsignal_protocol:.rodata..Lanon.565"
  refine w5bc_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl2' (mid := (blkPl_111).base + 2504#64) ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at0 hcl2' "libsignal_protocol:.rodata..Lanon.565" 54) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 8) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 16) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 24) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 32) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 40) rfl ?_
  refine SepWP.rodata64_intro (w5bw_rodata_ro8_at hcl2' "libsignal_protocol:.rodata..Lanon.565" 54 46) rfl ?_
  wp_steps_sync_111 ((blkPl_111).base + 2504#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl3 => ?_⟩
  have hshift := shift_window_40_to_46 (s2.readReg64 .x0) (s2.mem.read64 (roBase + 40#64))
  refine w5bc_mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (Entails.trans (by apply entails_of_eq; rw [← sepConj_assoc])
              (Entails.trans (sepConj_mono_left hshift)
                (by apply entails_of_eq; rw [sepConj_assoc])))))))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine w5bc_exists_pre fun w46 => ?_
  refine w5bc_of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl3 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2596#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hcl4 => ?_⟩
  refine ⟨⟨⟨by tryFromPost_sp [hsp2], by tryFromPost_sp_align hsp2_align, hcl4,
        by simp [htr2, arm64_norm]⟩,
      by simp [hx29_2, arm64_norm],
      by simp [hx26_2, arm64_norm],
      by simp [hx23_2, arm64_norm],
      by simp [hx22_2, arm64_norm],
      by simp [hx21_2, arm64_norm],
      by simp [hx20_2, arm64_norm],
      by simp [hx19_2, arm64_norm]⟩, ?_⟩
  have hpack54 := memRegion54_pack (s2.readReg64 .x0)
    (s2.mem.read64 roBase)
    (s2.mem.read64 (roBase + 8#64))
    (s2.mem.read64 (roBase + 16#64))
    (s2.mem.read64 (roBase + 24#64))
    (s2.mem.read64 (roBase + 32#64))
    (s2.mem.read64 (roBase + 46#64))
  have herr := freshString_entails_pksmErrE A.repAlloc sret (s2.readReg64 .x0)
    (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64) s0_6 54
    ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
      ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
      ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
      ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
      ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
      ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
      ((roBase + 46#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 46#64)))
    (by decide) (by decide) hoom (bf_low8_eq_3 s0_5)
  have herr' :
      (sret ↦₆₄ errTag) ∗ ((sret + 8#64) ↦₆₄ speWord 24) ∗
        ((sret + 16#64) ↦₆₄ 54#64) ∗ ((sret + 24#64) ↦₆₄ s2.readReg64 .x0) ∗
        ((sret + 32#64) ↦₆₄ 54#64) ∗
        ((sret + 40#64) ↦₆₄ (s0_5 &&& bv% (2 ^ 64 - 256) ||| 3#64)) ∗
        ((sret + 48#64) ↦₆₄ s0_6) ∗ memRegion (sret + 56#64) 192 ∗
        A.repAlloc.live (s2.readReg64 .x0) 54 1 ∗
        (((s2.readReg64 .x0) ↦₆₄ s2.mem.read64 roBase) ∗
          ((s2.readReg64 .x0 + 8#64) ↦₆₄ s2.mem.read64 (roBase + 8#64)) ∗
          ((s2.readReg64 .x0 + 16#64) ↦₆₄ s2.mem.read64 (roBase + 16#64)) ∗
          ((s2.readReg64 .x0 + 24#64) ↦₆₄ s2.mem.read64 (roBase + 24#64)) ∗
          ((s2.readReg64 .x0 + 32#64) ↦₆₄ s2.mem.read64 (roBase + 32#64)) ∗
          memRegion (s2.readReg64 .x0 + 40#64) 6 ∗
          ((s2.readReg64 .x0 + 46#64) ↦₆₄ s2.mem.read64 (roBase + 46#64))) ∗
        ((roBase ↦₆₄ᵣ s2.mem.read64 roBase) ∗
          ((roBase + 8#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 8#64)) ∗
          ((roBase + 16#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 16#64)) ∗
          ((roBase + 24#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 24#64)) ∗
          ((roBase + 32#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 32#64)) ∗
          ((roBase + 40#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 40#64)) ∗
          ((roBase + 46#64) ↦₆₄ᵣ s2.mem.read64 (roBase + 46#64))) ⊢
        pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap :=
    Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left hpack54))))))))))
      herr
  refine Entails.trans ?_
    (Entails.trans
      (sepConj_mono_left
        (Q := A.pool lim (M.stepEvents (rustAllocEvents 54 1) st) _ ∗
          stackAt sp' (Prost.skipFieldStackX 100)) herr')
      (by apply entails_of_eq; sep_ac_rfl))
  dsimp only [roBase]
  simp only [hstack, errTag, speWord, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm, arm64_norm]
  apply entails_of_eq; sep_ac_rfl

/-! ## 2. ``w5b_kyber_ok_placed_wpW``: Full Kyber `Ok` Dispatch (`+0x684 → +0x830`) -/

/-- (``+0x684 → +0x830`, dec `1668 → 2096``):
Composes `pk_scatter_head_placed_wp` with `kyber_both_ok_placed_wp` and `kyber_neither_v3_ok_placed_wp`
from `BaseKeyOkStatePlaced` at `+0x684` (`1668`) to `KyberOkStatePlaced` at `+0x830` (`2096`)
with `kyberSpillsAtW`, `kyberStageOut A.repAlloc`, and `IntoBoxedOptCapEnv kyberCap kyberOpt`. -/
theorem w5b_kyber_ok_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkCap bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen : BitVec 64}
    {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (IntoBoxedOptCapEnv kyberCap kyberOpt))
    (hkpk : match kpkOpt with | some id => kpkTag = 1#32 ∧ kpkVal = id | none => kpkTag = 0#32)
    (hok : (kpkOpt.isSome && kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40))
    (hst : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running) :
    w5bc_SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ (evsK : List AllocEvent) (kyberBoxPtr kyberBoxLen : BitVec 64)
          (b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8)
          (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64),
          IntoBoxedOptCapEnv kyberCap kyberOpt evsK ∧
          (bk.take 33).drop 1 = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∧
          KyberOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf ∧
          (Pf ⊢ kyberSpillsAtW sp' bkCap bkPtr kyberLen ikPtr ikLen msgPtr msgLen
              regTag regVal opkTag opkVal spkVal kpkVal
              b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 ∗
            memRegion (sp' + 312#64) 48 ∗
            kyberStageOut A.repAlloc kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen ∗
            A.pool lim (M.stepEvents evsK st) sf ∗ stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  apply sepWPp_anyQp_of_noPanic
  rcases hst with ⟨hst_ep, hbk_ok, hpk_eq, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  have hpre_split :
      memRegion (sp' + 12#64) 4 ∗
        seg1SpillsAtW sp' bkCap bkPtr bkLen kyberLen ikPtr ikLen msgPtr msgLen
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100) ⊢
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (sp' + 345#64) 15 ∗ A.pool lim st s) ∗
      (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion (sp' + 12#64) 4 ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
        ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
        ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 72#64) ↦₆₄ bkLen) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        stackAt sp' (Prost.skipFieldStackX 100)) := by
    dsimp only [seg1SpillsAtW]
    apply entails_of_eq; sep_ac_rfl
  refine w5bc_mono_pre hpre_split ?_
  refine w5bc_bind_frame_noPanic
    (pk_scatter_head_placed_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21 hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, hx8_1, hx11_1, hx12_1,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx24_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  refine w5bc_mono_pre (sepConj_mono_left hent1) ?_
  rcases hok with hboth | ⟨rfl, rfl, hvb_lt⟩
  · cases kpkOpt with
    | none => simp at hboth
    | some kpkId =>
      cases kyberOpt with
      | none => simp at hboth
      | some kyberCt =>
        rcases hkpk with ⟨rfl, rfl⟩
        have hvec_lt :
            optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen (some kyberCt) ⊢
              ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
                Wire.vecU8Buf A.repAlloc kyberCap kyberPtr kyberCt := by
          dsimp only [optVecU8Buf, Wire.vecU8Buf]
          refine Entails.pure_left fun hlen => Entails.pure_left fun ⟨hle, hlt, hne⟩ => ?_
          rw [pure_true_emp ⟨hlen, hlt⟩, emp_sepConj, pure_true_emp ⟨hle, hlt, hne⟩, emp_sepConj]
          exact Entails.refl _
        refine w5bc_mono_pre (P' :=
            ⌜kyberLen = BitVec.ofNat 64 kyberCt.length ∧ kyberCap.toNat < 2 ^ 63⌝ ∗
            ((memRegion (sp' + 12#64) 4 ∗
              ((sp' + 40#64) ↦₆₄ kyberLen) ∗
              ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗
              memRegion (sp' + 312#64) 48 ∗
              Wire.vecU8Buf A.repAlloc kyberCap kyberPtr kyberCt ∗
              A.pool lim st s1 ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
             (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
              ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
              ((sp' + 32#64) ↦₆₄ msgLen) ∗
              ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
              ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
              ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
              ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
              spUnused112 sp' ∗
              ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
              ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
              sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6)))
          (by
            refine Entails.trans (sepConj_mono_right (sepConj_mono_left hvec_lt)) ?_
            apply entails_of_eq; sep_ac_rfl) ?_
        refine w5bc_pure_pre fun ⟨hky_len, hky_lt⟩ => ?_
        subst hky_len
        have hfit_cap : FitsEnv M lim st (IntoBoxedCapEnv kyberCap kyberCt) := hfit
        refine w5bc_frame_noPanic_pk
          (kyber_both_ok_placed_wp hC hfit_cap hbk_ok hpk_eq hpk_bytes hky_lt hst1 hpc1 hrun1 hpstate1
            hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
          fun sf Pf ⟨kyberBoxPtr, hstf, hptr_nz, hentf⟩ => ?_
        refine ⟨intoBoxedCapEvents kyberCap kyberCt, kyberBoxPtr, BitVec.ofNat 64 kyberCt.length,
          b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23,
          rfl, hpk_of, hstf, ?_⟩
        refine Entails.trans (sepConj_mono_left hentf) ?_
        dsimp only [kyberSpillsAtW, kyberStageOut]
        rw [pure_true_emp ⟨hptr_nz, rfl, rfl⟩, emp_sepConj]
        apply entails_of_eq; sep_ac_rfl
  · subst hkpk
    refine w5bc_mono_pre (P' :=
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen none ∗
        ((memRegion (sp' + 12#64) 4 ∗
          ((sp' + 68#64) ↦₃₂ 0#32) ∗ ((sp' + 72#64) ↦₆₄ bkLen) ∗ A.pool lim st s1) ∗
         (((sp' + 16#64) ↦₃₂ kpkVal) ∗ ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 32#64) ↦₆₄ msgLen) ∗ ((sp' + 40#64) ↦₆₄ kyberLen) ∗
          ((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ memRegion (sp' + 64#64) 4 ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ spUnused112 sp' ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗
          ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          memRegion (sp' + 312#64) 48 ∗ stackAt sp' (Prost.skipFieldStackX 100))))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    dsimp only [optVecU8Buf]
    refine w5bc_pure_pre fun hcap => ?_
    subst hcap
    refine w5bc_frame_noPanic_pk
      (kyber_neither_v3_ok_placed_wp hbk_ok hpk_eq hpk_bytes hvb_lt hst1 hpc1 hrun1 hpstate1
        hx8_1 hx11_1 hx12_1 hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ?_
    refine ⟨[], 0#64, kyberPtr, b0, b1, b2, b3, b4, b5, b6, b7, b8, b31, w9, w13, w15, w23,
      rfl, hpk_of, hstf, ?_⟩
    rw [M.stepEvents_nil]
    refine Entails.trans (sepConj_mono_left hentf) ?_
    dsimp only [kyberSpillsAtW, kyberStageOut]
    rw [pure_true_emp ⟨rfl, hvb_lt⟩]; apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlacedBudget
