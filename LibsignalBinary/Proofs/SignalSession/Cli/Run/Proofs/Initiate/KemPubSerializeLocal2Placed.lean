/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Proof of `<kem::Key<Public>>::serialize [local#1]`

Proves fixed- and variable-stack `[LibsignalPlacement]` contracts for
`<kem::Key<Public>>::serialize [local#1]` on block `523` (`lsProg_523`), and transfers them to
caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

private theorem stackAt_kemPubSerFixed_placed (sp : BitVec 64) :
    stackAt sp kemPubSerFixedStk =
      stackAt (sp - 48#64) extHookStack ∗ ProofLib.cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_1569_split_placed (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), ProofLib.memRegion_one]

private theorem sepWPp_pure_mid_placed {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem panic_mem_of_trace_eq_placed (s0 : State) {sp : State} {Pm R : SepProp}
    (htr : sp.trace = s0.trace ++ [allocFailedEvent]) (hm : sp.mem ⊨ Pm ∗ R) :
    sp.mem ⊨ ⌜allocFailedIn s0 sp ∧ s0.trace <+: sp.trace⌝ ∗ anyHeap ∗ R := by
  rw [← sepConj_assoc]
  exact Satisfies.mono
    (sepConj_mono_left
      (Entails.pure_right
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq htr)
        (entails_anyHeap Pm)))
    hm

private theorem sp_sub_48_add_48_placed (sp : BitVec 64) : (sp - 48#64) + 48#64 = sp := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit sp_sub_48_add_48_placed BitVec.toNat_zero

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1200000 in
theorem kemPubKeySerialize_local2_fixed_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A H) :
    subroutine_ok (lsProg_523 H) (blkPl_523).base
      (kemPubSerializeValAtStkSpec A kemPubSerFixedStk) := by
  have hshim : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustNoAllocShimSymCli)
      noAllocShimSpec :=
    ls_hook_ok_ultra_of_mem hh.shim
  have halloc : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ lsRustAllocSymCli)
      (rustAllocSpec A) :=
    ls_hook_ok_ultra_of_mem hh.rawAlloc
  have hmemcpy : subroutine_ok (lsProg_523 H) ((blkPl_523).ρ memcpyName)
      sessionMemcpyRegionSpec :=
    ls_hook_ok_ultra_of_mem hh.sessionMemcpyRegion
  have hpanic :
      ((blkPC_523).rebase (blkPl_523).base H).externAt?
        ((blkPl_523).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
    (ls_externAt?_of_mem
      (sym := "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")).trans hh.panic_raw
  clear hh
  simp only [kemPubSerializeValAtStkSpec, stackAt_kemPubSerFixed_placed]
  cells_unfold
  dsimp only [lsProg_523] at hshim halloc hmemcpy ⊢
  wpp_init g s0
  obtain ⟨boxPtr, pkBytes⟩ := g
  dsimp only at *
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_523).base + 72#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := (blkPl_523).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    exact panic_mem_of_trace_eq_placed s0
      (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›]) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split_placed, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid_placed fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, pkBytes)
    wp_steps
    simp only [pointsToBytes_cons]
    wp_done

private theorem memRegion_bound_of_pointsTo64_placed {m : Memory} {b a v : BitVec 64} {n : Nat}
    {R : SepProp} (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

private theorem stackAt_sub_split_placed (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem kemPubKeySerialize_local2_full_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks}
    (hh : RunHooksPlaced W A H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (lsProg_523 H) (lsmpl.base 523)
      (kemPubSerializeFullAtStkSpec A stk) := by
  refine subroutine_ok.of_codeLoaded fun (keyRef, kpkPtr, kpk) R s0 hpc hrun hpre hsp _hL => ?_
  have hle : kemPubSerFixedStk ≤ stk := by
    dsimp [kemPubSerFixedStk]; omega
  have hbound_mem : s0.mem ⊨ memRegion (s0.sp - BitVec.ofNat 64 stk) stk ∗
      ((keyRef ↦₆₄ kpkPtr) ∗
       (⌜s0.readReg64 .x0 = kpkPtr ∧ s0.readReg64 .x1 = 1568#64 ∧ kpk.length = 1568⌝ ∗
        ((keyRef + 8#64) ↦₆₄ 1568#64) ∗ (kpkPtr ↦ₛ kpk) ∗ A.pool ∗ R)) := by
    dsimp only [kemPubSerializeFullAtStkSpec, stackAt] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  have hhi : stk ≤ 2 ^ 64 := memRegion_bound_of_pointsTo64_placed hbound_mem
  have hsplit := stackAt_sub_split_placed s0.sp hle hhi
  let F : SepProp :=
    (keyRef ↦₆₄ kpkPtr) ∗ ((keyRef + 8#64) ↦₆₄ 1568#64) ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kemPubSerFixedStk)
  have hpre' : s0.mem ⊨ (kemPubSerializeValAtStkSpec A kemPubSerFixedStk).pre
      (kpkPtr, kpk) s0 ∗ (F ∗ R) := by
    dsimp only [kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (kemPubKeySerialize_local2_fixed_placed_ok hh).mono_outcome (kpkPtr, kpk) (F ∗ R) s0
    hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [kemPubSerializeFullAtStkSpec, kemPubSerializeValAtStkSpec, F] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

/-- Transfers `kemPubKeySerialize_local2_full_placed_ok` (block `523`) to any caller block `i < 619`. -/
theorem kemPubKeySerialize_local2_full_rocl_ok [LibsignalPlacement]
    {prog : Program} {i : Nat} {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks}
    [IsLsBlockProg prog i H]
    (hh : RunHooksPlaced W A H)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 523)
      (StoreKit.withLsCodeRoLoaded lsmpl (kemPubSerializeFullAtStkSpec A stk)) := by
  have hrocl := StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := prog)
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
      (kemPubKeySerialize_local2_full_placed_ok hh hstk)) hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [StoreKit.withLsRoCl, StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.KemPubSerializeLocal2

end
