/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseSidFs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import ProofLib.SepLogic.WPp

/-!
# Relocatable `ServiceId::parse_from_service_id_string` Preserving `fs` (Block `206`)

Proves relocatable `ServiceId::parse_from_service_id_string` on Block `206` (calling `<Uuid>::try_parse`
on Block `252`) with `.keepsFs` under `[LibsignalPlacement]`, and lifts it to any caller block via
`StoreKit.withLsRoCl` and `withLsCl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ParseServiceId
open CryptoVerification.SignalSession.Cli.MainHops.UuidFs

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem fs_writeReg_placed (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

set_option maxHeartbeats 800000 in
/-- Relocatable `ServiceId::parse_from_service_id_string` (Block `206`) with caller-supplied
`withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack).keepsFs` on Block `252`. -/
theorem parseSid_placed_okFs_of_contract_stack [LibsignalPlacement]
    (H : LibsignalHooks) (hookStack : Nat := 0)
    (huuid_entry : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H)
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseStackSpec hookStack).keepsFs)) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack).keepsFs) := by
  have huuid := ls_subroutine_ok_of_block (callerProg := (blkPC_206).rebase (blkPl_206).base H) huuid_entry
  change subroutine_ok _ (lsmpl.base 252) _ at huuid
  unfold withLsCodeLoaded Spec.keepsFs at huuid ⊢
  simp only [parseSidCodeStackSpec, parseSidSpec, uuidTryParseStackSpec, uuidTryParseSpec]
    at huuid ⊢
  clear huuid_entry
  wp_init x s0
  obtain ⟨p, bs, out⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_eq : (s0.readReg64 (Reg.gpr 1#5)).toNat = bs.length := by assumption
  rw [memRegion_17_none_split out, stackAt_parseSidFrame_split s0.sp]
  wp_pull_exists
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_206).base + bv% (16))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_steps
  wp_if hlt4
  · rw [serviceIdParse_of_lt_4 bs (toNat_lt_of_ult hlen_eq hlt4), parseSidResultAt]
    wp_steps
    wp_done
  · obtain ⟨b0, b1, b2, b3, bs', rfl⟩ := exists_cons4_of_le (le_of_not_ult hlen_eq hlt4)
    rw [pointsToBytes_cons4 p b0 b1 b2 b3 bs']
    wp_steps
    wp_if hpni
    · rw [serviceIdParse_cons4_pni b0 b1 b2 b3 bs' hpni]
      wp_steps
      wp_if hlen40
      · have hne36 := length_ne_36_of_ne_40 hlen_eq hlen40
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_40 hlen_eq hlen40
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p + 4#64, bs', s0.sp - 64#64)
        cases hparse : uuidTryParse bs' with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out true u]
          wp_pull_exists
          wp_steps
          wp_done
    · rw [serviceIdParse_cons4_aci b0 b1 b2 b3 bs' hpni, ← pointsToBytes_cons4 p b0 b1 b2 b3 bs']
      wp_steps
      wp_if hlen36
      · have hne36 := length_ne_36_of_ne_36 hlen_eq hlen36
        simp only [hne36, ↓reduceIte, parseSidResultAt]
        wp_steps
        wp_done
      · have heq36 := length_eq_36_of_eq_36 hlen_eq hlen36
        simp only [heq36, ↓reduceIte]
        wp_steps
        wp_call huuid (p, b0 :: b1 :: b2 :: b3 :: bs', s0.sp - 64#64)
        cases hparse : uuidTryParse (b0 :: b1 :: b2 :: b3 :: bs') with
        | none =>
          rw [uuidResultAt_sp64_none s0.sp, memRegion_sp64_none_split s0.sp]
          dsimp only [Option.map, parseSidResultAt]
          wp_steps
          wp_done
        | some u =>
          rw [uuidResultAt_sp64_some s0.sp u, memRegion_sp64_some_split s0.sp,
              memRegion_out1_16_split out]
          dsimp only [Option.map]
          rw [parseSidResultAt_some_eq out false u]
          wp_pull_exists
          wp_steps
          wp_done

private theorem hookStack_le_of_frame_disjoint_placed {m : Memory} {sp : BitVec 64} {hookStack : Nat}
    {R : SepProp}
    (hm : m ⊨ stackAt (sp - 80#64) hookStack ∗ stackAt sp parseSidFrameStack ∗ R) :
    hookStack ≤ 2 ^ 64 := by
  by_cases h0 : hookStack = 0
  · omega
  · have hm' :
        m ⊨ memRegion (sp - 80#64) 80 ∗
          (memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack ∗ R) := by
      dsimp only [stackAt, parseSidFrameStack] at hm
      ac_nf at hm ⊢
    have hd := disjointRegions_of_coversRegion (by decide) (Nat.pos_of_ne_zero h0)
      (IsBlock.memRegion (sp - 80#64) 80).covers
      (IsBlock.memRegion ((sp - 80#64) - BitVec.ofNat 64 hookStack) hookStack).covers
      hm'
    have hlt1 := (((sp - 80#64) - BitVec.ofNat 64 hookStack) - (sp - 80#64)).isLt
    have hlt2 := ((sp - 80#64) - ((sp - 80#64) - BitVec.ofNat 64 hookStack)).isLt
    have h1 := hd.1
    have h2 := hd.2
    omega

/-- Relocatable `ServiceId::parse_from_service_id_string` on Block `206` with `.keepsFs`, for any
`hookStack ≥ uuidTryParseStack`. -/
theorem parseSid_blk206_okFs [LibsignalPlacement] (H : LibsignalHooks)
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide) :
    subroutine_ok ((blkPC_206).rebase (blkPl_206).base H)
      (blkPl_206).base
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack).keepsFs) := by
  intro x R s0 hpc hrun hpre hal hL
  have hmax : hookStack ≤ 2 ^ 64 := by
    have hm :
        s0.mem ⊨ stackAt (s0.sp - 80#64) hookStack ∗ stackAt s0.sp parseSidFrameStack ∗
          (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
            (parseSidSpec (serviceIdParse uuidTryParse)).pre x s0 ∗ R) := by
      dsimp only [withLsCodeLoaded, Spec.keepsFs, parseSidCodeStackSpec] at hpre
      ac_nf at hpre ⊢
    exact hookStack_le_of_frame_disjoint_placed hm
  exact parseSid_placed_okFs_of_contract_stack H hookStack
    (uuidTryParse_stack_keepsFs_placed H hstack hmax)
    x R s0 hpc hrun hpre hal hL

private theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_local
    {α : Type} {prog : Program} {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨⟨hcl, _⟩, hpre_spec⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl, hpre_spec⟩
  intro hL
  exact h.to_outcome x R s0 hpc hrun hpre' hsp hL

/-- Relocatable `ServiceId::parse_from_service_id_string` lifted to any caller block `prog`
(`IsLsBlockProg prog i H`, `i < 619`) at `lsmpl.base 206` with `StoreKit.withLsRoCl lsmpl`. -/
theorem parseSid_placed_okFs_rocl [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl (parseSidCodeStackSpec hookStack).keepsFs) := by
  have h0 : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (lsmpl.base 206)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (parseSidCodeStackSpec hookStack).keepsFs) :=
    subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_local
      (parseSid_blk206_okFs H hookStack hstack)
  exact LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block
    (callerProg := prog) h0 hi (by decide) (by decide)

/-- Relocatable `ServiceId::parse_from_service_id_string` lifted to any caller block `prog`
(`IsLsBlockProg prog i H`, `i < 619`) at `lsmpl.base 206` with `withLsCl lsmpl`. -/
theorem parseSid_placed_okFs_cl [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (hookStack : Nat := extHookStack)
    (hstack : uuidTryParseStack ≤ hookStack := by decide)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsmpl.base 206)
      (withLsCl lsmpl (parseSidCodeStackSpec hookStack).keepsFs) := by
  have h0 : subroutine_ok ((blkPC_206).rebase (blkPl_206).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackSpec hookStack).keepsFs) :=
    parseSid_blk206_okFs H hookStack hstack
  exact ls_subroutine_ok_cl_of_block (callerProg := prog) h0 hi (by decide) (by decide)

end CryptoVerification.SignalSession.Cli.MainHops
