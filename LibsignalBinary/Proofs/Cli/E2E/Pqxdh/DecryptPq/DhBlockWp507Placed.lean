/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepTightTargets
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBlocks
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

/-!
# Relocatable DH Ratchet Sub-Block WP Lemmas on Block `507`

Relocatable `[LibsignalPlacement]` `DhCommitBlockWp` and `DhStepBlockWp` symbolic-step witnesses for
Segment `S3` of `try_decrypt_with_state::<signal_session_handshake::Coins>` (Block `507`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
open CryptoVerification.LibsignalSession
open CryptoVerification.CliHandshake.TryDecPlaced

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "wp_reg" : tactic =>
  `(tactic| simp only [wp_norm,
    DhCommitFacts.writeReg64_trace, DhCommitFacts.writeReg32_trace, DhCommitFacts.setPC_trace,
    DhCommitFacts.setPState_trace, DhCommitFacts.setMem_trace, State.trace_writeVReg128,
    *])

local macro "wp_done_reg" hsp_al:ident : tactic =>
  `(tactic| (
    wp_steps
    refine SepWP.done (by rfl) (by wp_reg) ?_
    refine And.intro (by wp_reg) (And.intro (DhCommitFacts.spAligned_of_sp_eq (by wp_reg) $hsp_al) ?_)
    repeat' (refine And.intro ?_ ?_ <;> [wp_reg; skip])
    try rw [← saturating_sub_one_u32 _]
    exact Entails.refl _))

set_option maxHeartbeats 1600000 in
theorem dhCommitBlockWp_507 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhCommitBlockWp ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base (lsmpl.base 513) where
  step1 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx22 hx25 hx27 hx28; wp_done_reg hsp_align
  step2_pre_shim := by intro _ _ _ _ _ s hpc hrun hsp hsp_align hx0 hx1 hx24; wp_done_reg hsp_align
  step2_pre_alloc := by intro _ s hpc hrun hsp hsp_align hx26; wp_done_reg hsp_align
  step2_oom := by intro _ s hpc hrun _hsp _hsp_align hx0; wp_steps; exact SepWP.done (by rfl) (by wp_reg) ⟨by wp_reg, Entails.refl _⟩
  step2_post_alloc := by
    intro _ srkPtr _ s hpc hrun hsp hsp_align hx0 hsrk_ne hx26
    have hbeq : (srkPtr == 0#64) = false := beq_false_of_ne hsrk_ne; wp_done_reg hsp_align
  step2_to_pb := by intro _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align
  step3a_nogrow := by
    intro _ chainsCap rcLen s hpc hrun hsp hsp_align hne
    have hbeq : (rcLen == chainsCap) = false := beq_false_of_ne hne
    have hne' : (rcLen != chainsCap) = true := by simp [hne]
    wp_done_reg hsp_align
  step3a_grow := by intro _ _ s hpc hrun hsp hsp_align; wp_done_reg hsp_align
  step3b := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx24 hx25 hx26 hx27 hx28; wp_done_reg hsp_align
  step4a_lo := by intro _ _ s hpc hrun hsp hsp_align hlo; wp_done_reg hsp_align
  step4a_ge := by intro _ _ s hpc hrun hsp hsp_align hx25 hge; wp_done_reg hsp_align
  step4b_pre_memmove := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28; wp_done_reg hsp_align
  step4b_post_memmove := by
    intro _ _ c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx23 hx24 hx25 hx26 hx27 hx28 hc0_ne
    have hbeq : (c0 + 1#64 == 0#64) = false := beq_false_of_ne hc0_ne; wp_done_reg hsp_align
  step4c_hi := by intro _ _ s hpc hrun hsp hsp_align hhi; wp_done_reg hsp_align
  step4c_le := by intro _ _ s hpc hrun hsp hsp_align hle; wp_done_reg hsp_align
  step5 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hpc hrun hsp hsp_align hx25; wp_done_reg hsp_align

def dhStepBlockWp_507 [LibsignalPlacement] (H : String → Option (State → State)) :
    DhStepBlockWp ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base
      (lsmpl.base 618) where
  missingScAddr := lsmpl.ρ "libsignal_cli_handshake:.rodata..Lanon.2"
  hro_missingSc := by
    intro m P hro hP
    exact lsro_slice_intro hro (sym := "libsignal_cli_handshake:.rodata..Lanon.2") (off := 0)
      (by simp) (by decide +kernel) hP
  wpp_2dc_to_30c := by
    intro s0 s w2c0 w2c8 u34c u344 u338 u330 u2b8 u2b0 u180 u178 u170 u168 u340 u2d0 u18c u188
      sp hpc hrun hsp hsp_al hx29 hx12 hx20 hx25 htrace hvregs
    wp_steps
    have hre : ((sp + 832#64) ↦₃₂ u2d0 ∗ (sp + 836#64) ↦₆₄ u2b0 ∗ (sp + 844#64) ↦₆₄ u2b8 ∗ memRegion (sp + 852#64) 556) =
        ((sp + 832#64) ↦₆₄ (u2b0.extractLsb' 0 32 ++ u2d0) ∗
         (sp + 840#64) ↦₆₄ (u2b8.extractLsb' 0 32 ++ u2b0.extractLsb' 32 32) ∗
         (sp + 848#64) ↦₃₂ u2b8.extractLsb' 32 32 ∗
         memRegion (sp + 852#64) 556) := by
      have := congrArg (· ∗ memRegion (sp + 852#64) 556) (reassoc_4_8_8_to_8_8_4 (sp + 832#64) u2d0 u2b0 u2b8)
      have h1 : sp + 832#64 + 4#64 = sp + 836#64 := by bv_arith
      have h2 : sp + 832#64 + 12#64 = sp + 844#64 := by bv_arith
      have h3 : sp + 832#64 + 8#64 = sp + 840#64 := by bv_arith
      have h4 : sp + 832#64 + 16#64 = sp + 848#64 := by bv_arith
      rw [h1, h2, h3, h4] at this
      exact Eq.trans (by ac_rfl) (Eq.trans this (by ac_rfl))
    rw [hre]
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp, by simp [hx20, sp], by simp, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h178_fold : memRegion (sp + 0x178#64) 24 =
        memRegion (sp + 376#64) 8 ∗ memRegion (sp + 384#64) 8 ∗
        memRegion (sp + 392#64) 4 ∗ memRegion (sp + 396#64) 4 := by
      rw [show sp + 0x178#64 = sp + 376#64 from rfl,
          memRegion_split' (b := sp + 376#64) (b' := sp + 384#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 384#64) (b' := sp + 392#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 392#64) (b' := sp + 396#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    have h190_fold : memRegion (sp + 0x190#64) 0x3f0 =
        memRegion (sp + 400#64) 288 ∗ memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗
        memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗
        memRegion (sp + 724#64) 92 ∗ memRegion (sp + 816#64) 8 ∗ memRegion (sp + 824#64) 8 ∗
        memRegion (sp + 832#64) 8 ∗ memRegion (sp + 840#64) 8 ∗ memRegion (sp + 848#64) 4 ∗
        memRegion (sp + 852#64) 556 := by
      rw [show sp + 0x190#64 = sp + 400#64 from rfl,
          memRegion_split' (b := sp + 400#64) (b' := sp + 688#64) (n := 288) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 816#64) (n := 92) (k := 592) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 816#64) (b' := sp + 824#64) (n := 8) (k := 584) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 824#64) (b' := sp + 832#64) (n := 8) (k := 576) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 832#64) (b' := sp + 840#64) (n := 8) (k := 568) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 840#64) (b' := sp + 848#64) (n := 8) (k := 560) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 848#64) (b' := sp + 852#64) (n := 4) (k := 556) rfl (by bv_arith) (by decide)]
    rw [h178_fold, h190_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_7f8_to_2dc := by
    intro s0 s u508 u500 u2c8 u2c0 u2b8 u2b0 u2d0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [sp], by simp, by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have h140_fold : memRegion (sp + 0x140#64) 0x440 =
        memRegion (sp + 320#64) 88 ∗ memRegion (sp + 408#64) 8 ∗ memRegion (sp + 416#64) 272 ∗
        memRegion (sp + 688#64) 8 ∗ memRegion (sp + 696#64) 8 ∗ memRegion (sp + 704#64) 8 ∗
        memRegion (sp + 712#64) 8 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 724#64) 556 ∗
        memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 8 ∗ memRegion (sp + 1296#64) 112 := by
      rw [show sp + 0x140#64 = sp + 320#64 from rfl,
          memRegion_split' (b := sp + 320#64) (b' := sp + 408#64) (n := 88) (k := 992 + 8) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 408#64) (b' := sp + 416#64) (n := 8) (k := 992) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 416#64) (b' := sp + 688#64) (n := 272) (k := 720) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 688#64) (b' := sp + 696#64) (n := 8) (k := 712) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 696#64) (b' := sp + 704#64) (n := 8) (k := 704) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 704#64) (b' := sp + 712#64) (n := 8) (k := 696) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 712#64) (b' := sp + 720#64) (n := 8) (k := 688) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 720#64) (b' := sp + 724#64) (n := 4) (k := 684) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 724#64) (b' := sp + 1280#64) (n := 556) (k := 128) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1280#64) (b' := sp + 1288#64) (n := 8) (k := 120) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 1288#64) (b' := sp + 1296#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide)]
    rw [h140_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_missing_sc := by
    intro s0 s x u2c0 u2c8 sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], by simp [hx12, sp], by simp [hx19], by simp [hx20, sp],
       by simp [hx25, sp], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    have hsp38_fold : memRegion sp 0x38 =
        memRegion sp 0x20 ∗ memRegion (sp + 0x20#64) 8 ∗ memRegion (sp + 0x28#64) 4 ∗
        memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x30#64) 8 := by
      rw [memRegion_split' (b := sp) (b' := sp + 0x20#64) (n := 32) (k := 24) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x28#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 4) (k := 12) rfl (by bv_arith) (by decide),
          memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 4) (k := 8) rfl (by bv_arith) (by decide)]
    rw [hsp38_fold]
    change m ⊨ _
    arm64_sep_close
  wpp_cc1_err := by
    intro s0 s u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc1_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_pre_cc1 := by
    intro s0 s x p0 p1 p2 p3 k0 k1 k2 k3 u390 u398 u3a0 u3a8 u3b0 u3b8 u3c0 u3c8
      sp hpc hrun hsp hsp_al hx29 hx12 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], by simp, by simp [sp], by simp [sp],
       by simp [hx19], by simp [hx20, sp], by simp [hx21], by simp [hx22], by simp [hx23, sp],
       by simp [hx24], by simp [hx25, sp], by simp [sp], by simp [hx27, sp],
       by simp [hx28, sp], by simp [hx29], rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_ok := by
    intro s0 s sp hpc hrun hsp hsp_al hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_cc2_err := by
    intro s0 s msgW u1bc u1b4 u1a8 u1a0 u1c4 u1b0 sp hpc hrun hsp hsp_al hx29 hx20 hx23 hx25 hx26 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx29], rfl, by simp [hx20, sp], by simp [hx23, sp],
       by simp [hx25, sp], by simp [hx26, sp], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_70c_to_778 := by
    intro s0 s r0 r4 c2 u10 u1c u3e0 u4a0 u4bc u510
      r1 r2 r3 c0 c1 c3 c4 u3d0 u3d8 u3e4 u3ec u400 u408 u440 u448
      u4a4 u4ac u4b4 u4c0 u4c8 u4d0 u4d8 u500 u508
      sp hpc hrun hsp hsp_al hx29 hx23 hx25 hx26 htrace hvregs
    rw [show s0.sp - 96#64 = sp + 0x580#64 by dsimp only [sp]; bv_arith] at hx29
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp], rfl, rfl, rfl, rfl, rfl,
       by simp [hx23, sp], by simp [hx25, sp], rfl, rfl, by simp [sp],
       by simp [hx29, sp]; bv_arith, rfl, by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_778_to_rng := by
    intro s0 s u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx1 hx25 hv0 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx1], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_780_to_7a8 := by
    intro s0 s b0 b31 sp hpc hrun hsp hsp_al hx29 hx23 hx25 htrace hvregs
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, by simp [sp],
       rfl, rfl, rfl, rfl, rfl, by simp [sp], rfl, rfl, rfl, rfl,
       by simp [hx29], by simp [htrace], by simp [arm64_norm, hvregs], fun m R hm => ?_⟩
    rw [clamp_byte0 b0, clamp_byte31 b31] at hm
    arm64_sep_close
  wpp_7a8_to_dpk := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx0 hx8 hx23 hx25 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [hx0, sp], by simp [hx8, sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7b4_to_sd := by
    intro s0 s p0 p1 p2 p3 u0 u1 u2 u3 sp hpc hrun hsp hsp_al hx29 hx23 hx28 htrace
    wp_steps
    refine SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp, sp], by simp [sp]; bv_arith, rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace], fun m R hm => ?_⟩
    arm64_sep_close
  wpp_7c4_to_cc2 := by
    intro s0 s2 msgA sp hpc2 hrun2 hsp2 hsp_al2 hx22_2 hx24_2 hx29_2 htrace2
    wp_steps
    refine SepWP.done rfl (by simp [hrun2])
      ⟨by simp [hsp2], by simp [sp]; bv_arith, by simp,
       by simp [sp], by simp [sp], rfl,
       ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
       by simp [htrace2], fun m R hm => ?_⟩
    simpa [emp_sepConj] using hm

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
