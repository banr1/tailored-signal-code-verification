/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS1Err507Placed
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.RegChain

/-!
# Relocatable Segment `S2` Step and Call Lemmas on Block `507`

Relocatable `[LibsignalPlacement]` symbolic step lemmas and `find_receiver_chain_key` call
reachability for Segment `S2` of `try_decrypt_with_state::<signal_session_handshake::Coins>`
(Block `507`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding memRegion_eight
open CryptoVerification.LibsignalTripleRatchet.Getters hiding drop_chain_placed_ok
open CryptoVerification.LibsignalTripleRatchet.Decrypt hiding
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  DhStepStatePlaced ConsumeMsgKeyStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  VerifyMacStatePlaced AesDecryptStatePlaced ApplyRatchetStatePlaced
  ErrTailSeamPlaced S0SeamPlaced S1SeamPlaced S2SeamPlaced S3SeamPlaced S4SeamPlaced
  S5SeamPlaced S6SeamPlaced S7SeamPlaced S8SeamPlaced S9SeamPlaced
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup hiding arrayAt_nil arrayAt_cons
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt
open CryptoVerification.CliHandshake.TryDecPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem findChain_bl_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = segFindChainPC_at (blkPl_508).base) (hmeta : tryDecryptWPInv s0 s) :
    SepWP ((blkPC_508).rebase (blkPl_508).base H)
      (lsmpl.base 25) s emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_508).base + 680#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x8 = s.readReg64 .x8 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only [segFindChainPC_at] at hpc
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem findChain_err_1a_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 d0 : BitVec 64} {w1_lo w1_hi d1_lo d1_hi : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 680#64) (hmeta : tryDecryptWPInv s0 s) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 720#64) s
      (((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗
       ((sp + 416#64) ↦₃₂ w1_lo) ∗ ((sp + 420#64) ↦₃₂ w1_hi) ∗
       ((sp + 704#64) ↦₆₄ d0) ∗ ((sp + 712#64) ↦₃₂ d1_lo) ∗ ((sp + 716#64) ↦₃₂ d1_hi))
      (fun sf P =>
        P = (((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗
             ((sp + 416#64) ↦₃₂ w1_lo) ∗ ((sp + 420#64) ↦₃₂ w1_hi) ∗
             ((sp + 704#64) ↦₆₄ w0) ∗ ((sp + 712#64) ↦₃₂ w1_lo) ∗ ((sp + 716#64) ↦₃₂ w1_hi)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem findChain_err_1b_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 b0 b1 s1 s2 : BitVec 64} {d8c d2d0 s0_w : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 720#64) (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 704#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 756#64) s
      (((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗
       ((sp + 704#64) ↦₆₄ w0) ∗ ((sp + 712#64) ↦₆₄ w1) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗
       ((sp + 832#64) ↦₃₂ s0_w) ∗ ((sp + 836#64) ↦₆₄ s1) ∗ ((sp + 844#64) ↦₆₄ s2))
      (fun sf P =>
        P = (((sp + 396#64) ↦₃₂ 24#32) ∗ ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗
             ((sp + 704#64) ↦₆₄ w0) ∗ ((sp + 712#64) ↦₆₄ w1) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗
             ((sp + 832#64) ↦₃₂ d2d0) ∗ ((sp + 836#64) ↦₆₄ b0) ∗ ((sp + 844#64) ↦₆₄ b1)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20 ∧
        sf.readVReg128 1#5 = w1 ++ w0) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  exact ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm, speWord], by simp_all [arm64_norm]⟩

theorem findChain_err_1c_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 u0 u1 c0 c1 g0 g1 g2 g3 : BitVec 64} {u2 g4 : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 756#64) (hmeta : tryDecryptWPInv s0 s)
    (hx12 : s.readReg64 .x12 = (s0.sp - 1504#64) + 704#64)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hq1 : s.readVReg128 1#5 = w1 ++ w0) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (errTailPC_at (blkPl_508).base) s
      (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 368#64) ↦₆₄ g1) ∗ ((sp + 376#64) ↦₆₄ g2) ∗
       ((sp + 384#64) ↦₆₄ g3) ∗ ((sp + 392#64) ↦₃₂ g4) ∗ ((sp + 816#64) ↦₆₄ c0) ∗
       ((sp + 824#64) ↦₆₄ c1) ∗ ((sp + 832#64) ↦₆₄ u0) ∗ ((sp + 840#64) ↦₆₄ u1) ∗
       ((sp + 848#64) ↦₃₂ u2))
      (fun sf P =>
        P = (((sp + 360#64) ↦₆₄ w0) ∗ ((sp + 368#64) ↦₆₄ w1) ∗ ((sp + 376#64) ↦₆₄ u0) ∗
             ((sp + 384#64) ↦₆₄ u1) ∗ ((sp + 392#64) ↦₃₂ u2) ∗ ((sp + 816#64) ↦₆₄ w0) ∗
             ((sp + 824#64) ↦₆₄ w1) ∗ ((sp + 832#64) ↦₆₄ u0) ∗ ((sp + 840#64) ↦₆₄ u1) ∗
             ((sp + 848#64) ↦₃₂ u2)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = s.readReg64 .x26) := by
  dsimp only [errTailPC_at]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  exact ⟨by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem findChain_ok_branch_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {tag : BitVec 32} {s0 s : State}
    (htag : (tag != 2#32) = true)
    (hpc : s.pc = (blkPl_508).base + 680#64) (hmeta : tryDecryptWPInv s0 s) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog ((blkPl_508).base + 948#64) s
      ((sp + 400#64) ↦₃₂ tag)
      (fun sf P =>
        P = ((sp + 400#64) ↦₃₂ tag) ∧
        tryDecryptWPInv s0 sf ∧
        (sf.readReg64 .x9).setWidth 32 = tag ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem findChain_ok_none_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 948#64) (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 0#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segDhStepPC_at (blkPl_508).base) s
      (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
       ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗ ((sp + 896#64) ↦₆₄ d0) ∗
       ((sp + 904#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
             ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗ ((sp + 896#64) ↦₆₄ w3) ∗
             ((sp + 904#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only [segDhStepPC_at]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem findChain_ok_some_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 948#64) (hmeta : tryDecryptWPInv s0 s)
    (hx9 : (s.readReg64 .x9).setWidth 32 = 1#32)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segConsumeMsgKeyPC_at (blkPl_508).base) s
      (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
       ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗ ((sp + 688#64) ↦₆₄ b0) ∗
       ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 704#64) ↦₃₂ c0) ∗ ((sp + 708#64) ↦₆₄ c1) ∗
       ((sp + 716#64) ↦₆₄ c2) ∗ ((sp + 896#64) ↦₆₄ d0) ∗ ((sp + 904#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
             ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗ ((sp + 688#64) ↦₆₄ w3) ∗
             ((sp + 696#64) ↦₆₄ w4) ∗ ((sp + 704#64) ↦₃₂ w0) ∗ ((sp + 708#64) ↦₆₄ w1) ∗
             ((sp + 716#64) ↦₆₄ w2) ∗ ((sp + 896#64) ↦₆₄ w3) ∗ ((sp + 904#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only [segConsumeMsgKeyPC_at]
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  wp_steps
  wp_finish
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem findChain_err_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 w1 g0 g1 g2 g3 b0 b1 d0 c0 c1 s1 s2 : BitVec 64}
    {g4 d8c d1_lo d1_hi d2d0 s0_w : BitVec 32} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (errTailPC_at (blkPl_508).base) s
      (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 368#64) ↦₆₄ g1) ∗ ((sp + 376#64) ↦₆₄ g2) ∗
       ((sp + 384#64) ↦₆₄ g3) ∗ ((sp + 392#64) ↦₃₂ g4) ∗ ((sp + 396#64) ↦₃₂ d8c) ∗
       ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗ ((sp + 416#64) ↦₆₄ w1) ∗
       ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 704#64) ↦₆₄ d0) ∗
       ((sp + 712#64) ↦₃₂ d1_lo) ∗ ((sp + 716#64) ↦₃₂ d1_hi) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗
       ((sp + 816#64) ↦₆₄ c0) ∗ ((sp + 824#64) ↦₆₄ c1) ∗ ((sp + 832#64) ↦₃₂ s0_w) ∗
       ((sp + 836#64) ↦₆₄ s1) ∗ ((sp + 844#64) ↦₆₄ s2))
      (fun sf P =>
        let u0 := b0.extractLsb' 0 32 ++ d2d0
        let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
        let u2 := b1.extractLsb' 32 32
        P = (((sp + 360#64) ↦₆₄ w0) ∗ ((sp + 368#64) ↦₆₄ w1) ∗ ((sp + 376#64) ↦₆₄ u0) ∗
             ((sp + 384#64) ↦₆₄ u1) ∗ ((sp + 392#64) ↦₃₂ u2) ∗ ((sp + 396#64) ↦₃₂ 24#32) ∗
             ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗ ((sp + 416#64) ↦₆₄ w1) ∗
             ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 704#64) ↦₆₄ w0) ∗
             ((sp + 712#64) ↦₆₄ w1) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗ ((sp + 816#64) ↦₆₄ w0) ∗
             ((sp + 824#64) ↦₆₄ w1) ∗ ((sp + 832#64) ↦₆₄ u0) ∗ ((sp + 840#64) ↦₆₄ u1) ∗
             ((sp + 848#64) ↦₃₂ u2)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x26 = speWord 20) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hsplit_416 :
      ((sp + 416#64) ↦₆₄ w1) =
        ((sp + 416#64) ↦₃₂ w1.extractLsb' 0 32) ∗ ((sp + 420#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 416#64) w1
  have hsplit_712 :
      ((sp + 712#64) ↦₆₄ w1) =
        ((sp + 712#64) ↦₃₂ w1.extractLsb' 0 32) ∗ ((sp + 716#64) ↦₃₂ w1.extractLsb' 32 32) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (sp + 712#64) w1
  have h1a := findChain_err_1a_507_wp_placed (H := H)
    (w0 := w0) (w1_lo := w1.extractLsb' 0 32) (w1_hi := w1.extractLsb' 32 32)
    (d0 := d0) (d1_lo := d1_lo) (d1_hi := d1_hi) hpc hmeta
  refine SepWP.rw_pre (by rw [hsplit_416]) ?_
  refine SepWP.bind_framed
    (F := ((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 368#64) ↦₆₄ g1) ∗ ((sp + 376#64) ↦₆₄ g2) ∗
          ((sp + 384#64) ↦₆₄ g3) ∗ ((sp + 392#64) ↦₃₂ g4) ∗ ((sp + 396#64) ↦₃₂ d8c) ∗
          ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗
          ((sp + 816#64) ↦₆₄ c0) ∗ ((sp + 824#64) ↦₆₄ c1) ∗ ((sp + 832#64) ↦₃₂ s0_w) ∗
          ((sp + 836#64) ↦₆₄ s1) ∗ ((sp + 844#64) ↦₆₄ s2))
    h1a (by dsimp only [sp]; sep_ac_rfl) ?_
  intro s1a P1a ⟨hP1a, hmeta1a, hx12_1a, hx19_1a, hx20_1a, hx25_1a⟩ hpc1a
  subst hP1a
  have h1b := findChain_err_1b_507_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (b0 := b0) (b1 := b1) (s1 := s1) (s2 := s2)
    (d8c := d8c) (d2d0 := d2d0) (s0_w := s0_w) hpc1a hmeta1a hx12_1a (hx25_1a.trans hx25)
  refine SepWP.bind_framed
    (F := ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗ ((sp + 416#64) ↦₆₄ w1) ∗
          ((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 368#64) ↦₆₄ g1) ∗ ((sp + 376#64) ↦₆₄ g2) ∗
          ((sp + 384#64) ↦₆₄ g3) ∗ ((sp + 392#64) ↦₃₂ g4) ∗ ((sp + 816#64) ↦₆₄ c0) ∗
          ((sp + 824#64) ↦₆₄ c1))
    h1b (by rw [hsplit_416, hsplit_712]; dsimp only [sp]; sep_ac_rfl) ?_
  intro s1b P1b ⟨hP1b, hmeta1b, hx12_1b, hx19_1b, hx20_1b, hx26_1b, hq1_1b⟩ hpc1b
  subst hP1b
  have hrealign :
      (((sp + 832#64) ↦₃₂ d2d0) ∗ ((sp + 836#64) ↦₆₄ b0) ∗ ((sp + 844#64) ↦₆₄ b1)) =
      (((sp + 832#64) ↦₆₄ (b0.extractLsb' 0 32 ++ d2d0)) ∗
       ((sp + 840#64) ↦₆₄ (b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32)) ∗
       ((sp + 848#64) ↦₃₂ b1.extractLsb' 32 32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using realign_20_bytes (sp + 832#64) d2d0 b0 b1
  have h1c := findChain_err_1c_507_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (u0 := b0.extractLsb' 0 32 ++ d2d0)
    (u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32) (u2 := b1.extractLsb' 32 32)
    (c0 := c0) (c1 := c1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3) (g4 := g4)
    hpc1b hmeta1b hx12_1b (by reg_chain) hq1_1b
  refine SepWP.bind_framed
    (F := ((sp + 396#64) ↦₃₂ 24#32) ∗ ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ w0) ∗
          ((sp + 416#64) ↦₆₄ w1) ∗ ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗
          ((sp + 704#64) ↦₆₄ w0) ∗ ((sp + 712#64) ↦₆₄ w1) ∗ ((sp + 720#64) ↦₃₂ d2d0))
    h1c (by rw [← hrealign]; dsimp only [sp]; sep_ac_rfl) ?_
  intro sf Pf ⟨hPf, hmetaf, hx19_f, hx20_f, hx26_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨by dsimp only [sp]; sep_ac_rfl, hmetaf, by reg_chain⟩

theorem findChain_ok_none_full_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 : BitVec 32} {w1 w2 w3 w4 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segDhStepPC_at (blkPl_508).base) s
      (((sp + 400#64) ↦₃₂ 0#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗
       ((sp + 416#64) ↦₆₄ w2) ∗ ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
       ((sp + 896#64) ↦₆₄ d0) ∗ ((sp + 904#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 400#64) ↦₃₂ 0#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗
             ((sp + 416#64) ↦₆₄ w2) ∗ ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
             ((sp + 896#64) ↦₆₄ w3) ∗ ((sp + 904#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := findChain_ok_branch_507_wp_placed (H := H) (tag := 0#32) (by decide) hpc hmeta
  refine SepWP.bind_framed hbr (by sep_frame) ?_
  intro s1 P1 ⟨hP1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 400#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 704#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hnone := findChain_ok_none_507_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed hnone (by sep_frame) ?_
  intro sf Pf ⟨hPf, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  sep_ac_rfl

theorem findChain_ok_some_full_507_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w0 c0 : BitVec 32} {w1 w2 w3 w4 b0 b1 c1 c2 d0 d1 : BitVec 64} {s0 s : State}
    (hpc : s.pc = (blkPl_508).base + 680#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segConsumeMsgKeyPC_at (blkPl_508).base) s
      (((sp + 400#64) ↦₃₂ 1#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗
       ((sp + 416#64) ↦₆₄ w2) ∗ ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
       ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 704#64) ↦₃₂ c0) ∗
       ((sp + 708#64) ↦₆₄ c1) ∗ ((sp + 716#64) ↦₆₄ c2) ∗ ((sp + 896#64) ↦₆₄ d0) ∗
       ((sp + 904#64) ↦₆₄ d1))
      (fun sf P =>
        P = (((sp + 400#64) ↦₃₂ 1#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗
             ((sp + 416#64) ↦₆₄ w2) ∗ ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
             ((sp + 688#64) ↦₆₄ w3) ∗ ((sp + 696#64) ↦₆₄ w4) ∗ ((sp + 704#64) ↦₃₂ w0) ∗
             ((sp + 708#64) ↦₆₄ w1) ∗ ((sp + 716#64) ↦₆₄ w2) ∗ ((sp + 896#64) ↦₆₄ w3) ∗
             ((sp + 904#64) ↦₆₄ w4)) ∧
        tryDecryptWPInv s0 sf ∧
        sf.readReg64 .x12 = sp + 704#64 ∧
        CalleeSavedPreserved s sf) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hbr := findChain_ok_branch_507_wp_placed (H := H) (tag := 1#32) (by decide) hpc hmeta
  refine SepWP.bind_framed hbr (by sep_frame) ?_
  intro s1 P1 ⟨hP1, hmeta1, hx9_1, hcs1⟩ hpc1
  subst hP1
  have hx25_1 : s1.readReg64 .x25 = sp + 400#64 := (hcs1.2.2.2.2.2.2.1).trans hx25
  have hx28_1 : s1.readReg64 .x28 = sp + 704#64 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans hx28
  have hsome := findChain_ok_some_507_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    hpc1 hmeta1 hx9_1 hx25_1 hx28_1
  refine SepWP.bind_framed hsome (by sep_frame) ?_
  intro sf Pf ⟨hPf, hmetaf, hx12_f, hcsf⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨?_, hmetaf, hx12_f, CalleeSavedPreserved.trans hcs1 hcsf⟩
  sep_ac_rfl

theorem findChain_call_findReceiverChainKey_507_reaches_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A)))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State)
    (hS2 : FindChainStatePlaced (blkPl_508).base A ctl x trG tr st1 R s0 s) :
    let prog := (blkPC_508).rebase (blkPl_508).base H
    let sp := s0.sp - 1504#64
    reaches_pc prog ((blkPl_508).base + 680#64) s
      (fun s_ret =>
        tryDecryptMidMeta_placed s0 s_ret ∧
        LibsignalRoLoaded lsmpl s_ret.mem ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 320#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 1280#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = sp + 400#64 ∧
        s_ret.readReg64 .x27 = sp + 56#64 ∧
        s_ret.readReg64 .x28 = sp + 704#64 ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
          trAt A (sp + 56#64) trG tr ∗
          memRegion x.ret 48 ∗ memRegion sp 32 ∗
          ((sp + 32#64) ↦₆₄ x.locA) ∗ ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
          memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 320#64) 80 ∗
          findReceiverChainKeyResultAt (sp + 400#64) (tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey) ∗
          memRegion (sp + 440#64) 968 ∗
          cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS2 with ⟨hpc, hmeta_full, hx0, hx1, hx8, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hmem⟩
  obtain ⟨hmeta, hro⟩ := tryDecryptMidMetaPlaced_to_placed_507 hmeta_full
  have hwp_bl := findChain_bl_507_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗ ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 1088 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  have hcl_s : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  refine reaches_pc_seq_lscl hcl_s (reaches_pc_lsro_preserve hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _ ⟨⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩ hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold cliTryDecryptCommonHeapPlaced at hm_call
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest, memRegion_0x140_split_findReceiverChainKey,
      show FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let fg : FindReceiverChainKeyGhost :=
    { self := sp + 56#64, G := trG.ratchet, st := tr.ratchet,
      theirA := x.msgA + 56#64, their := x.msg.senderRatchetKey, ret := sp + 400#64 }
  let F_call : SepProp :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trRestAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 440#64) 968 ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageRestAt A x.msgG x.msgA x.msg ∗
    cliTapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - findReceiverChainKeyStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R
  have hfrck_blk := ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H) hfrck
  rw [show (blkPl_25).base = lsmpl.base 25 from rfl] at hfrck_blk
  have hpre_call : s_call.mem ⊨ (findReceiverChainKeyPlacedSpec A).pre fg s_call ∗ F_call := by
    dsimp only [findReceiverChainKeyPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hro_call, hx0_c.trans hx0, hx1_c.trans hx1, hx8_c.trans hx8⟩, ?_⟩
    rw [hsp_call]
    dsimp only [fg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl hfrck_blk fg F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [findReceiverChainKeyPlacedSpec] at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨hro_ret, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain,
     hcl_ret, by reg_chain⟩
  refine ⟨hmeta_ret, hro_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold cliTryDecryptCommonHeapPlaced
  rw [trAt_eq_ratchetAt_trRestAt, signalMessageAt_eq_srk_rest,
      show FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp findReceiverChainKeyStack (by decide)]
  dsimp only [fg, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup
