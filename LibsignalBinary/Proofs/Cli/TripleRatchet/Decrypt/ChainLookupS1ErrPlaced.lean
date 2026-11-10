/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupErrSymPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.RegChain

/-!
# Relocatable Tight Segment `S1` and `ErrTail` on Block `433`

Proves the relocatable tight-panic seams `S1TightSeamPlaced` and `ErrTailTightSeamPlaced` for
`try_decrypt_with_state::<Coins>` (block `433`).
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem loadRatchet_bl_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = segLoadRatchetPC_at (blkPl_434).base)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 57) s emp
      (fun s1 P1 =>
        P1 = emp ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_434).base + 484#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 400#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segLoadRatchetPC_at] at hpc
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem loadRatchet_err_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    SepWP prog (retEpiloguePC_at (blkPl_434).base) s
      (((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ tag) ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗
       ((sp + 1280#64) ↦₆₄ t0) ∗
       words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 400#64) ↦₆₄ errTag) ∗
             ((sp + 408#64) ↦₆₄ tag) ∗
             words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗
             ((sp + 1280#64) ↦₆₄ tag) ∗
             words5At (sp + 1288#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [retEpiloguePC_at]
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩⟩

theorem loadRatchet_ok_1a_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 528#64) s
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 400#64) ↦₆₄ cap) ∗ words4At (sp + 408#64) w0 w1 w2 w3 ∗
       ((sp + 440#64) ↦₆₄ w4) ∗ ((sp + 448#64) ↦₆₄ w5) ∗ words4At (sp + 1280#64) t0 t1 t2 t3 ∗
       ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 32#64) ↦₆₄ locA) ∗ ((sp + 400#64) ↦₆₄ cap) ∗ words4At (sp + 408#64) w0 w1 w2 w3 ∗
             ((sp + 440#64) ↦₆₄ w4) ∗ ((sp + 448#64) ↦₆₄ w5) ∗ words4At (sp + 1280#64) w0 w1 w2 w3 ∗
             ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5)) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 400#64 ∧ sf.readReg64 .x27 = sp + 56#64) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1b_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 w24 w25 w26 w27 w28 w29 w30 w31 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_434).base + 528#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap) (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 56#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 588#64) s
      (((sp + 48#64) ↦₆₄ remA) ∗ ((sp + 56#64) ↦₆₄ d_cap) ∗ ((sp + 456#64) ↦₆₄ w6) ∗
       ((sp + 464#64) ↦₆₄ w7) ∗ ((sp + 536#64) ↦₆₄ w16) ∗ ((sp + 544#64) ↦₆₄ w17) ∗
       words8At (sp + 600#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 256#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 48#64) ↦₆₄ remA) ∗ ((sp + 56#64) ↦₆₄ cap) ∗ ((sp + 456#64) ↦₆₄ w6) ∗
             ((sp + 464#64) ↦₆₄ w7) ∗ ((sp + 536#64) ↦₆₄ w16) ∗ ((sp + 544#64) ↦₆₄ w17) ∗
             words8At (sp + 600#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 256#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 56#64 ∧ sf.readReg64 .x1 = msgA + 56#64 ∧
        sf.readReg64 .x8 = remA ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 704#64 ∧ sf.readVReg128 0#5 = w17 ++ w16 ∧ sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem tryDecryptMidMetaPlaced_to_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMetaPlaced s0 s) :
    tryDecryptMidMeta_placed s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1.1, h.2.2.2.2.2.2.2⟩, h.2.2.2.2.2.2.1.2⟩

theorem tryDecryptMidMetaPlaced_of_placed [LibsignalPlacement] {s0 s : State}
    (h : tryDecryptMidMeta_placed s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    tryDecryptMidMetaPlaced s0 s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    ⟨h.2.2.2.2.2.2.1, hro⟩, h.2.2.2.2.2.2.2⟩

theorem loadRatchet_ok_1c_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_434).base + 588#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 56#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) ((blkPl_434).base + 620#64) s
      (((sp + 472#64) ↦₆₄ w8) ∗ ((sp + 480#64) ↦₆₄ w9) ∗ ((sp + 552#64) ↦₆₄ w18) ∗
       ((sp + 560#64) ↦₆₄ w19) ∗ words4At (sp + 568#64) w20 w21 w22 w23 ∗
       words8At (sp + 192#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 472#64) ↦₆₄ w8) ∗ ((sp + 480#64) ↦₆₄ w9) ∗ ((sp + 552#64) ↦₆₄ w18) ∗
             ((sp + 560#64) ↦₆₄ w19) ∗ words4At (sp + 568#64) w20 w21 w22 w23 ∗
             words8At (sp + 192#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧ sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_1d_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 620#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA) (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8) (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 488#64) ↦₆₄ w10) ∗ ((sp + 496#64) ↦₆₄ w11) ∗
       words4At (sp + 504#64) w12 w13 w14 w15 ∗ ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
       ((msgA + 104#64) ↦₃₂ counter) ∗ words8At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 128#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 40#64) ↦₃₂ counter) ∗ ((sp + 488#64) ↦₆₄ w10) ∗ ((sp + 496#64) ↦₆₄ w11) ∗
             words4At (sp + 504#64) w12 w13 w14 w15 ∗ ((sp + 672#64) ↦₆₄ remA) ∗
             ((sp + 684#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗ words4At (sp + 1280#64) w0 w1 w2 w3 ∗
             ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗ ((msgA + 104#64) ↦₃₂ counter) ∗
             words8At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 128#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 400#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segFindChainPC_at]
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; wp_steps; wp_finish
  exact ⟨by ac_rfl, ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], hs0_align,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem loadRatchet_ok_433_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    SepWP prog (segFindChainPC_at (blkPl_434).base) s
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 48#64) ↦₆₄ remA) ∗
       ((sp + 56#64) ↦₆₄ d_cap) ∗
       words32At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 400#64) ↦₆₄ cap) ∗
       words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) t0 t1 t2 t3 ∗ ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5) ∗
       ((msgA + 104#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 32#64) ↦₆₄ locA) ∗ ((sp + 40#64) ↦₃₂ counter) ∗ ((sp + 48#64) ↦₆₄ remA) ∗
               ((sp + 56#64) ↦₆₄ cap) ∗
               words32At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 400#64) ↦₆₄ cap) ∗
               words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 672#64) ↦₆₄ remA) ∗ ((sp + 684#64) ↦₈ b2ac) ∗
               words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
               ((msgA + 104#64) ↦₃₂ counter)) ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 56#64 ∧ sf.readReg64 .x1 = msgA + 56#64 ∧
          sf.readReg64 .x8 = sp + 400#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = sp + 400#64 ∧
          sf.readReg64 .x27 = sp + 56#64 ∧ sf.readReg64 .x28 = sp + 704#64) := by
  dsimp only
  have h1a := loadRatchet_ok_1a_433_wp_placed (H := H)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed h1a (by sep_frame) ?_
  intro s1a P1a ⟨hP1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a, hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := loadRatchet_ok_1b_433_wp_placed (H := H)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed h1b (by sep_frame) ?_
  intro s1b P1b ⟨hP1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b, hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := loadRatchet_ok_1c_433_wp_placed (H := H)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed h1c (by sep_frame) ?_
  intro s1c P1c ⟨hP1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c, hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := loadRatchet_ok_1d_433_wp_placed (H := H)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    hpc1c hmeta1c (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    hq0_1c (by reg_chain)
  refine SepWP.bind_framed h1d (by sep_frame) ?_
  intro sf Pf ⟨hPf, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_, hmetaf, by reg_chain⟩
  rw [words32At_40_eq, words32At_198_eq]
  sep_ac_rfl

theorem loadRatchet_call_trFrom_433_reaches_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base (trFromPlacedSpec A))
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetStatePlaced (blkPl_434).base A ctl x R s0 s) :
    let prog := (blkPC_434).rebase (blkPl_434).base H
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog ((blkPl_434).base + 484#64) s
      (fun s_ret =>
        tryDecryptMidMeta_placed s0 s_ret ∧
        s_ret.readReg64 .x19 = x.ret ∧
        s_ret.readReg64 .x20 = sp + 320#64 ∧
        s_ret.readReg64 .x21 = x.ss ∧
        s_ret.readReg64 .x22 = x.msgA ∧
        s_ret.readReg64 .x23 = sp + 1280#64 ∧
        (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s_ret.readReg64 .x25 = x.locA ∧
        (s_ret.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom res.2 ∗
          trResultAt A (sp + 400#64) x.G res.1 ∗
          memRegion x.ret 48 ∗
          memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗
          memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 664#64) 744 ∗
          cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta_full, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  obtain ⟨hmeta, hro⟩ := tryDecryptMidMetaPlaced_to_placed hmeta_full
  have hwp_bl := loadRatchet_bl_433_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt A x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  refine reaches_pc_seq_lscl hmeta.2.2.2.2.2.2.1 (reaches_pc_lsro hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _ ⟨⟨P1, hm_call, ⟨hP1, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩ hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold cliTryDecryptCommonHeapPlaced at hm_call
  have h56_split :
      memRegion (sp + 56#64) 1352 =
      memRegion (sp + 56#64) 344 ∗ memRegion (sp + 400#64) 264 ∗ memRegion (sp + 664#64) 744 := by
    rw [show (1352 : Nat) = 344 + (264 + 744) by decide,
        memRegion_split (sp + 56#64) 344 (264 + 744) (by decide),
        show sp + 56#64 + 344#64 = sp + 400#64 by bv_omega,
        memRegion_split (sp + 400#64) 264 744 (by decide),
        show sp + 400#64 + 264#64 = sp + 664#64 by bv_omega]
  rw [h56_split, show FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 400#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
    protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ R
  have htrFrom_blk := ls_subroutine_ok_of_block (callerProg := (blkPC_434).rebase (blkPl_434).base H) htrFrom
  rw [show (blkPl_57).base = lsmpl.base 57 from rfl] at htrFrom_blk
  have hpre_call : s_call.mem ⊨ (withLsRoLoaded lsmpl (trFromRawPlacedSpec A)).pre tg s_call ∗ F_call := by
    dsimp only [withLsRoLoaded, trFromRawPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro_call, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]; dsimp only [tg, F_call, sp] at hm_call ⊢; convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl htrFrom_blk tg F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [withLsRoLoaded, trFromRawPlacedSpec] at hpost_ret
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨_, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain, hcl_ret, by reg_chain⟩
  refine ⟨hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold cliTryDecryptCommonHeapPlaced
  rw [show FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) from rfl,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)]
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

private theorem loadRatchet_err_pre_extract_433 {A : RustAlloc}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {F : SepProp} {s0 s : State} (hnpan : e ≠ .panic)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗ F) :
    let sp := s0.sp - 1504#64
    ∃ (w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64) (H_spe : SepProp),
      (∀ q : BitVec 64, (q ↦₆₄ speTag e) ∗ words5At (q + 8#64) w0 w1 w2 w3 w4 ∗ H_spe ⊢
        speAt A (utf8 "decrypt") q e) ∧
      (s.mem ⊨
        (((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
         words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ ((sp + 1280#64) ↦₆₄ t0) ∗
         words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5) ∗
        (H_spe ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 48 ∗
         ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
         memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
         memRegion (sp + 1328#64) 80 ∗ F)) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (((sp + 400#64) ↦₆₄ errTag) ∗ speAt A (utf8 "decrypt") (sp + 400#64 + 8#64) e ∗
     memRegion (sp + 400#64 + 56#64) 208) ∗
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗ F at hm
  rw [show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega,
      show sp + 400#64 + 56#64 = sp + 456#64 by bv_omega,
      speAt_eq_speTag_speBodyAt hnpan,
      show sp + 408#64 + 8#64 = sp + 416#64 by bv_omega,
      show (744 : Nat) = 616 + 128 by decide,
      memRegion_split (sp + 664#64) 616 128 (by decide),
      show sp + 664#64 + 616#64 = sp + 1280#64 by bv_omega,
      show (128 : Nat) = 48 + 80 by decide,
      memRegion_split (sp + 1280#64) 48 80 (by decide),
      show sp + 1280#64 + 48#64 = sp + 1328#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 416#64) e ∗
      (memRegion (sp + 1280#64) 48 ∗ memRegion x.ret 48 ∗ ((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
       memRegion (sp + 1328#64) 80 ∗ F) := by convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hm2, hent_spe⟩ := exists_words5_of_speBodyAt hnpan hm1
  have hm3 : s.mem ⊨ memRegion (sp + 1280#64) 48 ∗
      (memRegion x.ret 48 ∗ words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
       ((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 56#64) 344 ∗ memRegion (sp + 456#64) 208 ∗
       memRegion (sp + 664#64) 616 ∗ memRegion (sp + 1328#64) 80 ∗ F) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm4⟩ := exists_words6_of_memRegion_48 hm3
  rw [show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm4
  have hm5 : s.mem ⊨ memRegion x.ret 48 ∗
      (((sp + 1280#64) ↦₆₄ t0) ∗ words5At (sp + 1288#64) t1 t2 t3 t4 t5 ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ H_spe ∗ ((sp + 400#64) ↦₆₄ errTag) ∗
       ((sp + 408#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 456#64) 208 ∗ memRegion (sp + 664#64) 616 ∗
       memRegion (sp + 1328#64) 80 ∗ F) := by convert hm4 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hm6⟩ := exists_words6_of_memRegion_48 hm5
  refine ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, ?_⟩
  dsimp only [sp] at hm6 ⊢; convert hm6 using 1; sep_ac_rfl

theorem loadRatchet_after_call_error_tight_433_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_434).base + 484#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗
      cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptTightSpecPlaced C A ctl uuidTryParse S) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_tight_433_placed x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  have hm' : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trResultAt A (sp + 400#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
      (cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := hm
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract_433 hnpan hm'
  have hwp := loadRatchet_err_433_wp_placed (H := H)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta_placed hinv_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ speAt A (utf8 "decrypt") x.ret e ∗
    memRegion sp 1408 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
      (memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       ((sp + 400#64) ↦₆₄ errTag) ∗ ((sp + 408#64) ↦₆₄ speTag e) ∗
       words5At (sp + 416#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 456#64) 208 ∗
       memRegion (sp + 664#64) 616 ∗ ((sp + 1280#64) ↦₆₄ speTag e) ∗
       words5At (sp + 1288#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 1328#64) 80) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem loadRatchet_after_call_ok_433_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 400#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 48 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗
      memRegion ((s0.sp - 1504#64) + 664#64) 744 ∗
      cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :
    reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (fun s' => ∃ trG, FindChainStatePlaced (blkPl_434).base A ctl x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A (sp + 400#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗ memRegion sp 48 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744 ∗
    cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R at hm
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A (sp + 400#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨ trAt A (sp + 400#64) trG tr ∗
    (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
     ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
     memRegion (sp + 664#64) 744 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 400#64 + 8#64 = sp + 408#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A trG tr ∗
      (((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗ trBodyAt (sp + 408#64) trG tr ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 408#64) trG tr ∗
      (trHeapAt A trG tr ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 664#64) 744 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 48 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 664#64) 744) ∗
      (words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗ trHeapAt A trG tr ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 g28 g2ac hm_stk2 => ?_
  unfold cliTryDecryptCommonHeapPlaced at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗ trHeapAt A trG tr ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
    memRegion sp 32 ∗ memRegion (sp + 44#64) 4 ∗ memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 664#64) 8 ∗ memRegion (sp + 680#64) 4 ∗ memRegion (sp + 685#64) 595 ∗
    memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
    FromRecordCallees.lsLogOff ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 32#64) ↦₆₄ g20) ∗ ((sp + 40#64) ↦₃₂ g28) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       ((sp + 56#64) ↦₆₄ d_cap) ∗
       words32At (sp + 64#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 672#64) ↦₆₄ g2a0) ∗ ((sp + 684#64) ↦₈ g2ac) ∗
       words4At (sp + 1280#64) t0 t1 t2 t3 ∗ ((sp + 1312#64) ↦₆₄ t4) ∗ ((sp + 1320#64) ↦₆₄ t5) ∗
       ((x.msgA + 104#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢; convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_433_wp_placed (H := H)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    hcap hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx22 hx23 hx25
  have hstep : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
      (fun sf => LibsignalRoLoaded lsmpl sf.mem →
        FindChainStatePlaced (blkPl_434).base A ctl x trG tr st1 R s0 sf) := by
    refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
    intro sf Pf hpcf ⟨b2ac, hPf, hwpInv_f, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hcl_f hmf hro_f
    subst hPf
    refine ⟨hpcf, tryDecryptMidMetaPlaced_of_placed (hwpInv_f.to_midMeta_placed hcl_f) hro_f,
      hx0_f, hx1_f, hx8_f,
      hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
      by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
      hx25_f, hx27_f, hx28_f, ?_⟩
    unfold cliTryDecryptCommonHeapPlaced
    rw [trAt_eq_cap_body_heap, show sp + 56#64 + 8#64 = sp + 64#64 by bv_omega,
        signalMessageAt_eq_counter_rest]
    have hmf_re : sf.mem ⊨
        (words32At (sp + 64#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
           w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
        (memRegion (sp + 320#64) 80 ∗ ((sp + 400#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         words32At (sp + 408#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
           w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
         memRegion (sp + 664#64) 8 ∗ ((sp + 672#64) ↦₆₄ x.remA) ∗ memRegion (sp + 680#64) 4 ∗
         ((sp + 684#64) ↦₈ b2ac) ∗ memRegion (sp + 685#64) 595 ∗
         words4At (sp + 1280#64) w0 w1 w2 w3 ∗ ((sp + 1312#64) ↦₆₄ w4) ∗ ((sp + 1320#64) ↦₆₄ w5) ∗
         memRegion (sp + 1328#64) 80) ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         trHeapAt A trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         ((x.msgA + 104#64) ↦₃₂ x.msg.counter) ∗ signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗
         cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
         stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R) := by
      dsimp only [F_ok, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
    have hmf2 := Satisfies.mono
      (sepConj_mono (hent_tr (sp + 64#64))
        (sepConj_mono_left
          (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
            w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
            w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
    dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl
  exact reaches_pc_mono (reaches_pc_lsro hro hstep) (fun _ _ _ ⟨himpl, hro_f⟩ => ⟨trG, himpl hro_f⟩)

theorem errTail_ok_tight_433_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S parse).1 = .error e)
    (hmod2 : (x.model C S parse).2 = st1)
    (herr : ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_434).rebase (blkPl_434).base H)
      (cliTryDecryptTightSpecPlaced C A ctl parse S) x R s0 s := by
  rcases herr with ⟨hpc, hmeta_full, hx19, hx20, hx26, hmem⟩
  obtain ⟨hmeta, _⟩ := tryDecryptMidMetaPlaced_to_placed hmeta_full
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 56#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 56 ∗
         memRegion (sp + 320#64) 40 ∗ speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
         memRegion (sp + 400#64) 1008 ∗ cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 360#64) e ∗
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 56 ∗
         memRegion (sp + 320#64) 40 ∗ memRegion (sp + 400#64) 1008 ∗
         cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 40 ∗
         memRegion (sp + 400#64) 1008 ∗ cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h320_split :
      memRegion (sp + 320#64) 40 = memRegion (sp + 320#64) 24 ∗ memRegion (sp + 344#64) 16 := by
    rw [show (40 : Nat) = 24 + 16 by decide, memRegion_split (sp + 320#64) 24 16 (by decide),
        show (sp + 320#64) + 24#64 = sp + 344#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 320#64) 24 ∗
        (memRegion (sp + 344#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 80#64) 152 ∗
         ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 56 ∗ memRegion (sp + 400#64) 1008 ∗
         cliTryDecryptCommonHeapPlaced A ctl x draws s0 ∗ R) := by
    rw [h320_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_433_wp_placed (A := A) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold cliTryDecryptCommonHeapPlaced at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 320#64) ↦₆₄ t0) ∗ ((sp + 328#64) ↦₆₄ t1) ∗
         ((sp + 336#64) ↦₆₄ t2) ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 56 ∗
         memRegion (sp + 80#64) 152 ∗ memRegion (sp + 248#64) 72 ∗ memRegion (sp + 344#64) 16 ∗
         memRegion (sp + 400#64) 1008 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗
         FromRecordCallees.lsLogOff ∗ tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S parse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S parse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight_433_placed x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold cliTryDecryptCommonHeapPlaced
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S parse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 56 ∗ ((sp + 56#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 64#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 72#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 80#64) 152 ∗ ((sp + 232#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 240#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 248#64) 72 ∗
          ((sp + 320#64) ↦₆₄ w0) ∗ ((sp + 328#64) ↦₆₄ w1) ∗ ((sp + 336#64) ↦₆₄ w2) ∗
          memRegion (sp + 344#64) 16 ∗ words5At (sp + 360#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 400#64) 1008) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAfter ctl x.cur x.rest draws ∗
          FromRecordCallees.lsLogOff ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

theorem loadRatchet_433_placed_okT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec A)) :
    S1TightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x R s0 s hS1 hcode
  have hro : LibsignalRoLoaded lsmpl s.mem := hS1.2.1.2.2.2.2.2.2.1.2
  have hcall := loadRatchet_call_trFrom_433_reaches_placed htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact P3kR1bc.reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error_tight_433_placed hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segFindChainPC_at (blkPl_434).base) s
        (fun s' => ∃ trG, FindChainStatePlaced (blkPl_434).base A ctl x trG tr st1 R s0 s') := by
      refine reaches_pc_seq (reaches_pc_lsro hro hcall) ?_
      intro s_ret hpc_ret _ ⟨⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩, hro_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok_433_placed hpc_ret hmeta_ret hro_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, trG, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, trG, hS2⟩
    · exact hoom.elim

theorem errTail_433_placed_okT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    ErrTailTightSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl parse S := by
  intro x trG tr st1 e R s0 s he hmod1 hmod2 herr
  exact errTail_ok_tight_433_placed hdealloc x trG tr st1 e R s0 s he hmod1 hmod2 herr

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup
