/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS0Placed
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS1ErrPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookupS2SymPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `ChainLookup` Proof on Block `433`

Proves the relocatable `[LibsignalPlacement]` segment `S2` (`S2SeamPlaced`) for
`try_decrypt_with_state::<Coins>` (block `433`) and re-exports the front-segment seams `S0`, `S1`,
and `ErrTail`.
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

theorem blk433_entry_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

private theorem findChain_err_pre_extract_433 {A : RustAlloc}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {F : SepProp} {s0 s : State}
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 56#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 32 ∗
      (((s0.sp - 1504#64) + 32#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 44#64) 4 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 320#64) 80 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 400#64) (.error e) ∗
      memRegion ((s0.sp - 1504#64) + 440#64) 968 ∗
      F) :
    let sp := s0.sp - 1504#64
    let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
    ∃ (p g0 g1 g2 g3 b0 b1 d0 c0 c1 s1 s2 : BitVec 64)
      (g4 d8c d1_lo d1_hi d2d0 s0_w : BitVec 32),
      e = .invalidSessionStructure .missingReceiverChainKey ∧
      s.mem ⊨
        (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 368#64) ↦₆₄ g1) ∗ ((sp + 376#64) ↦₆₄ g2) ∗
         ((sp + 384#64) ↦₆₄ g3) ∗ ((sp + 392#64) ↦₃₂ g4) ∗ ((sp + 396#64) ↦₃₂ d8c) ∗
         ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ p) ∗ ((sp + 416#64) ↦₆₄ w1) ∗
         ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗ ((sp + 704#64) ↦₆₄ d0) ∗
         ((sp + 712#64) ↦₃₂ d1_lo) ∗ ((sp + 716#64) ↦₃₂ d1_hi) ∗ ((sp + 720#64) ↦₃₂ d2d0) ∗
         ((sp + 816#64) ↦₆₄ c0) ∗ ((sp + 824#64) ↦₆₄ c1) ∗ ((sp + 832#64) ↦₃₂ s0_w) ∗
         ((sp + 836#64) ↦₆₄ s1) ∗ ((sp + 844#64) ↦₆₄ s2)) ∗
        ((p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ memRegion (sp + 404#64) 4 ∗
         memRegion (sp + 424#64) 16 ∗ memRegion (sp + 440#64) 248 ∗
         memRegion (sp + 724#64) 92 ∗ memRegion (sp + 852#64) 556 ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
         memRegion x.ret 48 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 40 ∗
         F) := by
  dsimp only
  let sp := s0.sp - 1504#64
  have hm_frck : s.mem ⊨ findReceiverChainKeyResultAt (sp + 400#64) (.error e) ∗
      ((memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗ ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
        memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion (sp + 320#64) 80 ∗ memRegion (sp + 440#64) 968 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨he, hm_err⟩ := findReceiverChainKeyResultAt_error_eq hm_frck
  subst he
  have hm_sp56 := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (findChain_err_stack_recombine_sp38 sp x.locA x.remA x.msg.counter)))
    hm_err
  unfold strRefAt at hm_sp56
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_sp56
  have hm_ex : s.mem ⊨
      (∃∗ p : BitVec 64,
        ((sp + 408#64) ↦₆₄ p) ∗
        ((sp + 416#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length) ∗
        (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey)) ∗
      (((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗ memRegion (sp + 424#64) 16 ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 440#64) 968 ∗ F) := by
    convert hm_sp56 using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨p, hm_p⟩
  rw [memRegion_split (sp + 320#64) 40 40 (by decide),
      show (sp + 320#64) + BitVec.ofNat 64 40 = sp + 360#64 by bv_omega,
      memRegion_split (sp + 360#64) 16 24 (by decide),
      show (sp + 360#64) + 16#64 = sp + 376#64 by bv_omega,
      memRegion_split (sp + 376#64) 16 8 (by decide),
      show (sp + 376#64) + 16#64 = sp + 392#64 by bv_omega,
      memRegion_split (sp + 392#64) 4 4 (by decide),
      show (sp + 392#64) + 4#64 = sp + 396#64 by bv_omega,
      memRegion_split (sp + 440#64) 248 720 (by decide),
      show (sp + 440#64) + BitVec.ofNat 64 248 = sp + 688#64 by bv_omega,
      memRegion_split (sp + 688#64) 16 704 (by decide),
      show (sp + 688#64) + 16#64 = sp + 704#64 by bv_omega,
      memRegion_split (sp + 704#64) 8 696 (by decide),
      show (sp + 704#64) + 8#64 = sp + 712#64 by bv_omega,
      memRegion_split (sp + 712#64) 4 692 (by decide),
      show (sp + 712#64) + 4#64 = sp + 716#64 by bv_omega,
      memRegion_split (sp + 716#64) 4 688 (by decide),
      show (sp + 716#64) + 4#64 = sp + 720#64 by bv_omega,
      memRegion_split (sp + 720#64) 4 684 (by decide),
      show (sp + 720#64) + 4#64 = sp + 724#64 by bv_omega,
      memRegion_split (sp + 724#64) 92 592 (by decide),
      show (sp + 724#64) + BitVec.ofNat 64 92 = sp + 816#64 by bv_omega,
      memRegion_split (sp + 816#64) 16 576 (by decide),
      show (sp + 816#64) + 16#64 = sp + 832#64 by bv_omega,
      memRegion_split (sp + 832#64) 20 556 (by decide),
      show (sp + 832#64) + 20#64 = sp + 852#64 by bv_omega] at hm_p
  let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
  let F_err_base :=
    (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗
    ((sp + 400#64) ↦₃₂ 2#32) ∗ ((sp + 408#64) ↦₆₄ p) ∗ ((sp + 416#64) ↦₆₄ w1) ∗
    memRegion (sp + 404#64) 4 ∗ memRegion (sp + 424#64) 16 ∗ memRegion (sp + 440#64) 248 ∗
    memRegion (sp + 724#64) 92 ∗ memRegion (sp + 852#64) 556 ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 40 ∗ F
  have hm1 : s.mem ⊨ memRegion (sp + 360#64) 16 ∗
      (memRegion (sp + 376#64) 16 ∗ memRegion (sp + 392#64) 4 ∗ memRegion (sp + 396#64) 4 ∗
       memRegion (sp + 688#64) 16 ∗ memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 4 ∗
       memRegion (sp + 716#64) 4 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗
       memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    dsimp only [F_err_base, w1]; convert hm_p using 1; sep_ac_rfl
  obtain ⟨g0, g1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  have hm3 : s.mem ⊨ memRegion (sp + 376#64) 16 ∗
      ((((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 392#64) 4 ∗ memRegion (sp + 396#64) 4 ∗ memRegion (sp + 688#64) 16 ∗
       memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 4 ∗ memRegion (sp + 716#64) 4 ∗
       memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨g2, g3, hm4⟩ := exists_words16_of_memRegion_16 hm3
  have hm5 : s.mem ⊨ memRegion (sp + 392#64) 4 ∗
      ((((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 396#64) 4 ∗ memRegion (sp + 688#64) 16 ∗ memRegion (sp + 704#64) 8 ∗
       memRegion (sp + 712#64) 4 ∗ memRegion (sp + 716#64) 4 ∗ memRegion (sp + 720#64) 4 ∗
       memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨g4, hm6⟩ := exists_word32_of_memRegion_4 hm5
  have hm7 : s.mem ⊨ memRegion (sp + 396#64) 4 ∗
      (((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 688#64) 16 ∗ memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 4 ∗
       memRegion (sp + 716#64) 4 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗
       memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm6 using 1; sep_ac_rfl
  obtain ⟨d8c, hm8⟩ := exists_word32_of_memRegion_4 hm7
  have hm9 : s.mem ⊨ memRegion (sp + 688#64) 16 ∗
      (((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 704#64) 8 ∗ memRegion (sp + 712#64) 4 ∗ memRegion (sp + 716#64) 4 ∗
       memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm8 using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm10⟩ := exists_words16_of_memRegion_16 hm9
  have hm11 : s.mem ⊨ memRegion (sp + 704#64) 8 ∗
      ((((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 712#64) 4 ∗ memRegion (sp + 716#64) 4 ∗ memRegion (sp + 720#64) 4 ∗
       memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm10 using 1; sep_ac_rfl
  obtain ⟨d0, hm12⟩ := exists_word64_of_memRegion_8 hm11
  have hm13 : s.mem ⊨ memRegion (sp + 712#64) 4 ∗
      (((sp + 704#64) ↦₆₄ d0) ∗ (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 716#64) 4 ∗ memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗
       memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm12 using 1; sep_ac_rfl
  obtain ⟨d1_lo, hm14⟩ := exists_word32_of_memRegion_4 hm13
  have hm15 : s.mem ⊨ memRegion (sp + 716#64) 4 ∗
      (((sp + 712#64) ↦₃₂ d1_lo) ∗ ((sp + 704#64) ↦₆₄ d0) ∗
       (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 720#64) 4 ∗ memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm14 using 1; sep_ac_rfl
  obtain ⟨d1_hi, hm16⟩ := exists_word32_of_memRegion_4 hm15
  have hm17 : s.mem ⊨ memRegion (sp + 720#64) 4 ∗
      (((sp + 716#64) ↦₃₂ d1_hi) ∗ ((sp + 712#64) ↦₃₂ d1_lo) ∗ ((sp + 704#64) ↦₆₄ d0) ∗
       (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 816#64) 16 ∗ memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm16 using 1; sep_ac_rfl
  obtain ⟨d2d0, hm18⟩ := exists_word32_of_memRegion_4 hm17
  have hm19 : s.mem ⊨ memRegion (sp + 816#64) 16 ∗
      (((sp + 720#64) ↦₃₂ d2d0) ∗ ((sp + 716#64) ↦₃₂ d1_hi) ∗ ((sp + 712#64) ↦₃₂ d1_lo) ∗
       ((sp + 704#64) ↦₆₄ d0) ∗ (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗
       memRegion (sp + 832#64) 20 ∗ F_err_base) := by
    convert hm18 using 1; sep_ac_rfl
  obtain ⟨c0, c1, hm20⟩ := exists_words16_of_memRegion_16 hm19
  have hm21 : s.mem ⊨ memRegion (sp + 832#64) 20 ∗
      ((((sp + 816#64) ↦₆₄ c0) ∗ ((sp + 816#64 + 8#64) ↦₆₄ c1)) ∗
       ((sp + 720#64) ↦₃₂ d2d0) ∗ ((sp + 716#64) ↦₃₂ d1_hi) ∗ ((sp + 712#64) ↦₃₂ d1_lo) ∗
       ((sp + 704#64) ↦₆₄ d0) ∗ (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 688#64 + 8#64) ↦₆₄ b1)) ∗
       ((sp + 396#64) ↦₃₂ d8c) ∗ ((sp + 392#64) ↦₃₂ g4) ∗
       (((sp + 376#64) ↦₆₄ g2) ∗ ((sp + 376#64 + 8#64) ↦₆₄ g3)) ∗
       (((sp + 360#64) ↦₆₄ g0) ∗ ((sp + 360#64 + 8#64) ↦₆₄ g1)) ∗ F_err_base) := by
    convert hm20 using 1; sep_ac_rfl
  obtain ⟨s0_w, s1, s2, hm22⟩ := exists_words20_of_memRegion_20 hm21
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm22
  refine ⟨p, g0, g1, g2, g3, b0, b1, d0, c0, c1, s1, s2, g4, d8c, d1_lo, d1_hi, d2d0, s0_w, rfl, ?_⟩
  dsimp only [F_err_base, w1, sp] at hm22 ⊢
  convert hm22 using 1; sep_ac_rfl

theorem findChain_after_call_ok_none_433_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 56#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 56#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 32 ∗
      (((s0.sp - 1504#64) + 32#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 44#64) 4 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 320#64) 80 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 400#64) (.ok none) ∗
      memRegion ((s0.sp - 1504#64) + 440#64) 968 ∗
      cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :
    reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segDhStepPC_at (blkPl_434).base) s
      (DhStepStatePlaced (blkPl_434).base A ctl x trG tr st1 R s0) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
    (((sp + 400#64) ↦₃₂ 0#32) ∗ memRegion (sp + 400#64 + 4#64) 36) ∗
    memRegion (sp + 440#64) 968 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R at hm
  rw [show sp + 400#64 + 4#64 = sp + 404#64 by bv_omega,
      memRegion_split (sp + 440#64) 456 512 (by decide),
      show (sp + 440#64) + BitVec.ofNat 64 456 = sp + 896#64 by bv_omega,
      memRegion_split (sp + 896#64) 16 496 (by decide),
      show (sp + 896#64) + 16#64 = sp + 912#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 404#64) 36 ∗
      (memRegion (sp + 896#64) 16 ∗ ((sp + 400#64) ↦₃₂ 0#32) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 440#64) 456 ∗ memRegion (sp + 912#64) 496 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, hm2⟩ := exists_words36_of_memRegion_36 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 896#64) 16 ∗
      ((((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
        ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
       ((sp + 400#64) ↦₃₂ 0#32) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       trAt A (sp + 56#64) trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 32 ∗
       ((sp + 32#64) ↦₆₄ x.locA) ∗ ((sp + 40#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 44#64) 4 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 80 ∗ memRegion (sp + 440#64) 456 ∗
       memRegion (sp + 912#64) 496 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm4⟩ := exists_words16_of_memRegion_16 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  let F_none :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 440#64) 456 ∗ memRegion (sp + 912#64) 496 ∗
    cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 400#64) ↦₃₂ 0#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗
       ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
       ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
       ((sp + 896#64) ↦₆₄ d0) ∗ ((sp + 904#64) ↦₆₄ d1)) ∗ F_none := by
    dsimp only [F_none]; convert hm4 using 1; sep_ac_rfl
  have hwp := findChain_ok_none_full_433_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  have hstep : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segDhStepPC_at (blkPl_434).base) s
      (fun sf => LibsignalRoLoaded lsmpl sf.mem →
        DhStepStatePlaced (blkPl_434).base A ctl x trG tr st1 R s0 sf) := by
    refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
    intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hcl_f hmf hro_f
    subst hPf
    refine ⟨hpcf, tryDecryptMidMetaPlaced_of_placed (hwpInv_f.to_midMeta_placed hcl_f) hro_f, hx12_f,
      (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
      (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
      by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
      (hcs.2.2.2.2.2.2.1).trans hx25, (hcs.2.2.2.2.2.2.2.2.1).trans hx27,
      (hcs.2.2.2.2.2.2.2.2.2.1).trans hx28, ?_⟩
    have hmf_re : sf.mem ⊨
        (memRegion (sp + 320#64) 80 ∗ ((sp + 400#64) ↦₃₂ 0#32) ∗
         (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗
          ((sp + 416#64) ↦₆₄ w2) ∗ ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
         memRegion (sp + 440#64) 456 ∗
         (((sp + 896#64) ↦₆₄ w3) ∗ ((sp + 904#64) ↦₆₄ w4)) ∗
         memRegion (sp + 912#64) 496) ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
         memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
         ((sp + 48#64) ↦₆₄ x.remA) ∗
         cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
      dsimp only [F_none, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
    have hmf2 := Satisfies.mono (sepConj_mono_left (findChain_none_stack_recombine sp w0 w1 w2 w3 w4)) hmf_re
    dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl
  exact reaches_pc_mono (reaches_pc_lsro_preserve hro hstep) (fun _ _ _ ⟨himpl, hro_f⟩ => himpl hro_f)

theorem findChain_after_call_ok_some_433_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hx28 : s.readReg64 .x28 = (s0.sp - 1504#64) + 704#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 56#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 32 ∗
      (((s0.sp - 1504#64) + 32#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 44#64) 4 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 320#64) 80 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 400#64) (.ok (some ck)) ∗
      memRegion ((s0.sp - 1504#64) + 440#64) 968 ∗
      cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :
    reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segConsumeMsgKeyPC_at (blkPl_434).base) s
      (ConsumeMsgKeyStatePlaced (blkPl_434).base A ctl x trG tr st1 ck 0 R s0) := by
  let sp := s0.sp - 1504#64
  have htake_len : ((chainKeyBytes ck).take 20).length = 20 := by
    rw [List.length_take_of_le (by rw [chainKeyBytes_length]; decide)]
  have hdrop_len : ((chainKeyBytes ck).drop 20).length = 16 := by
    rw [List.length_drop, chainKeyBytes_length]
  obtain ⟨w0, w1, w2, hw20⟩ := exists_words20_of_length_20 htake_len
  obtain ⟨w3, w4, hw16⟩ := exists_words16_of_length_16 hdrop_len
  have hck_split :
      ((sp + 400#64 + 4#64) ↦ₛ chainKeyBytes ck) =
        (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2)) ∗
        (((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) := by
    rw [show sp + 400#64 + 4#64 = sp + 404#64 by bv_omega,
        ← List.take_append_drop 20 (chainKeyBytes ck), pointsToBytes_append, htake_len,
        show (sp + 404#64) + BitVec.ofNat 64 20 = sp + 424#64 by bv_omega,
        hw20 (sp + 404#64), hw16 (sp + 424#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
    (((sp + 400#64) ↦₃₂ 1#32) ∗ ((sp + 400#64 + 4#64) ↦ₛ chainKeyBytes ck)) ∗
    memRegion (sp + 440#64) 968 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R at hm
  rw [hck_split,
      memRegion_split (sp + 440#64) 248 720 (by decide),
      show (sp + 440#64) + BitVec.ofNat 64 248 = sp + 688#64 by bv_omega,
      memRegion_split (sp + 688#64) 16 704 (by decide),
      show (sp + 688#64) + 16#64 = sp + 704#64 by bv_omega,
      memRegion_split (sp + 704#64) 20 684 (by decide),
      show (sp + 704#64) + 20#64 = sp + 724#64 by bv_omega,
      memRegion_split (sp + 724#64) 172 512 (by decide),
      show (sp + 724#64) + BitVec.ofNat 64 172 = sp + 896#64 by bv_omega,
      memRegion_split (sp + 896#64) 16 496 (by decide),
      show (sp + 896#64) + 16#64 = sp + 912#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ memRegion (sp + 688#64) 16 ∗
      (memRegion (sp + 704#64) 20 ∗ memRegion (sp + 896#64) 16 ∗ ((sp + 400#64) ↦₃₂ 1#32) ∗
       (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2)) ∗
       (((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 440#64) 248 ∗ memRegion (sp + 724#64) 172 ∗
       memRegion (sp + 912#64) 496 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨b0, b1, hm2⟩ := exists_words16_of_memRegion_16 hm1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
  have hm3 : s.mem ⊨ memRegion (sp + 704#64) 20 ∗
      ((((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1)) ∗
       memRegion (sp + 896#64) 16 ∗ ((sp + 400#64) ↦₃₂ 1#32) ∗
       (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2)) ∗
       (((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 440#64) 248 ∗ memRegion (sp + 724#64) 172 ∗
       memRegion (sp + 912#64) 496 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨c0, c1, c2, hm4⟩ := exists_words20_of_memRegion_20 hm3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm4
  have hm5 : s.mem ⊨ memRegion (sp + 896#64) 16 ∗
      ((((sp + 704#64) ↦₃₂ c0) ∗ ((sp + 708#64) ↦₆₄ c1) ∗ ((sp + 716#64) ↦₆₄ c2)) ∗
       (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1)) ∗
       ((sp + 400#64) ↦₃₂ 1#32) ∗
       (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2)) ∗
       (((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
       memRegion (sp + 440#64) 248 ∗ memRegion (sp + 724#64) 172 ∗
       memRegion (sp + 912#64) 496 ∗
       cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨d0, d1, hm6⟩ := exists_words16_of_memRegion_16 hm5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm6
  let F_some :=
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
    memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
    ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 320#64) 80 ∗
    memRegion (sp + 440#64) 248 ∗ memRegion (sp + 724#64) 172 ∗
    memRegion (sp + 912#64) 496 ∗ cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 400#64) ↦₃₂ 1#32) ∗ ((sp + 404#64) ↦₃₂ w0) ∗
       ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
       ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4) ∗
       ((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1) ∗
       ((sp + 704#64) ↦₃₂ c0) ∗ ((sp + 708#64) ↦₆₄ c1) ∗
       ((sp + 716#64) ↦₆₄ c2) ∗ ((sp + 896#64) ↦₆₄ d0) ∗
       ((sp + 904#64) ↦₆₄ d1)) ∗ F_some := by
    dsimp only [F_some]; convert hm6 using 1; sep_ac_rfl
  have hwp := findChain_ok_some_full_433_wp_placed (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (b0 := b0) (b1 := b1) (c0 := c0) (c1 := c1) (c2 := c2) (d0 := d0) (d1 := d1)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx25 hx28
  have hstep : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (segConsumeMsgKeyPC_at (blkPl_434).base) s
      (fun sf => LibsignalRoLoaded lsmpl sf.mem →
        ConsumeMsgKeyStatePlaced (blkPl_434).base A ctl x trG tr st1 ck 0 R s0 sf) := by
    refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
    intro sf Pf hpcf ⟨hPf, hwpInv_f, hx12_f, hcs⟩ hcl_f hmf hro_f
    subst hPf
    refine ⟨hpcf, tryDecryptMidMetaPlaced_of_placed (hwpInv_f.to_midMeta_placed hcl_f) hro_f, hx12_f,
      (hcs.1).trans hx19, (hcs.2.1).trans hx20, (hcs.2.2.1).trans hx21,
      (hcs.2.2.2.1).trans hx22, (hcs.2.2.2.2.1).trans hx23,
      by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hcs.2.2.2.2.2.1]; exact hx24,
      (hcs.2.2.2.2.2.2.1).trans hx25, ?_⟩
    have h688 : (((sp + 688#64) ↦₆₄ w3) ∗ ((sp + 696#64) ↦₆₄ w4)) =
        ((sp + 688#64) ↦ₛ (chainKeyBytes ck).drop 20) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw16 (sp + 688#64)).symm
    have h704 : (((sp + 704#64) ↦₃₂ w0) ∗ ((sp + 708#64) ↦₆₄ w1) ∗ ((sp + 716#64) ↦₆₄ w2)) =
        ((sp + 704#64) ↦ₛ (chainKeyBytes ck).take 20) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using (hw20 (sp + 704#64)).symm
    have hmf_re : sf.mem ⊨
        (memRegion (sp + 320#64) 80 ∗ ((sp + 400#64) ↦₃₂ 1#32) ∗
         (((sp + 404#64) ↦₃₂ w0) ∗ ((sp + 408#64) ↦₆₄ w1) ∗ ((sp + 416#64) ↦₆₄ w2) ∗
          ((sp + 424#64) ↦₆₄ w3) ∗ ((sp + 432#64) ↦₆₄ w4)) ∗
         memRegion (sp + 440#64) 248) ∗
        (memRegion (sp + 724#64) 172 ∗
         (((sp + 896#64) ↦₆₄ w3) ∗ ((sp + 904#64) ↦₆₄ w4)) ∗
         memRegion (sp + 912#64) 496) ∗
        (((sp + 688#64) ↦₆₄ w3) ∗ ((sp + 696#64) ↦₆₄ w4)) ∗
        (((sp + 704#64) ↦₃₂ w0) ∗ ((sp + 708#64) ↦₆₄ w1) ∗ ((sp + 716#64) ↦₆₄ w2)) ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
         memRegion x.ret 48 ∗ memRegion sp 32 ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 44#64) 4 ∗
         ((sp + 48#64) ↦₆₄ x.remA) ∗
         cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
      dsimp only [F_some, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
    rw [h688, h704] at hmf_re
    have hmf2 := Satisfies.mono
      (sepConj_mono (findChain_some_stack_recombine_left sp w0 w1 w2 w3 w4)
        (sepConj_mono_left (findChain_some_stack_recombine_right sp w3 w4))) hmf_re
    dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl
  exact reaches_pc_mono (reaches_pc_lsro_preserve hro hstep) (fun _ _ _ ⟨himpl, hro_f⟩ => himpl hro_f)

theorem findChain_after_call_error_433_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_434).base + 680#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 400#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trAt A ((s0.sp - 1504#64) + 56#64) trG tr ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 32 ∗
      (((s0.sp - 1504#64) + 32#64) ↦₆₄ x.locA) ∗
      (((s0.sp - 1504#64) + 40#64) ↦₃₂ x.msg.counter) ∗
      memRegion ((s0.sp - 1504#64) + 44#64) 4 ∗
      (((s0.sp - 1504#64) + 48#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 320#64) 80 ∗
      findReceiverChainKeyResultAt ((s0.sp - 1504#64) + 400#64) (.error e) ∗
      memRegion ((s0.sp - 1504#64) + 440#64) 968 ∗
      cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) :
    reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (errTailPC_at (blkPl_434).base) s
      (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 e 0 R s0) := by
  let sp := s0.sp - 1504#64
  let w1 := BitVec.ofNat 64 (invalidSessionStructureStr .missingReceiverChainKey).length
  obtain ⟨p, g0, g1, g2, g3, b0, b1, d0, c0, c1, s1, s2, g4, d8c, d1_lo, d1_hi, d2d0, s0_w, he, hm_pre⟩ :=
    findChain_err_pre_extract_433 hm
  subst he
  have hwp := findChain_err_433_wp_placed (H := H)
    (w0 := p) (w1 := w1) (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3)
    (b0 := b0) (b1 := b1) (d0 := d0) (c0 := c0) (c1 := c1) (s1 := s1) (s2 := s2)
    (g4 := g4) (d8c := d8c) (d1_lo := d1_lo) (d1_hi := d1_hi) (d2d0 := d2d0) (s0_w := s0_w)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx25
  have hstep : reaches_pc ((blkPC_434).rebase (blkPl_434).base H) (errTailPC_at (blkPl_434).base) s
      (fun sf => LibsignalRoLoaded lsmpl sf.mem →
        ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1
          (.invalidSessionStructure .missingReceiverChainKey) 0 R s0 sf) := by
    refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
    intro sf Pf hpcf ⟨hPf, hwpInv_f, hx19_f, hx20_f, hx26_f⟩ hcl_f hmf hro_f
    subst hPf
    refine ⟨hpcf, tryDecryptMidMetaPlaced_of_placed (hwpInv_f.to_midMeta_placed hcl_f) hro_f,
      hx19_f.trans hx19, hx20_f.trans hx20, hx26_f, ?_⟩
    let u0 := b0.extractLsb' 0 32 ++ d2d0
    let u1 := b1.extractLsb' 0 32 ++ b0.extractLsb' 32 32
    let u2 := b1.extractLsb' 32 32
    have hmf_re : sf.mem ⊨
        (((sp + 360#64) ↦₆₄ p) ∗ ((sp + 368#64) ↦₆₄ w1) ∗
         (p ↦ᵣ invalidSessionStructureStr .missingReceiverChainKey) ∗ ((sp + 376#64) ↦₆₄ u0) ∗
         ((sp + 384#64) ↦₆₄ u1) ∗ ((sp + 392#64) ↦₃₂ u2) ∗ ((sp + 396#64) ↦₃₂ 24#32)) ∗
        (((sp + 400#64) ↦₃₂ 2#32) ∗ memRegion (sp + 404#64) 4 ∗
         (((sp + 408#64) ↦₆₄ p) ∗ ((sp + 416#64) ↦₆₄ w1)) ∗
         memRegion (sp + 424#64) 16 ∗ memRegion (sp + 440#64) 248 ∗
         (((sp + 688#64) ↦₆₄ b0) ∗ ((sp + 696#64) ↦₆₄ b1)) ∗
         (((sp + 704#64) ↦₆₄ p) ∗ ((sp + 712#64) ↦₆₄ w1)) ∗
         ((sp + 720#64) ↦₃₂ d2d0) ∗ memRegion (sp + 724#64) 92 ∗
         (((sp + 816#64) ↦₆₄ p) ∗ ((sp + 824#64) ↦₆₄ w1)) ∗
         (((sp + 832#64) ↦₆₄ u0) ∗ ((sp + 840#64) ↦₆₄ u1)) ∗
         ((sp + 848#64) ↦₃₂ u2) ∗ memRegion (sp + 852#64) 556) ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
         memRegion x.ret 48 ∗ memRegion sp 56 ∗ memRegion (sp + 320#64) 40 ∗
         cliTryDecryptCommonHeapPlaced A ctl x 0 s0 ∗ R) := by
      dsimp only [u0, u1, u2, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
    have hmf2 := Satisfies.mono
      (sepConj_mono (findChain_err_speBody_entails A sp p u0 u1 u2)
        (sepConj_mono_left (findChain_err_stack_recombine_0x190 sp p w1 b0 b1 u0 u1 d2d0 u2))) hmf_re
    dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl
  exact reaches_pc_mono (reaches_pc_lsro_preserve hro hstep) (fun _ _ _ ⟨himpl, hro_f⟩ => himpl hro_f)

theorem findChain_433_placed_ok [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {H : String → Option (State → State)}
    (hfrck : subroutine_ok ((blkPC_25).rebase (blkPl_25).base H) (blkPl_25).base
      (withLsCodeLoaded lsmpl (findReceiverChainKeyPlacedSpec A))) :
    S2SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base A ctl := by
  intro x trG tr st1 R s0 s hs2P _hcode
  have hcall := findChain_call_findReceiverChainKey_433_reaches_placed hfrck x trG tr st1 R s0 s hs2P
  cases hres : tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | ok optCk =>
    cases optCk with
    | some ck =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hro_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, _, hx28_ret, hm_ret⟩ => ?_)
      exact findChain_after_call_ok_some_433_placed hpc_ret hmeta_ret hro_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx28_ret hm_ret
    | none =>
      rw [hres] at hcall
      refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hro_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hx27_ret, hx28_ret, hm_ret⟩ => ?_)
      exact findChain_after_call_ok_none_433_placed hpc_ret hmeta_ret hro_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hx27_ret hx28_ret hm_ret
  | error e =>
    rw [hres] at hcall
    refine reaches_pc_seq hcall (fun s_ret hpc_ret _ ⟨hmeta_ret, hro_ret, hx19_ret, hx20_ret, _, _, _, _, hx25_ret, _, _, hm_ret⟩ => ?_)
    exact findChain_after_call_error_433_placed hpc_ret hmeta_ret hro_ret hx19_ret hx20_ret hx25_ret hm_ret

end CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup
