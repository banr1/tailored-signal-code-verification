/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitPack
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` S3 Commit Receiver-Chain Eviction Loop

Proves sub-segment 4 (`dhCommit_step4`, `+0xaf0 → +0xb98`), evicting oldest receiver chains via
`Vec::remove(0)` (`memmove` and `drop_glue<Chain>`) while `6 ≤ gcs.length`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DhCommitFacts

end DhCommitFacts

/-- Single iteration of the eviction loop (`+0xb04 → +0xb8c`) for `gc₀ :: gcs` with `gcs.length < 2 ^ 32`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_evict_one (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hDrop : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gc₀ : ChainGhost × ReceiverChain) (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb04#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64)
    (hx24 : s.readReg64 .x24 = sp + 0x190#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx27 : s.readReg64 .x27 = 0xffffffffffffff98#64)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (gc₀ :: gcs).length)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActive A sp chainsCap chainsPtr (gc₀ :: gcs) ∗ (Frame ∗ R)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb8c#64 ∧
      sf.status = .Running ∧
      sf.sp = sp ∧
      sf.spAligned = true ∧
      sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧
      sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧
      sf.readReg64 .x24 = sp + 0x190#64 ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧
      sf.readReg64 .x27 = 0xffffffffffffff98#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
      (sf.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R))) := by
  unfold evictActive at hmem
  have hexp := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (vecBuf_chainAt_expose_for_remove0 A chainsCap chainsPtr gc₀ gcs)))))
    hmem
  have hexp_pull :
      s.mem ⊨
        (∃∗ pad₀ : List (BitVec 8), ∃∗ bs_rest : List (BitVec 8),
          ⌜pad₀.length = optChainKeyPadLen gc₀.2.chainKey ∧
            ChainArrayBytes gcs bs_rest ∧ bs_rest.length = gcs.length * 104 ∧
            gcs.length + 1 ≤ chainsCap.toNat ∧ chainsCap.toNat * 104 < 2 ^ 63 ∧
            chainsPtr ≠ 0 ∧ chainsCap ≠ 0⌝ ∗
          A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
          ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A gc₀ ∗
          chainHeaps A gcs) ∗
        (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         memRegion (sp + 0x500#64) 96 ∗
         A.pool ∗
         stackAt sp dropChainStack ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hexp
    ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull
  rcases hexp_pull with ⟨pad₀, hexp_pull⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hexp_pull
  rcases hexp_pull with ⟨bs_rest, hexp_pull⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hexp_pull
  rcases hexp_pull with ⟨⟨hpad₀, hrest, hbs_len, hcap_le, hcap_lt, hptr, _hcap_ne⟩, hm0⟩
  have hsrk_pull :
      s.mem ⊨ chainHeap A gc₀ ∗
        (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         (chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
         ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
         memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
           ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
         chainHeaps A gcs ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         memRegion (sp + 0x500#64) 96 ∗
         A.pool ∗
         stackAt sp dropChainStack ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm0
    ac_rfl
  have hsrk_ne_mem := Satisfies.mono (sepConj_mono_left (chainHeap_srk_cap_ne_zero A gc₀)) hsrk_pull
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsrk_ne_mem
  rcases hsrk_ne_mem with ⟨hc0_ne, hm1⟩
  have hm500_front :
      s.mem ⊨ memRegion (sp + 0x500#64) 96 ∗
        ((chainsPtr ↦ₛ chainBytes gc₀ pad₀) ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         memRegion (sp + 0x190#64) 104 ∗
         A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
         ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
         memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
           ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
         chainHeap A gc₀ ∗
         chainHeaps A gcs ∗
         A.pool ∗
         stackAt sp dropChainStack ∗
         (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    ac_rfl
  obtain ⟨s500, s508, s510, s518, s520, s528, s530, s538, s540, s548, s550, s558, hm2⟩ :=
    elim_memRegion_96 hm500_front
  set tail₀ := optChainKeyTailBytes gc₀.1.ck gc₀.2.chainKey pad₀
  set c0 := gc₀.1.srk.cap
  set c1 := gc₀.1.srk.ptr
  set c2 := BitVec.ofNat 64 gc₀.1.srk.bytes.length
  set c3 := gc₀.1.priv.cap
  set c4 := gc₀.1.priv.ptr
  set c5 := BitVec.ofNat 64 gc₀.1.priv.bytes.length
  set c6 := gc₀.1.mkCap
  set c7 := gc₀.1.mkPtr
  set c8 := BitVec.ofNat 64 (gc₀.1.keys.zip gc₀.2.messageKeys).length
  set c9 := pack64 (tail₀.take 8)
  set c10 := pack64 ((tail₀.drop 8).take 8)
  set c11 := pack64 ((tail₀.drop 16).take 8)
  set c12 := pack64 (tail₀.drop 24)
  have hcells_ptr : (chainsPtr ↦ₛ chainBytes gc₀ pad₀) =
      (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
      ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
      ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
      ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
      ((chainsPtr + 96#64) ↦₆₄ c12) :=
    pointsToBytes_chainBytes_eq_13_cells chainsPtr gc₀ hpad₀
  have hm_pre_wp :
      s.mem ⊨
        (((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         (chainsPtr ↦₆₄ c0) ∗ ((chainsPtr + 8#64) ↦₆₄ c1) ∗ ((chainsPtr + 16#64) ↦₆₄ c2) ∗
         ((chainsPtr + 24#64) ↦₆₄ c3) ∗ ((chainsPtr + 32#64) ↦₆₄ c4) ∗ ((chainsPtr + 40#64) ↦₆₄ c5) ∗
         ((chainsPtr + 48#64) ↦₆₄ c6) ∗ ((chainsPtr + 56#64) ↦₆₄ c7) ∗ ((chainsPtr + 64#64) ↦₆₄ c8) ∗
         ((chainsPtr + 72#64) ↦₆₄ c9) ∗ ((chainsPtr + 80#64) ↦₆₄ c10) ∗ ((chainsPtr + 88#64) ↦₆₄ c11) ∗
         ((chainsPtr + 96#64) ↦₆₄ c12) ∗
         ((sp + 0x500#64) ↦₆₄ s500) ∗ ((sp + 0x508#64) ↦₆₄ s508) ∗ ((sp + 0x510#64) ↦₆₄ s510) ∗
         ((sp + 0x518#64) ↦₆₄ s518) ∗ ((sp + 0x520#64) ↦₆₄ s520) ∗ ((sp + 0x528#64) ↦₆₄ s528) ∗
         ((sp + 0x530#64) ↦₆₄ s530) ∗ ((sp + 0x538#64) ↦₆₄ s538) ∗ ((sp + 0x540#64) ↦₆₄ s540) ∗
         ((sp + 0x548#64) ↦₆₄ s548) ∗ ((sp + 0x550#64) ↦₆₄ s550) ∗ ((sp + 0x558#64) ↦₆₄ s558)) ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
          memRegion (sp + 0x190#64) 104 ∗
          A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          ((chainsPtr + 104#64) ↦ₛ bs_rest) ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A gc₀ ∗
          chainHeaps A gcs ∗
          A.pool ∗
          stackAt sp dropChainStack ∗
          Frame) ∗ R) := by
    rw [hcells_ptr] at hm2
    have e1 := add_assoc_const sp 0x500#64 8#64 0x508#64
    have e2 := add_assoc_const sp 0x500#64 16#64 0x510#64
    have e3 := add_assoc_const sp 0x500#64 24#64 0x518#64
    have e4 := add_assoc_const sp 0x500#64 32#64 0x520#64
    have e5 := add_assoc_const sp 0x500#64 40#64 0x528#64
    have e6 := add_assoc_const sp 0x500#64 48#64 0x530#64
    have e7 := add_assoc_const sp 0x500#64 56#64 0x538#64
    have e8 := add_assoc_const sp 0x500#64 64#64 0x540#64
    have e9 := add_assoc_const sp 0x500#64 72#64 0x548#64
    have e10 := add_assoc_const sp 0x500#64 80#64 0x550#64
    have e11 := add_assoc_const sp 0x500#64 88#64 0x558#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at hm2
    refine Satisfies.mono (Entails.of_eq ?_) hm2
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4b_pre_memmove_wp img.base ext sp chainsPtr
      (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s500 s508 s510 s518 s520 s528 s530 s538 s540 s548 s550 s558
      s hpc hrun hsp hsp_align hx23 hx24 hx25 hx27 hx28)
    hm_pre_wp hL ?_
  intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm_s1 hpost1
  rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx1_1, hx2_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
  have hm_s1' := Satisfies.mono (sepConj_mono_left hP1) hm_s1
  set b₀ := chainBytes gc₀ pad₀
  have hb₀_len : b₀.length = 104 := chainBytes_length gc₀ hpad₀
  have hcomb_bytes : (chainsPtr ↦ₛ (b₀ ++ bs_rest)) =
      (chainsPtr ↦ₛ b₀) ∗ ((chainsPtr + 104#64) ↦ₛ bs_rest) := by
    rw [pointsToBytes_append, hb₀_len]
  have hx2_toNat : (s1.readReg64 .x2).toNat = gcs.length * 104 := by
    rw [hx2_1, List.length_cons]
    exact memmove_len_toNat hlen_lt
  have hm_memmove :
      s1.mem ⊨
        (sessionMemmoveSpec dropChainStack).pre (chainsPtr, b₀ ++ bs_rest, 0, 104, gcs.length * 104) s1 ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
          memRegion (sp + 0x190#64) 104 ∗
          ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
          ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
          ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
          ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
          A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
          memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
            ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
          chainHeap A gc₀ ∗
          chainHeaps A gcs ∗
          A.pool ∗
          Frame) ∗ R) := by
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec]
    have hpre_pure :
        s1.readReg64 .x0 = chainsPtr + BitVec.ofNat 64 0 ∧
        s1.readReg64 .x1 = chainsPtr + BitVec.ofNat 64 104 ∧
        (s1.readReg64 .x2).toNat = gcs.length * 104 ∧
        0 + gcs.length * 104 ≤ (b₀ ++ bs_rest).length ∧
        104 + gcs.length * 104 ≤ (b₀ ++ bs_rest).length := by
      rw [BitVec.add_zero, List.length_append, hb₀_len, hbs_len]
      have ⟨hb1, hb2⟩ := DhCommitFacts.memmove_bounds (n := gcs.length)
      exact ⟨hx0_1, hx1_1, hx2_toNat, hb1, hb2⟩
    rw [hsp1, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpre_pure, ?_⟩
    rw [hcomb_bytes, show b₀ = chainBytes gc₀ pad₀ from rfl, hcells_ptr]
    refine Satisfies.mono (Entails.of_eq ?_) hm_s1'
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.memmove_ok_at_0xe6c0 hA dropChainStack)
    hpc1 hrun1 hsp_align1 hx30_1 hm_memmove hL1 (by intro _; rfl) (by intros; rfl) ?_
  intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 _hkf2 _hsym2 hL2 hm_s2
  dsimp only [sessionMemmoveSpec] at hm_s2
  rw [hsp1, sepConj_assoc, satisfies_pure_sepConj] at hm_s2
  rcases hm_s2 with ⟨⟨_hx0_2, htr2⟩, hm_s2⟩
  have hvec_reasm :
      s2.mem ⊨
        memRegion (sp + 0x190#64) 104 ∗
        (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
         ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
         ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
         ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
         chainHeap A gc₀ ∗
         A.pool ∗
         stackAt sp dropChainStack ∗
         (Frame ∗ R)) := by
    have hpull_rem :
        s2.mem ⊨
          (A.live chainsPtr (chainsCap.toNat * 104) 8 ∗
           (chainsPtr ↦ₛ listMove (b₀ ++ bs_rest) 0 104 (gcs.length * 104)) ∗
           memRegion (chainsPtr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
             ((chainsCap.toNat - (gcs.length + 1)) * 104) ∗
           chainHeaps A gcs) ∗
          (memRegion (sp + 0x190#64) 104 ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
           ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
           ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
           ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
           ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12) ∗
           ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
           chainHeap A gc₀ ∗
           A.pool ∗
           stackAt sp dropChainStack ∗
           (Frame ∗ R)) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm_s2
      ac_rfl
    have hrem := Satisfies.mono
      (sepConj_mono_left (vecBuf_chainAt_of_remove0 A chainsCap chainsPtr hb₀_len hrest hcap_le hcap_lt hptr))
      hpull_rem
    refine Satisfies.mono (Entails.of_eq ?_) hrem
    ac_rfl
  obtain ⟨s190, s198, s1a0, s1a8, s1b0, s1b8, s1c0, s1c8, s1d0, s1d8, s1e0, s1e8, s1f0, hm_s2_cells⟩ :=
    elim_memRegion_104 hvec_reasm
  have hm_post_mm_wp :
      s2.mem ⊨
        (((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gc₀ :: gcs).length) ∗
         ((sp + 0x190#64) ↦₆₄ s190) ∗ ((sp + 0x198#64) ↦₆₄ s198) ∗ ((sp + 0x1a0#64) ↦₆₄ s1a0) ∗
         ((sp + 0x1a8#64) ↦₆₄ s1a8) ∗ ((sp + 0x1b0#64) ↦₆₄ s1b0) ∗ ((sp + 0x1b8#64) ↦₆₄ s1b8) ∗
         ((sp + 0x1c0#64) ↦₆₄ s1c0) ∗ ((sp + 0x1c8#64) ↦₆₄ s1c8) ∗ ((sp + 0x1d0#64) ↦₆₄ s1d0) ∗
         ((sp + 0x1d8#64) ↦₆₄ s1d8) ∗ ((sp + 0x1e0#64) ↦₆₄ s1e0) ∗ ((sp + 0x1e8#64) ↦₆₄ s1e8) ∗
         ((sp + 0x1f0#64) ↦₆₄ s1f0) ∗
         ((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
         ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
         ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
         ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          chainHeap A gc₀ ∗
          A.pool ∗
          stackAt sp dropChainStack ∗
          Frame) ∗ R) := by
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    have e4 := add_assoc_const sp 0x190#64 32#64 0x1b0#64
    have e5 := add_assoc_const sp 0x190#64 40#64 0x1b8#64
    have e6 := add_assoc_const sp 0x190#64 48#64 0x1c0#64
    have e7 := add_assoc_const sp 0x190#64 56#64 0x1c8#64
    have e8 := add_assoc_const sp 0x190#64 64#64 0x1d0#64
    have e9 := add_assoc_const sp 0x190#64 72#64 0x1d8#64
    have e10 := add_assoc_const sp 0x190#64 80#64 0x1e0#64
    have e11 := add_assoc_const sp 0x190#64 88#64 0x1e8#64
    have e12 := add_assoc_const sp 0x190#64 96#64 0x1f0#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12] at hm_s2_cells
    refine Satisfies.mono (Entails.of_eq ?_) hm_s2_cells
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4b_post_memmove_wp img.base ext sp
      (BitVec.ofNat 64 (gc₀ :: gcs).length)
      c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
      s190 s198 s1a0 s1a8 s1b0 s1b8 s1c0 s1c8 s1d0 s1d8 s1e0 s1e8 s1f0
      s2 hpc2 hrun2 (by reg_chain) hsp_align2
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      hc0_ne)
    hm_post_mm_wp hL2 ?_
  intro s3 P3 hpc3 hrun3 _hkf3 _hsym3 hL3 hm_s3 hpost3
  rcases hpost3 with ⟨hsp3, hsp_align3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, _hx26_3, hx27_3, _hx28_3, hx29_3, hx30_3, hvregs_3, hP3⟩
  have hm_s3' := Satisfies.mono (sepConj_mono_left hP3) hm_s3
  have hcells_190 : ((sp + 0x190#64) ↦ₛ chainBytes gc₀ pad₀) =
      ((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
      ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
      ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
      ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
      ((sp + 0x1f0#64) ↦₆₄ c12) := by
    have h := pointsToBytes_chainBytes_eq_13_cells (sp + 0x190#64) gc₀ hpad₀
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    have e4 := add_assoc_const sp 0x190#64 32#64 0x1b0#64
    have e5 := add_assoc_const sp 0x190#64 40#64 0x1b8#64
    have e6 := add_assoc_const sp 0x190#64 48#64 0x1c0#64
    have e7 := add_assoc_const sp 0x190#64 56#64 0x1c8#64
    have e8 := add_assoc_const sp 0x190#64 64#64 0x1d0#64
    have e9 := add_assoc_const sp 0x190#64 72#64 0x1d8#64
    have e10 := add_assoc_const sp 0x190#64 80#64 0x1e0#64
    have e11 := add_assoc_const sp 0x190#64 88#64 0x1e8#64
    have e12 := add_assoc_const sp 0x190#64 96#64 0x1f0#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12] at h
    exact h
  have h500_reg :
      (((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
       ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
       ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
       ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ⊢
      memRegion (sp + 0x500#64) 96 := by
    have h := cells_12_to_memRegion_96 (sp + 0x500#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
    have e1 := add_assoc_const sp 0x500#64 8#64 0x508#64
    have e2 := add_assoc_const sp 0x500#64 16#64 0x510#64
    have e3 := add_assoc_const sp 0x500#64 24#64 0x518#64
    have e4 := add_assoc_const sp 0x500#64 32#64 0x520#64
    have e5 := add_assoc_const sp 0x500#64 40#64 0x528#64
    have e6 := add_assoc_const sp 0x500#64 48#64 0x530#64
    have e7 := add_assoc_const sp 0x500#64 56#64 0x538#64
    have e8 := add_assoc_const sp 0x500#64 64#64 0x540#64
    have e9 := add_assoc_const sp 0x500#64 72#64 0x548#64
    have e10 := add_assoc_const sp 0x500#64 80#64 0x550#64
    have e11 := add_assoc_const sp 0x500#64 88#64 0x558#64
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h
    exact h
  have hsub1 : BitVec.ofNat 64 (gc₀ :: gcs).length - 1#64 = BitVec.ofNat 64 gcs.length :=
    sub_one_ofNat_succ gcs.length
  have hm_drop :
      s3.mem ⊨
        (dropChainSpec A).pre ⟨sp + 0x190#64, gc₀⟩ s3 ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          memRegion (sp + 0x500#64) 96 ∗
          Frame) ∗ R) := by
    dsimp only [dropChainSpec]
    rw [hsp3, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0_3, ?_⟩
    have hpull_drop :
        s3.mem ⊨
          ((((sp + 0x190#64) ↦₆₄ c0) ∗ ((sp + 0x198#64) ↦₆₄ c1) ∗ ((sp + 0x1a0#64) ↦₆₄ c2) ∗
            ((sp + 0x1a8#64) ↦₆₄ c3) ∗ ((sp + 0x1b0#64) ↦₆₄ c4) ∗ ((sp + 0x1b8#64) ↦₆₄ c5) ∗
            ((sp + 0x1c0#64) ↦₆₄ c6) ∗ ((sp + 0x1c8#64) ↦₆₄ c7) ∗ ((sp + 0x1d0#64) ↦₆₄ c8) ∗
            ((sp + 0x1d8#64) ↦₆₄ c9) ∗ ((sp + 0x1e0#64) ↦₆₄ c10) ∗ ((sp + 0x1e8#64) ↦₆₄ c11) ∗
            ((sp + 0x1f0#64) ↦₆₄ c12)) ∗ chainHeap A gc₀) ∗
          (((sp + 0x500#64) ↦₆₄ c1) ∗ ((sp + 0x508#64) ↦₆₄ c2) ∗ ((sp + 0x510#64) ↦₆₄ c3) ∗
           ((sp + 0x518#64) ↦₆₄ c4) ∗ ((sp + 0x520#64) ↦₆₄ c5) ∗ ((sp + 0x528#64) ↦₆₄ c6) ∗
           ((sp + 0x530#64) ↦₆₄ c7) ∗ ((sp + 0x538#64) ↦₆₄ c8) ∗ ((sp + 0x540#64) ↦₆₄ c9) ∗
           ((sp + 0x548#64) ↦₆₄ c10) ∗ ((sp + 0x550#64) ↦₆₄ c11) ∗ ((sp + 0x558#64) ↦₆₄ c12)) ∗
          (A.pool ∗ stackAt sp dropChainStack ∗
           ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ (BitVec.ofNat 64 (gc₀ :: gcs).length - 1#64)) ∗
             vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
             Frame) ∗ R)) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm_s3'
      ac_rfl
    rw [← hcells_190, hsub1] at hpull_drop
    have hch := Satisfies.mono
      (sepConj_mono (chainAt_of_bytes A gc₀ (sp + 0x190#64) hpad₀)
        (sepConj_mono_left h500_reg))
      hpull_drop
    refine Satisfies.mono (Entails.of_eq ?_) hch
    ac_rfl
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_dropChain_eq] at hpc3
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic hDrop
    hpc3 hrun3 hsp_align3 hx30_3 hm_drop hL3 (by intro _; rfl) (by intros; rfl) ?_
  intro s4 hpc4 hrun4 hsp4 hsp_align4 hcs4 _hkf4 _hsym4 hL4 hm_s4
  dsimp only [dropChainSpec] at hm_s4
  rw [hsp3, sepConj_assoc, satisfies_pure_sepConj] at hm_s4
  rcases hm_s4 with ⟨htr4, hm_s4⟩
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpc4, hrun4, by reg_chain, hsp_align4, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL4, ?_⟩
  unfold evictActive
  refine Satisfies.mono (Entails.of_eq ?_) hm_s4
  ac_rfl

/-- Full eviction loop (`+0xb04 → +0xb98`) while `6 ≤ gcs.length`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_evict_loop (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hDrop : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    ∀ (s : State),
      6 ≤ gcs.length →
      gcs.length ≤ 2 ^ 32 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb04#64 →
      s.status = .Running →
      s.sp = sp →
      s.spAligned = true →
      s.trace = s0.trace →
      s.readReg64 .x23 = sp + 0x500#64 →
      s.readReg64 .x24 = sp + 0x190#64 →
      s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x27 = 0xffffffffffffff98#64 →
      s.readReg64 .x28 = BitVec.ofNat 64 gcs.length →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      (s.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb98#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 0x500#64 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
        (sf.mem ⊨ evictActive A sp chainsCap chainsPtr (evictList gcs) ∗ (Frame ∗ R))) := by
  induction gcs with
  | nil =>
    intro _ hge
    simp at hge
  | cons gc₀ gcs ih =>
    intro s hge hle hpc hrun hsp hsp_align htrace hx23 hx24 hx25 hx27 hx28 hL hmem
    rw [evictList_cons_of_ge_six gc₀ gcs hge]
    have hlen_lt : gcs.length < 2 ^ 32 := DhCommitFacts.len_lt_of_cons_le hle
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_evict_one img C A ctl S ext hA hDrop x R Frame s0 s sp chainsCap chainsPtr gc₀ gcs
        hlen_lt hpc hrun hsp hsp_align htrace hx23 hx24 hx25 hx27 hx28 hL hmem) ?_
    intro s1 _hkf1 _hsym1 ⟨hpc1, hrun1, hsp1, hsp_align1, htr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx29_1, hvregs_1, hL1, hm1⟩
    have hm1_48 :
        s1.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
            memRegion (sp + 0x190#64) 104 ∗
            memRegion (sp + 0x500#64) 96 ∗
            A.pool ∗
            stackAt sp dropChainStack ∗
            Frame) ∗ R) := by
      unfold evictActive at hm1
      refine Satisfies.mono (Entails.of_eq ?_) hm1
      ac_rfl
    by_cases hge' : 6 ≤ gcs.length
    · have hhi : BitVec.ult 5#64 (BitVec.ofNat 64 gcs.length) = true :=
        DhCommitFacts.ult_five_of_ge_six hge' hlen_lt
      refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4c_hi_wp img.base ext sp (BitVec.ofNat 64 gcs.length)
          s1 hpc1 hrun1 hsp1 hsp_align1 hhi)
        hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 _hkf2 _hsym2 hL2 hm2 hpost2
      rcases hpost2 with ⟨hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hx29_2, hvregs_2, hP2⟩
      have hm2_act : s2.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        unfold evictActive
        refine Satisfies.mono (Entails.of_eq ?_) hm2'
        ac_rfl
      refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.seq
        (ih s2 hge' (Nat.le_of_lt hlen_lt) hpc2 hrun2 hsp2 hsp_align2 (by reg_chain)
          (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hx28_2 hL2 hm2_act) ?_
      intro sf _ _ ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx23_f, hx25_f, by reg_chain,
        by reg_chain, hL_f, hm_f⟩
    · have hle5 : gcs.length ≤ 5 := DhCommitFacts.le_five_of_not_ge_six hge'
      have hle_bv : BitVec.ult 5#64 (BitVec.ofNat 64 gcs.length) = false :=
        DhCommitFacts.ult_five_eq_false_of_le_five hle5
      refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4c_le_wp img.base ext sp (BitVec.ofNat 64 gcs.length)
          s1 hpc1 hrun1 hsp1 hsp_align1 hle_bv)
        hm1_48 hL1 ?_
      intro s2 P2 hpc2 hrun2 _hkf2 _hsym2 hL2 hm2 hpost2
      rcases hpost2 with ⟨hsp2, hsp_align2, htr2, hx19_2, hx20_2, hx21_2, hx22_2,
        hx23_2, hx25_2, _hx27_2, _hx28_2, hx29_2, hvregs_2, hP2⟩
      rw [evictList_of_le_five gcs hle5]
      have hm2_act : s2.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        unfold evictActive
        refine Satisfies.mono (Entails.of_eq ?_) hm2'
        ac_rfl
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpc2, hrun2, hsp2, hsp_align2, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain,
        by reg_chain, by reg_chain, by reg_chain, by reg_chain, hL2, hm2_act⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_step4 (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hDrop : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DropChainOkExt img.base A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hle : gcs.length ≤ 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xaf0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx23 : s.readReg64 .x23 = sp + 0x500#64)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hmem : s.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0xb98#64 ∧
      sf.status = .Running ∧
      sf.sp = sp ∧
      sf.spAligned = true ∧
      sf.trace = s0.trace ∧
      sf.readReg64 .x19 = s.readReg64 .x19 ∧
      sf.readReg64 .x20 = s.readReg64 .x20 ∧
      sf.readReg64 .x21 = s.readReg64 .x21 ∧
      sf.readReg64 .x22 = s.readReg64 .x22 ∧
      sf.readReg64 .x23 = sp + 0x500#64 ∧
      sf.readReg64 .x25 = sp + 0x190#64 ∧
      sf.readReg64 .x29 = s.readReg64 .x29 ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
      (sf.mem ⊨ evictActive A sp chainsCap chainsPtr (evictList gcs) ∗ (Frame ∗ R))) := by
  have hm_48 :
      s.mem ⊨ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          memRegion (sp + 0x190#64) 104 ∗
          memRegion (sp + 0x500#64) 96 ∗
          A.pool ∗
          stackAt sp dropChainStack ∗
          Frame) ∗ R) := by
    unfold evictActive at hmem
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  by_cases hlt6 : gcs.length < 6
  · have hlo : BitVec.ult (BitVec.ofNat 64 gcs.length) 6#64 = true :=
      DhCommitFacts.ult_six_of_lt_six hlt6
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4a_lo_wp img.base ext sp (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align hlo)
      hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx25_1, _hx27_1, _hx28_1, hx29_1, hvregs_1, hP1⟩
    rw [evictList_of_le_five gcs (DhCommitFacts.le_five_of_lt_six hlt6)]
    have hm1_act : s1.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      unfold evictActive
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      ac_rfl
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpc1, hrun1, hsp1, hsp_align1, htr1.trans htrace,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1.trans hx23, hx25_1.trans hx25, hx29_1, hvregs_1, hL1, hm1_act⟩
  · have hge6 : 6 ≤ gcs.length := DhCommitFacts.ge_six_of_not_lt_six hlt6
    have hge_bv : BitVec.ult (BitVec.ofNat 64 gcs.length) 6#64 = false :=
      DhCommitFacts.ult_six_eq_false_of_not_lt_six hlt6 hle
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.commit_step4a_ge_wp img.base ext sp (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align hx25 hge_bv)
      hm_48 hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1_act : s1.mem ⊨ evictActive A sp chainsCap chainsPtr gcs ∗ (Frame ∗ R) := by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      unfold evictActive
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.seq
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dhCommit_evict_loop img C A ctl S ext hA hDrop x R Frame s0 sp chainsCap chainsPtr gcs
        s1 hge6 hle hpc1 hrun1 hsp1 hsp_align1 (htr1.trans htrace)
        (hx23_1.trans hx23) hx24_1 hx25_1 hx27_1 hx28_1 hL1 hm1_act) ?_
    intro sf _ _ ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx25_f, hx29_f, hvregs_f, hL_f, hm_f⟩
    exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done ⟨hpc_f, hrun_f, hsp_f, hsp_align_f, htr_f,
      hx19_f.trans hx19_1, hx20_f.trans hx20_1, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
      hx23_f, hx25_f, hx29_f.trans hx29_1, hvregs_f.trans hvregs_1, hL_f, hm_f⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
