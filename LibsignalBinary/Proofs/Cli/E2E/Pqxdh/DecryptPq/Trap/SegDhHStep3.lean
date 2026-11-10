/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHStep3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHPack
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHPack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhHPack
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegDhHWp
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHEvict
import ProofLib.SepLogic.WPp

/-!
# Trap-at-RNG DH Commit Sub-Segment 3

Proves `s3_step3a_trap` and `s3_step3_trap` (`+0xa84 → +0xaf0`) for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Sub-Segment 3 Composition (`s3_step3_trap`: `+0xa84 → +0xaf0`) -/

/-- Step 3a (`+0xa84 → +0xa9c`): checks `rcLen = chainsCap`, calling `grow_one` if equal,
guaranteeing `gcs.length < chainsCap1.toNat` at `+0xa9c`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step3a_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hGrow : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hL : (trTrapProgAt img.base C abs).CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic (trTrapProgAt img.base C abs) C A ctl uuidTryParse S img x R s0 s
      (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa9c#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 gcs.length ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (trTrapProgAt img.base C abs).CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
           ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
           vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 gcs ∗
           A.pool ∗
           stackAt sp growOneStack) ∗ (Frame ∗ R))) := by
  have hexp0 : s.mem ⊨
      vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       A.pool ∗ stackAt sp growOneStack ∗ (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  by_cases hgrow : BitVec.ofNat 64 gcs.length = chainsCap
  · have hexp :=
    Satisfies.mono (sepConj_mono_left (vecBuf_chainAt_expose_bytes A chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) =
        ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
      rw [hgrow]
    have hm_grow_wp : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
          chainHeaps A gcs ∗
          A.pool ∗
          stackAt sp growOneStack ∗
          Frame) ∗ R) := by
      rw [h38_grow] at hexp
      refine Satisfies.mono (Entails.of_eq ?_) hexp
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3a_grow_wp_trap img.base C abs sp (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align)
      hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hpc1' : s1.pc = (trTrapProgAt img.base C abs).fnAddr growOneChainName := by
      rw [hpc1, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_growOneChain_eq_trap]
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨
        ((CryptoVerification.LibsignalSession.growOneSpec A).inImage img).pre
          (sp + 0x38#64, chainsCap, chainsPtr, bs) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          chainHeaps A gcs ∗ Frame) ∗ R) := by
      dsimp only [CryptoVerification.LibsignalSession.growOneSpec, Spec.inImage]
      rw [hsp1]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hfrozen.of_keepsFrozen hkf1, hsym1.trans hsym⟩, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, by omega, hptr, hmax_lt⟩, ?_⟩
      have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
      rw [h38_8]
      have hm1'' : s1.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
          ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
            (if chainsCap = 0 then emp else A.live chainsPtr bs.length 8 ∗ (chainsPtr ↦ₛ bs)) ∗
            chainHeaps A gcs ∗
            A.pool ∗
            stackAt sp growOneStack ∗
            Frame) ∗ R) := by
        rw [← h38_grow] at hm1'
        exact hm1'
      refine Satisfies.mono (Entails.of_eq ?_) hm1''
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_call_alloc_panic hGrow hpc1' hrun1 hsp_align1 hx30_1
      (htr1.trans htrace) hm_call hL1 (by intro _; rfl) (by intros; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 _hkf2 _hsym2 hL2 hm2
    dsimp only [CryptoVerification.LibsignalSession.growOneSpec, Spec.inImage] at hm2
    rw [hsp1] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
    rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨hp', hm2⟩
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2,
        hx28_2, hx29_2, hvregs_2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < cap1.toNat := by omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
    rw [h38_8] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 =
        A.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat)
          * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) :=
            by
      rw [hlen_bs, hcap1_toNat, ← hlen_eq_cap]
    have hpull2 : s2.mem ⊨
        (A.live p' (cap1.toNat * 104) 8 ∗
         (p' ↦ₛ bs) ∗
         memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) ∗
         chainHeaps A gcs) ∗
        (((sp + 0x38#64) ↦₆₄ cap1) ∗
         ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         A.pool ∗
         stackAt sp growOneStack ∗
         (Frame ∗ R)) := by
      rw [hlive_eq, hmr_eq] at hm2
      refine Satisfies.mono (Entails.of_eq ?_) hm2
      ac_rfl
    have hreasm := vecBuf_chainAt_of_bytes A cap1 p' hcap1_ne hbs (by omega) (by omega) hp'
    have hm2_vec := Satisfies.mono (sepConj_mono_left hreasm) hpull2
    have hm2_final : s2.mem ⊨
        (((sp + 0x38#64) ↦₆₄ cap1) ∗
         ((sp + 0x40#64) ↦₆₄ p') ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A 104 8 (chainAt A) cap1 p' gcs ∗
         A.pool ∗
         stackAt sp growOneStack) ∗ (Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm2_vec
      ac_rfl
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.done ⟨cap1, p', hlt_cap1, hpc2, hrun2, hsp2.trans hsp1, hsp_align2,
      htr2.trans (htr1.trans htrace),
      hx19_2.trans hx19_1, hx20_2.trans hx20_1, hx21_2.trans hx21_1, hx22_2.trans hx22_1,
      hx23_2.trans hx23_1, hx24_2.trans hx24_1, hx25_2.trans hx25_1, hx26_2.trans hx26_1,
      hx27_2.trans hx27_1, hx28_2.trans hx28_1, hx29_2.trans hx29_1, hvregs_2.trans hvregs_1, hL2, hm2_final⟩
  · have hle_cap : gcs.length ≤ chainsCap.toNat := by
      unfold vecBuf at hexp0
      rw [sepConj_assoc, satisfies_pure_sepConj] at hexp0
      exact hexp0.1.1
    have hlt_cap : gcs.length < chainsCap.toNat := by
      rcases Nat.lt_or_eq_of_le hle_cap with hlt | heq
      · exact hlt
      · exfalso
        apply hgrow
        rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hm_nogrow : s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length)) ∗
        ((((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
          A.pool ∗
          stackAt sp growOneStack ∗
          Frame) ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hmem
      ac_rfl
    refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_sepWP
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3a_nogrow_wp_trap img.base C abs sp chainsCap (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align hgrow)
      hm_nogrow hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hm1_final : s1.mem ⊨
        (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
         vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
         A.pool ∗
         stackAt sp growOneStack) ∗ (Frame ∗ R) := by
      refine Satisfies.mono (Entails.of_eq ?_) hm1'
      ac_rfl
    exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.done ⟨chainsCap, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

/-- Step 3 (`+0xa84 → +0xaf0`): pushes the new `ReceiverChain` onto `receiver_chains`
(growing if `len = cap`), then frees `boxPtr` (`__rust_dealloc(boxPtr, 33, 1)`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step3_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs)
    (hGrow : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.GrowOneChainOk_trap img C A abs)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4)
    (hsrk_ne : srkPtr ≠ 0)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : (trTrapProgAt img.base C abs).CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic (trTrapProgAt img.base C abs) C A ctl uuidTryParse S img x R s0 s
      (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0xaf0#64 ∧
        sf.status = .Running ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (trTrapProgAt img.base C abs).CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
           ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool ∗
           stackAt sp growOneStack) ∗ (Frame ∗ R))) := by
  intro newGC
  set Step3Rest : SepProp :=
    ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
    memRegion (sp + 0x1b0#64) 72 ∗
    (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
    (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
    optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
    Frame
  have hm3a : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Step3Rest ∗ R) := by
    dsimp only [Step3Rest]
    refine Satisfies.mono (Entails.of_eq ?_) hmem
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.seq
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.s3_step3a_trap img C A ctl S abs hGrow x R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hpc hrun hsp hsp_align htrace hfrozen hsym hL hm3a) ?_
  rintro s1 _ _ ⟨chainsCap1, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
    hvregs_1, hL1, hm1⟩
  dsimp only [Step3Rest] at hm1
  have hm1_push : s1.mem ⊨
      vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 gcs ∗
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool ∗
       stackAt sp growOneStack ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1
    ac_rfl
  have hm1_exp :=
      Satisfies.mono (sepConj_mono_left (vecBuf_expose_for_push A chainsCap1 chainsPtr1 gcs
      hlt_cap1)) hm1_push
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_exp
  rcases hm1_exp with ⟨⟨hcap1_lt, hptr1_ne⟩, hm1_exp⟩
  set rcLen := BitVec.ofNat 64 gcs.length
  set slot := chainsPtr1 + rcLen * 104#64
  have hm1_slot : s1.mem ⊨
      memRegion slot 104 ∗
      (A.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A) 104 chainsPtr1 gcs ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
       ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
       memRegion (sp + 0x1b0#64) 72 ∗
       (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
       (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
       optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
       A.pool ∗
       stackAt sp growOneStack ∗
       (Frame ∗ R)) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm1_exp
    ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, hm1_w⟩ :=
    elim_memRegion_104 hm1_slot
  set tail := optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad
  have htail_len : tail.length = 32 := optChainKeyTailBytes_length ⟨32#64, ckPtr⟩ (some rck) hpad
  have h190_cells : ((sp + 0x190#64) ↦ₛ tail) =
      ((sp + 0x190#64) ↦₆₄ pack64 (tail.take 8)) ∗
      ((sp + 0x198#64) ↦₆₄ pack64 ((tail.drop 8).take 8)) ∗
      ((sp + 0x1a0#64) ↦₆₄ pack64 ((tail.drop 16).take 8)) ∗
      ((sp + 0x1a8#64) ↦₆₄ pack64 (tail.drop 24)) := by
    rw [pointsToBytes_32_eq_pointsTo64 (sp + 0x190#64) htail_len]
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    rw [e1, e2, e3]
  set ck0 := pack64 (tail.take 8)
  set ck1 := pack64 ((tail.drop 8).take 8)
  set ck2 := pack64 ((tail.drop 16).take 8)
  set ck3 := pack64 (tail.drop 24)
  have hm_step3b : s1.mem ⊨
      (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ rcLen) ∗
       ((sp + 0x190#64) ↦₆₄ ck0) ∗
       ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗
       ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
       ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗
       ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
       ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗
       ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
       ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗
       ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
       ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗
       ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
       ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗
       ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
       ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗
       ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
       ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12)) ∗
      ((A.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
        arrayAt (chainAt A) 104 chainsPtr1 gcs ∗
        memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
          ((chainsCap1.toNat - (gcs.length + 1)) * 104) ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
        memRegion (sp + 0x1b0#64) 72 ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
        A.pool ∗
        stackAt sp growOneStack ∗
        Frame) ∗ R) := by
    rw [h190_cells] at hm1_w
    dsimp only [slot] at hm1_w
    refine Satisfies.mono (Entails.of_eq ?_) hm1_w
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_sepWP
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.commit_step3b_wp_trap img.base C abs sp chainsPtr1 rcLen boxPtr srkPtr
      ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      s1 hpc1 hrun1 hsp1 hsp_align1 hx24_1
      (hx25_1.trans hx25) (hx26_1.trans hx26) (hx27_1.trans hx27) (hx28_1.trans hx28))
    hm_step3b hL1 ?_
  intro s2 P2 hpc2 hrun2 _hkf2 _hsym2 hL2 hm2 hpost2
  rcases hpost2 with ⟨hsp2, hsp_align2, htr2, hx0_2, hx1_2, hx2_2,
    hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _hx24_2, hx25_2, _hx26_2, _hx27_2, _hx28_2,
    hx29_2, hx30_2, hvregs_2, hP2⟩
  have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
  have h190_reg :
      (((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
       ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗
      memRegion (sp + 0x1b0#64) 72 ⊢ memRegion (sp + 0x190#64) 104 := by
    have hsplit104 := memRegion_split (sp + 0x190#64) 32 72 (by decide)
    rw [show (32 + 72 : Nat) = 104 from rfl] at hsplit104
    have h190_32 := add_assoc_const sp 0x190#64 (BitVec.ofNat 64 32) 0x1b0#64
    rw [hsplit104, h190_32]
    have h32 := cells_4_to_memRegion_32 (sp + 0x190#64) ck0 ck1 ck2 ck3
    have e1 := add_assoc_const sp 0x190#64 8#64 0x198#64
    have e2 := add_assoc_const sp 0x190#64 16#64 0x1a0#64
    have e3 := add_assoc_const sp 0x190#64 24#64 0x1a8#64
    rw [e1, e2, e3] at h32
    exact sepConj_mono_left h32
  have hslot_eq : chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104) = slot := by
    dsimp only [slot, rcLen]
    rw [BitVec.ofNat_mul]
  have hnew_chain :
      (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
        ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
        ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
        ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
        ((slot + 96#64) ↦₆₄ ck3) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck))) ⊢
      chainAt A newGC (chainsPtr1 + BitVec.ofNat 64 (gcs.length * 104)) := by
    rw [hslot_eq]
    exact chainAt_newChain_of_cells A slot srkPtr ckPtr srk rck hpad hsrk_ne
  have hpush_vec := vecBuf_chainAt_push_reassemble A chainsCap1 chainsPtr1 gcs newGC
    hlt_cap1 hcap1_lt hptr1_ne
  have hlen_append : rcLen + 1#64 = BitVec.ofNat 64 (gcs ++ [newGC]).length := by
    dsimp only [rcLen]
    rw [List.length_append, List.length_singleton, BitVec.ofNat_add]
  have hser_len : srk.serialize.length = 33 := publicKey_serialize_length srk
  have hm2_grouped : s2.mem ⊨
      (A.live chainsPtr1 (chainsCap1.toNat * 104) 8 ∗
       arrayAt (chainAt A) 104 chainsPtr1 gcs ∗
       (((slot ↦₆₄ 33#64) ∗ ((slot + 8#64) ↦₆₄ srkPtr) ∗ ((slot + 16#64) ↦₆₄ 33#64) ∗
         ((slot + 24#64) ↦₆₄ 0#64) ∗ ((slot + 32#64) ↦₆₄ 1#64) ∗ ((slot + 40#64) ↦₆₄ 0#64) ∗
         ((slot + 48#64) ↦₆₄ 0#64) ∗ ((slot + 56#64) ↦₆₄ 8#64) ∗ ((slot + 64#64) ↦₆₄ 0#64) ∗
         ((slot + 72#64) ↦₆₄ ck0) ∗ ((slot + 80#64) ↦₆₄ ck1) ∗ ((slot + 88#64) ↦₆₄ ck2) ∗
         ((slot + 96#64) ↦₆₄ ck3) ∗
         (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
         optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck))) ∗
       memRegion (chainsPtr1 + BitVec.ofNat 64 ((gcs.length + 1) * 104))
         ((chainsCap1.toNat - (gcs.length + 1)) * 104)) ∗
      ((((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
        ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3)) ∗
       memRegion (sp + 0x1b0#64) 72) ∗
      ((boxPtr ↦ₛ srk.serialize) ∗
       (A.live boxPtr 33 1 ∗ A.pool ∗
        ((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
        ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        stackAt sp growOneStack ∗
        Frame ∗ R)) := by
    rw [← hlen_append]
    dsimp only [slot]
    refine Satisfies.mono (Entails.of_eq ?_) hm2'
    ac_rfl
  have hm2_chain := Satisfies.mono
    (sepConj_mono
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hnew_chain)))
        hpush_vec)
      (sepConj_mono_left h190_reg))
    hm2_grouped
  have hbox_reg : (boxPtr ↦ₛ srk.serialize) ⊢ memRegion boxPtr 33 := by
    have h := pointsToBytes_entails_memRegion boxPtr srk.serialize
    rwa [hser_len] at h
  have hm2_box := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hbox_reg)))
    hm2_chain
  have hstk_dealloc := stackAt_split_from sp growOneStack allocHookStack (by decide) (by decide)
  have hm_dealloc : s2.mem ⊨
      (rustDeallocSpec A).pre (boxPtr, 33, 1) s2 ∗
      ((((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
        ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
        ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
        vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
        memRegion (sp + 0x190#64) 104 ∗
        memRegion (sp - BitVec.ofNat 64 growOneStack) (growOneStack - allocHookStack) ∗
        Frame) ∗ R) := by
    dsimp only [rustDeallocSpec]
    rw [hstk_dealloc] at hm2_box
    rw [hsp2]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_2, by rw [hx1_2]; rfl, by rw [hx2_2]; rfl⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm2_box
    ac_rfl
  refine CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_call_no_panic (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.dealloc_ok_at_0xe6b8_trap hHooks.alloc)
    hpc2 hrun2 hsp_align2 hx30_2 hm_dealloc hL2 (by intro _; rfl) (by intros; rfl) ?_
  intro s3 hpc3 hrun3 hsp3 hsp_align3 hcs3 _hkf3 _hsym3 hL3 hm3
  dsimp only [rustDeallocSpec] at hm3
  rw [hsp2, sepConj_assoc, satisfies_pure_sepConj] at hm3
  rcases hm3 with ⟨htr3, hm3⟩
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, _hx24_3, hx25_3, _hx26_3, _hx27_3,
      _hx28_3, hx29_3, hvregs_3⟩
  have hm3_final : s3.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
       memRegion (sp + 0x190#64) 104 ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Frame ∗ R) := by
    rw [hstk_dealloc]
    refine Satisfies.mono (Entails.of_eq ?_) hm3
    ac_rfl
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.done ⟨chainsCap1, chainsPtr1, hpc3, hrun3, hsp3.trans hsp2, hsp_align3,
    htr3.trans (htr2.trans htr1),
    hx19_3.trans (hx19_2.trans hx19_1),
    hx20_3.trans (hx20_2.trans hx20_1),
    hx21_3.trans (hx21_2.trans hx21_1),
    hx22_3.trans (hx22_2.trans hx22_1),
    hx23_3.trans (hx23_2.trans hx23_1),
    hx25_3.trans hx25_2,
    hx29_3.trans (hx29_2.trans hx29_1),
    hvregs_3.trans (hvregs_2.trans hvregs_1),
    hL3, hm3_final⟩

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
