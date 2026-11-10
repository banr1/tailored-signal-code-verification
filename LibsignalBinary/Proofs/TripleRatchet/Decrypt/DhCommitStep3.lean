/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitPack
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitWp
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# DH Step Commit Sub-Segment 3 (`dhCommit_step3`)

Verifies `+0xa84 → +0xaf0`: pushes the new `ReceiverChain` onto `receiver_chains` (calling
`grow_one` when `len = cap`) and deallocates the 33-byte `PublicKey::serialize` buffer.
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

/-! ## 13. Sub-Segment 3 Composition (`dhCommit_step3`: `+0xa84 → +0xaf0`) -/

abbrev growOneStack : Nat := 4608

theorem vecBuf_chainAt_expose_bytes (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜ChainArrayBytes gcs bs ∧ bs.length = gcs.length * 104 ∧
          gcs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else
           A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
             chainHeaps A gcs) := by
  by_cases hcap : cap = 0
  · subst hcap
    rw [vecBuf_zero, ← sepConj_emp ⌜gcs = [] ∧ ptr ≠ 0⌝]
    apply Entails.pure_left
    rintro ⟨rfl, hptr⟩
    apply Entails.sepExists_right []
    apply Entails.pure_right ⟨ChainArrayBytes.nil, rfl, by decide, by decide, hptr⟩
    simp
    exact Entails.refl _
  · refine Entails.trans (vecBuf_chainAt_entails_bytes A cap ptr gcs hcap) ?_
    apply Entails.sepExists_elim
    intro bs
    apply Entails.sepExists_right bs
    simp only [hcap, ↓reduceIte]
    exact Entails.refl _

theorem vecBuf_expose_for_grow (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (bs : List (BitVec 8))
    (hlen_bs : bs.length = gcs.length * 104) (hlen_eq_cap : gcs.length = cap.toNat) :
    (if cap = 0 then emp
     else
       A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 (gcs.length * 104)) ((cap.toNat - gcs.length) * 104) ∗
         chainHeaps A gcs) =
    ((if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ chainHeaps A gcs) := by
  by_cases hcap : cap = 0
  · subst hcap
    have h0 : gcs.length = 0 := hlen_eq_cap
    rcases List.eq_nil_of_length_eq_zero h0 with rfl
    simp [chainHeaps]
  · simp only [hcap, ↓reduceIte, hlen_bs, hlen_eq_cap, Nat.sub_self, Nat.zero_mul,
      memRegion_zero]
    ac_rfl

theorem vecBuf_expose_for_push (A : RustAlloc) (cap ptr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain)) (hlt : gcs.length < cap.toNat) :
    vecBuf A 104 8 (chainAt A) cap ptr gcs ⊢
      ⌜cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (chainAt A) 104 ptr gcs ∗
      memRegion (ptr + BitVec.ofNat 64 gcs.length * 104#64) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104))
        ((cap.toNat - (gcs.length + 1)) * 104) := by
  have hcap : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  rw [vecBuf_of_ne_zero A 104 8 (chainAt A) cap ptr gcs hcap]
  apply Entails.pure_left
  rintro ⟨_hle, hcap_lt, hptr⟩
  apply Entails.pure_right ⟨hcap_lt, hptr⟩
  have hrem : (cap.toNat - gcs.length) * 104 =
      104 + (cap.toNat - (gcs.length + 1)) * 104 := by
    have : cap.toNat - gcs.length = 1 + (cap.toNat - (gcs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (gcs.length * 104) = BitVec.ofNat 64 gcs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (gcs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((gcs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (gcs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by ac_rfl)

/-- Step 3a (`+0xa84 → +0xa9c`): checks `rcLen = chainsCap`, calling `grow_one` if equal,
guaranteeing `gcs.length < chainsCap1.toNat` at `+0xa9c`. -/
theorem dhCommit_step3a (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hGrow : GrowOneChainOkExt img A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0xa9c#64 ∧
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
        (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
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
  · have hexp := Satisfies.mono (sepConj_mono_left (vecBuf_chainAt_expose_bytes A chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
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
    refine ReachesOrPanic.of_sepWP
      (commit_step3a_grow_wp img.base ext sp (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align)
      hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hpc1' : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr growOneChainName := by
      rw [hpc1, fnAddr_growOneChain_eq]
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
    refine ReachesOrPanic.of_call_alloc_panic hGrow hpc1' hrun1 hsp_align1 hx30_1
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
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < cap1.toNat := by omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
    rw [h38_8] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
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
    exact ReachesOrPanic.done ⟨cap1, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, hL2, hm2_final⟩
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
    refine ReachesOrPanic.of_sepWP
      (commit_step3a_nogrow_wp img.base ext sp chainsCap (BitVec.ofNat 64 gcs.length)
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
    exact ReachesOrPanic.done ⟨chainsCap, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

/-- Generic Step 3b (`+0xa9c → +0xaf0`): writes the new `ReceiverChain` into slot `rcLen`,
increments `rcLen`, and calls `__rust_dealloc(boxPtr, 33, 1)`. -/
theorem dhCommit_step3b_of_wp {prog : Program} {entry deallocEntry : BitVec 64}
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hwp3b : ∀ (sp chainsPtr1 rcLen boxPtr srkPtr : BitVec 64)
      (ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64) (s : State),
      s.pc = entry + 0xa9c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x24 = rcLen → s.readReg64 .x25 = sp + 0x190#64 →
      s.readReg64 .x26 = 33#64 → s.readReg64 .x27 = boxPtr → s.readReg64 .x28 = srkPtr →
      SepWP prog deallocEntry s
        (((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ rcLen) ∗
         ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
         ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
         ((chainsPtr1 + rcLen * 104#64) ↦₆₄ w0) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ w1) ∗
         ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ w2) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ w3) ∗
         ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ w4) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ w5) ∗
         ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ w6) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ w7) ∗
         ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ w8) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ w9) ∗
         ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ w10) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ w11) ∗
         ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ w12))
        (fun sf P_f =>
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x0 = boxPtr ∧ sf.readReg64 .x1 = 33#64 ∧ sf.readReg64 .x2 = 1#64 ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = rcLen ∧
          sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x26 = 33#64 ∧
          sf.readReg64 .x27 = boxPtr ∧ sf.readReg64 .x28 = rcLen + 1#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x30 = entry + 0xaf0#64 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          (P_f ⊢
            ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗ ((sp + 0x48#64) ↦₆₄ (rcLen + 1#64)) ∗
            ((sp + 0x190#64) ↦₆₄ ck0) ∗ ((sp + 0x198#64) ↦₆₄ ck1) ∗
            ((sp + 0x1a0#64) ↦₆₄ ck2) ∗ ((sp + 0x1a8#64) ↦₆₄ ck3) ∗
            ((chainsPtr1 + rcLen * 104#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 8#64) ↦₆₄ srkPtr) ∗
            ((chainsPtr1 + rcLen * 104#64 + 16#64) ↦₆₄ 33#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 24#64) ↦₆₄ 0#64) ∗
            ((chainsPtr1 + rcLen * 104#64 + 32#64) ↦₆₄ 1#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 40#64) ↦₆₄ 0#64) ∗
            ((chainsPtr1 + rcLen * 104#64 + 48#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 56#64) ↦₆₄ 8#64) ∗
            ((chainsPtr1 + rcLen * 104#64 + 64#64) ↦₆₄ 0#64) ∗ ((chainsPtr1 + rcLen * 104#64 + 72#64) ↦₆₄ ck0) ∗
            ((chainsPtr1 + rcLen * 104#64 + 80#64) ↦₆₄ ck1) ∗ ((chainsPtr1 + rcLen * 104#64 + 88#64) ↦₆₄ ck2) ∗
            ((chainsPtr1 + rcLen * 104#64 + 96#64) ↦₆₄ ck3))))
    (hDealloc : subroutine_ok prog deallocEntry (rustDeallocSpec A))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s s1 : State)
    (sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlt_cap1 : gcs.length < chainsCap1.toNat)
    (hpad : pad.length = 4)
    (hsrk_ne : srkPtr ≠ 0)
    (hpc1 : s1.pc = entry + 0xa9c#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = sp)
    (hsp_align1 : s1.spAligned = true)
    (htr1 : s1.trace = s0.trace)
    (hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19)
    (hx20_1 : s1.readReg64 .x20 = s.readReg64 .x20)
    (hx21_1 : s1.readReg64 .x21 = s.readReg64 .x21)
    (hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22)
    (hx23_1 : s1.readReg64 .x23 = s.readReg64 .x23)
    (hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 gcs.length)
    (hx25_1 : s1.readReg64 .x25 = s.readReg64 .x25)
    (hx26_1 : s1.readReg64 .x26 = s.readReg64 .x26)
    (hx27_1 : s1.readReg64 .x27 = s.readReg64 .x27)
    (hx28_1 : s1.readReg64 .x28 = s.readReg64 .x28)
    (hx29_1 : s1.readReg64 .x29 = s.readReg64 .x29)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL1 : prog.CodeLoaded s1.mem)
    (hm1 : s1.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 gcs ∗
       A.pool ∗
       stackAt sp growOneStack) ∗
      ((((sp + 0x190#64) ↦ₛ optChainKeyTailBytes ⟨32#64, ckPtr⟩ (some rck) pad) ∗
        memRegion (sp + 0x1b0#64) 72 ∗
        (A.live boxPtr 33 1 ∗ (boxPtr ↦ₛ srk.serialize)) ∗
        (A.live srkPtr 33 1 ∗ (srkPtr ↦ₛ srk.serialize)) ∗
        optChainKeyHeap A ⟨32#64, ckPtr⟩ (some rck) ∗
        Frame) ∗ R)) :
    let newGC := (newChainGhost srkPtr ckPtr srk, newReceiverChain srk rck)
    ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧
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
        prog.CodeLoaded sf.mem ∧
        (sf.mem ⊨
          (((sp + 0x38#64) ↦₆₄ chainsCap1) ∗
           ((sp + 0x40#64) ↦₆₄ chainsPtr1) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 (gcs ++ [newGC]).length) ∗
           vecBuf A 104 8 (chainAt A) chainsCap1 chainsPtr1 (gcs ++ [newGC]) ∗
           memRegion (sp + 0x190#64) 104 ∗
           A.pool ∗
           stackAt sp growOneStack) ∗ (Frame ∗ R))) := by
  intro newGC
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
  have hm1_exp := Satisfies.mono (sepConj_mono_left (vecBuf_expose_for_push A chainsCap1 chainsPtr1 gcs hlt_cap1)) hm1_push
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
  refine ReachesOrPanic.of_sepWP
    (hwp3b sp chainsPtr1 rcLen boxPtr srkPtr
      ck0 ck1 ck2 ck3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      s1 hpc1 hrun1 hsp1 hsp_align1 hx24_1
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain))
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
  refine ReachesOrPanic.of_call_no_panic hDealloc
    hpc2 hrun2 hsp_align2 hx30_2 hm_dealloc hL2 (by intro _; rfl) (by intros; rfl) ?_
  intro s3 hpc3 hrun3 hsp3 hsp_align3 hcs3 _hkf3 _hsym3 hL3 hm3
  dsimp only [rustDeallocSpec] at hm3
  rw [hsp2, sepConj_assoc, satisfies_pure_sepConj] at hm3
  rcases hm3 with ⟨htr3, hm3⟩
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
  exact ReachesOrPanic.done ⟨chainsCap1, chainsPtr1, hpc3, hrun3, by reg_chain, hsp_align3,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, hL3, hm3_final⟩

/-- Step 3 (`+0xa84 → +0xaf0`): pushes the new `ReceiverChain` onto `receiver_chains`
(growing if `len = cap`), then frees `boxPtr` (`__rust_dealloc(boxPtr, 33, 1)`). -/
theorem dhCommit_step3 (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hGrow : GrowOneChainOkExt img A ext)
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4)
    (hsrk_ne : srkPtr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0xa84#64)
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
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
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
    ReachesOrPanic (tripleRatchetProgAtExt img.base ext) C A ctl uuidTryParse S img x R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr tryDecryptName + 0xaf0#64 ∧
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
        (tripleRatchetProgAtExt img.base ext).CodeLoaded sf.mem ∧
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
  refine ReachesOrPanic.seq
    (dhCommit_step3a img C A ctl S ext hGrow x R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hpc hrun hsp hsp_align htrace hfrozen hsym hL hm3a) ?_
  rintro s1 _ _ ⟨chainsCap1, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
    hvregs_1, hL1, hm1⟩
  exact dhCommit_step3b_of_wp img C A ctl S (commit_step3b_wp img.base ext) (dealloc_ok_at_0xe6b8 hA)
    x R Frame s0 s s1 sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr gcs srk rck pad
    hlt_cap1 hpad hsrk_ne hpc1 hrun1 hsp1 hsp_align1 htr1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    hx25 hx26 hx27 hx28 hL1 hm1

/-- Relocatable Step 3a (`+0xa84 → +0xa9c`): checks `rcLen = chainsCap`, calling `grow_one` if equal. -/
theorem dhCommit_step3a_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (CryptoVerification.LibsignalSession.growOneSpec A))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpc : s.pc = entry + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hL : prog.CodeLoaded s.mem)
    (hmem : s.mem ⊨
      (((sp + 0x38#64) ↦₆₄ chainsCap) ∗
       ((sp + 0x40#64) ↦₆₄ chainsPtr) ∗
       ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
       vecBuf A 104 8 (chainAt A) chainsCap chainsPtr gcs ∗
       A.pool ∗
       stackAt sp growOneStack) ∗ (Frame ∗ R)) :
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        gcs.length < chainsCap1.toNat ∧
        sf.pc = entry + 0xa9c#64 ∧
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
        prog.CodeLoaded sf.mem ∧
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
  · have hexp := Satisfies.mono (sepConj_mono_left (vecBuf_chainAt_expose_bytes A chainsCap chainsPtr gcs)) hexp0
    rw [sepExists_sepConj_left, satisfies_sepExists] at hexp
    rcases hexp with ⟨bs, hexp⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hexp
    rcases hexp with ⟨⟨hbs, hlen_bs, _hle_cap, _hcap_lt, hptr⟩, hexp⟩
    have hlen_eq_cap : gcs.length = chainsCap.toNat := by
      rw [← hgrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecBuf_expose_for_grow A chainsCap chainsPtr gcs bs hlen_bs hlen_eq_cap] at hexp
    have h38_grow : ((sp + 0x38#64) ↦₆₄ chainsCap) = ((sp + 0x38#64) ↦₆₄ BitVec.ofNat 64 gcs.length) := by
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
    refine ReachesOrPanic.of_sepWP
      (hwp.step3a_grow sp (BitVec.ofNat 64 gcs.length)
        s hpc hrun hsp hsp_align)
      hm_grow_wp hL ?_
    intro s1 P1 hpc1 hrun1 _hkf1 _hsym1 hL1 hm1 hpost1
    rcases hpost1 with ⟨hsp1, hsp_align1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1, hP1⟩
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hmax_lt : max (2 * chainsCap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 := by omega
    have hm_call : s1.mem ⊨
        (CryptoVerification.LibsignalSession.growOneSpec A).pre
          (sp + 0x38#64, chainsCap, chainsPtr, bs) s1 ∗
        ((((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 gcs.length) ∗
          chainHeaps A gcs ∗ Frame) ∗ R) := by
      dsimp only [CryptoVerification.LibsignalSession.growOneSpec]
      rw [hsp1]
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
    refine ReachesOrPanic.of_call_alloc_panic_placed hGrow
      hpc1 hrun1 hsp_align1 hx30_1 (htr1.trans htrace) hm_call hL1 (by intro _; rfl) (by intros; rfl) ?_
    intro s2 hpc2 hrun2 hsp2 hsp_align2 hcs2 _hkf2 hL2 hm2
    dsimp only [CryptoVerification.LibsignalSession.growOneSpec] at hm2
    rw [hsp1] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨htr2, hm2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
    rcases hm2 with ⟨p', hm2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
    rcases hm2 with ⟨hp', hm2⟩
    set cap1 := BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
    have hcap1_toNat : cap1.toNat = max (2 * chainsCap.toNat) 4 := by
      dsimp only [cap1]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt_cap1 : gcs.length < cap1.toNat := by omega
    have hcap1_ne : cap1 ≠ 0 := by
      intro h0; rw [h0] at hcap1_toNat; change 0 = max (2 * chainsCap.toNat) 4 at hcap1_toNat; omega
    have h38_8 := add_assoc_const sp 0x38#64 8#64 0x40#64
    rw [h38_8] at hm2
    have hlive_eq : A.live p' (max (2 * chainsCap.toNat) 4 * 104) 8 = A.live p' (cap1.toNat * 104) 8 := by
      rw [hcap1_toNat]
    have hmr_eq :
        memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * chainsCap.toNat) 4 - chainsCap.toNat) * 104) =
          memRegion (p' + BitVec.ofNat 64 (gcs.length * 104)) ((cap1.toNat - gcs.length) * 104) := by
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
    exact ReachesOrPanic.done ⟨cap1, p', hlt_cap1, hpc2, hrun2, by reg_chain, hsp_align2,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
      by reg_chain, hL2, hm2_final⟩
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
    refine ReachesOrPanic.of_sepWP
      (hwp.step3a_nogrow sp chainsCap (BitVec.ofNat 64 gcs.length)
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
    exact ReachesOrPanic.done ⟨chainsCap, chainsPtr, hlt_cap, hpc1, hrun1, hsp1, hsp_align1,
      htr1.trans htrace, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1, hL1, hm1_final⟩

/-- Relocatable Step 3 (`+0xa84 → +0xaf0`). -/
theorem dhCommit_step3_placed [LibsignalPlacement] {prog : Program} {entry dropChainEntry : BitVec 64}
    (hwp : DhCommitBlockWp prog entry dropChainEntry)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (hGrow : subroutine_ok prog (lsmpl.base 43) (CryptoVerification.LibsignalSession.growOneSpec A))
    (hDealloc : subroutine_ok prog (lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (x : TryDecryptGhost) (R Frame : SepProp) (s0 s : State)
    (sp chainsCap chainsPtr boxPtr srkPtr ckPtr : BitVec 64)
    (gcs : List (ChainGhost × ReceiverChain))
    (srk : PublicKey) (rck : ChainKey) (pad : List (BitVec 8))
    (hlen_lt : gcs.length < 2 ^ 32)
    (hpad : pad.length = 4)
    (hsrk_ne : srkPtr ≠ 0)
    (hpc : s.pc = entry + 0xa84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = sp + 0x190#64)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx27 : s.readReg64 .x27 = boxPtr)
    (hx28 : s.readReg64 .x28 = srkPtr)
    (hL : prog.CodeLoaded s.mem)
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
    ReachesOrPanic prog C A ctl uuidTryParse S tryDecryptPlacedImg x R s0 s (fun sf =>
      ∃ chainsCap1 chainsPtr1 : BitVec 64,
        sf.pc = entry + 0xaf0#64 ∧
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
        prog.CodeLoaded sf.mem ∧
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
  refine ReachesOrPanic.seq
    (dhCommit_step3a_placed hwp C A ctl S hGrow x R Step3Rest s0 s sp chainsCap chainsPtr gcs
      hlen_lt hpc hrun hsp hsp_align htrace hL hm3a) ?_
  rintro s1 _ _ ⟨chainsCap1, chainsPtr1, hlt_cap1, hpc1, hrun1, hsp1, hsp_align1, htr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1,
    hvregs_1, hL1, hm1⟩
  exact dhCommit_step3b_of_wp tryDecryptPlacedImg C A ctl S hwp.step3b hDealloc
    x R Frame s0 s s1 sp chainsCap1 chainsPtr1 boxPtr srkPtr ckPtr gcs srk rck pad
    hlt_cap1 hpad hsrk_ne hpc1 hrun1 hsp1 hsp_align1 htr1
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1
    hx25 hx26 hx27 hx28 hL1 hm1

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
