/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2

/-!
# Stage P2 Substage P2.3 Helpers and Shared Tail

Provides `KyberPreKeyRecord` layout/rodata helpers and proves the shared Substage P2.3 tail
`stageP2_sub3_tail_kits` (`+0x0d04 → +0x0d5c`, allocating and dropping the 21-byte `"missing pq
ciphertext"` error buffer).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_pointsToBytes_1569_entails_memRegion (ptr : BitVec 64) (pk : List (BitVec 8))
    (h : pk.length = 1568) :
    (ptr ↦ₛ (8#8 :: pk)) ⊢ memRegion ptr 1569 := by
  have h1 := ProofLib.pointsToBytes_entails_memRegion ptr (8#8 :: pk)
  have hlen : (8#8 :: pk).length = 1569 := by simp [h]
  rwa [hlen] at h1

theorem p2_pointsToBytes_3169_entails_memRegion (ptr : BitVec 64) (sk : List (BitVec 8))
    (h : sk.length = 3168) :
    (ptr ↦ₛ (8#8 :: sk)) ⊢ memRegion ptr 3169 := by
  have h1 := ProofLib.pointsToBytes_entails_memRegion ptr (8#8 :: sk)
  have hlen : (8#8 :: sk).length = 3169 := by simp [h]
  rwa [hlen] at h1

theorem p2_stackAt_kemKeyPair_eq (sp : BitVec 64) :
    stackAt sp (64 + allocHookStack) =
      (memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack) := by
  have h1 := ResponderStore.stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  rw [h2] at h1
  exact h1

theorem p2_kemStack_le_pure : 64 + allocHookStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : 64 + allocHookStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_dropSpe_le_pure : dropSpeStack ≤ stageP2PureAndErrStack :=
  Nat.le_trans (by decide : dropSpeStack ≤ stageP2aStack) p2_stageP2a_le_pure

theorem p2_memRegion_65_split_cells5 (p : BitVec 64) :
    memRegion p 65 = cells p 5 ∗ memRegion (p + 40#64) 25 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 40) (k := 25)
        (b' := p + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells p 5 (by decide)]

theorem p2_sp_a90_5words_entails_memRegion (p w0 w1 w2 w3 w4 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗
    ((p + 24#64) ↦₆₄ w3) ∗ ((p + 32#64) ↦₆₄ w4) ∗ memRegion (p + 40#64) 25 ⊢
      memRegion p 65 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 57) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 49) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 41) (b' :=
        p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 8) (k := 33) (b' :=
        p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 25) (b' :=
        p + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

theorem p2_errStr_21_split16_eq (p : BitVec 64) :
    memRegion p 21 =
      (∃∗ u8 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u8) ∗ memRegion (p + 16#64) 5) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p, ProofLib.memRegion_eight (p + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_errStr_overlap13_entails (p ro8 : BitVec 64) :
    ((p + 8#64) ↦₆₄ ro8) ∗ memRegion (p + 16#64) 5 ⊢
      memRegion (p + 8#64) 5 ∗ (∃∗ u13 : BitVec 64, (p + 13#64) ↦₆₄ u13) := by
  rw [← ProofLib.memRegion_eight (p + 13#64),
      ← ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 5) (b' :=
        p + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (p + 8#64) ro8)

theorem p2_errStr_21_rejoin_entails (p ro0 ro13 : BitVec 64) :
    (p ↦₆₄ ro0) ∗ memRegion (p + 8#64) 5 ∗ ((p + 13#64) ↦₆₄ ro13) ⊢
      memRegion p 21 := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 13) (b' :=
    p + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 5) (k := 8) (b' :=
        p + 13#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p ro0)
    (sepConj_mono_right (pointsTo64_entails_memRegion (p + 13#64) ro13))

theorem p2_memRegion_88_spe_split_eq (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 88 =
      (∃∗ b_400 : BitVec 8, ∃∗ u_3f8 : BitVec 64, ∃∗ u_3f0 : BitVec 64,
       ∃∗ u_3e8 : BitVec 64, ∃∗ u_3e0 : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
        ((sp + 0x3e8#64) ↦₆₄ u_3e8) ∗
        ((sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
        ((sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
        ((sp + 0x400#64) ↦₈ b_400) ∗
        memRegion (sp + 0x401#64) 15 ∗
        memRegion (sp + 0x410#64) 40) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 80) (b' :=
    sp + 0x3e8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 72) (b' :=
        sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 64) (b' :=
        sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 56) (b' :=
        sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 1) (k := 55) (b' :=
        sp + 0x401#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x401#64) (n := 15) (k := 40) (b' :=
        sp + 0x410#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x3e0#64),
      ProofLib.memRegion_eight (sp + 0x3e8#64),
      ProofLib.memRegion_eight (sp + 0x3f0#64),
      ProofLib.memRegion_eight (sp + 0x3f8#64),
      ProofLib.memRegion_one (sp + 0x400#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_speAt_badCiphertext_preKey_intro (A : RustAlloc) (sp errStrPtr : BitVec 64)
    (herr_nz : errStrPtr ≠ 0#64) :
    ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
    ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
    ((sp + 0x400#64) ↦₈ 3#8) ∗
    memRegion (sp + 0x401#64) 15 ∗
    A.live errStrPtr 21 1 ∗
    memRegion errStrPtr 21 ⊢
      speAt A [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) := by
  rw [ProofLib.memRegion_eq_exists_bytes errStrPtr 21 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro bs
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 ∗
        A.live errStrPtr 21 1 ∗
        ⌜bs.length = 21⌝ ∗ (errStrPtr ↦ₛ bs) =
      ⌜bs.length = 21⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  apply Entails.pure_left; intro hbs
  dsimp only [speAt, invalidMessageStrAt, RustHeap.vecU8, RustHeap.vecU8At, RustHeap.vecHeader]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_right bs (Entails.sepExists_right 21#64 (Entails.sepExists_right
    errStrPtr ?_))
  have h21_nat : (21#64).toNat = 21 := rfl
  have hspe24 : speWord 24 = 0x8000000000000018#64 := rfl
  have hmsg_pk : msgTypeByte MessageType.preKey = 3#8 := rfl
  have h21_sub : (21 : Nat) - 21 = 0 := rfl
  simp only [hbs, show (21#64 = 0#64) = False by decide, show (21#64 = 0) = False by decide,
    ↓reduceIte,
    h21_nat, hspe24, hmsg_pk, h21_sub,
    BitVec.ofNat_eq_ofNat, ProofLib.memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e8#64) + 8#64 = sp + 0x3f0#64 by bv_omega,
      show (sp + 0x3e8#64) + 16#64 = sp + 0x3f8#64 by bv_omega,
      show (sp + 0x3e0#64) + 32#64 = sp + 0x400#64 by bv_omega,
      show (sp + 0x3e0#64) + 33#64 = sp + 0x401#64 by bv_omega]
  rw [show ((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
        ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
        ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
        ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        A.live errStrPtr 21 1 ∗
        (errStrPtr ↦ₛ bs) ∗
        ((sp + 0x400#64) ↦₈ 3#8) ∗
        memRegion (sp + 0x401#64) 15 =
      ⌜21 ≤ 21 ∧ 21 < 2 ^ 63 ∧ errStrPtr ≠ 0#64⌝ ∗
        (((sp + 0x3e0#64) ↦₆₄ 0x8000000000000018#64) ∗
         ((sp + 0x3e8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x3f0#64) ↦₆₄ errStrPtr) ∗
         ((sp + 0x3f8#64) ↦₆₄ 21#64) ∗
         ((sp + 0x400#64) ↦₈ 3#8) ∗
         memRegion (sp + 0x401#64) 15 ∗
         A.live errStrPtr 21 1 ∗
         (errStrPtr ↦ₛ bs)) by ac_rfl]
  refine Entails.pure_right ⟨by decide, by decide, herr_nz⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem p2_kpkGetPoll_pre_intro {A : RustAlloc} {img : Obj.Image}
    {kpkKit : KyberPreKeyStoreSpec A img.base}
    {x : PreKeyPollCall} {st0 : kpkKit.KpkState} {s : State}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (henv : kpkKit.envOk s.fs.files)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hx0 : s.readReg64 .x0 = x.fut) (hx8 : s.readReg64 .x8 = x.out)
    (hid : kpkKit.getIdOk x.id) :
    kpkKit.getBoxAt x.fut x.self x.id 0#8 ∗ kpkKit.storeAt x.self st0 ∗
      memRegion x.out 88 ∗ A.pool ∗ stackAt s.sp kpkKit.getPollStack ⊢
        ((kitKpkGetPollSpecE kpkKit).inImage img).pre (x, st0) s := by
  dsimp only [Spec.inImage, kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec]
  refine Entails.pure_right ⟨hF, hsym⟩ ?_
  refine Entails.pure_right henv ?_
  refine Entails.pure_right ⟨hb, hx0, hx8, hid⟩ ?_
  exact Entails.refl _

theorem p2_bind_sepWPp_steps_frame_oom {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ |
    ⟨_, hoom⟩⟩ := hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem p2_call_inImage_nopanic_steps_frame {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx30 : s.readReg64 .x30 = ret_pc)
    (hpre : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ s' : State, Steps prog s s' → s'.pc = ret_pc → s'.status = .Running →
      s'.sp = s.sp → s'.spAligned = true → CalleeSavedPreserved s s' →
      img.FrozenLoaded s' → s'.symtab = img.symtab →
      SepWPp prog ret s' (spec.post x s s' ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp :=
  p2_call_nopanic_steps_frame (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    hF hsym hcall hpc hrun hsp hx30
    (by dsimp only [Spec.inImage]; rw [hpre, ← sepConj_assoc, pure_sepConj_pure])
    (And.intro (And.intro hF hsym) hφ) hP
    (hpan_false := fun sf => by dsimp only [Spec.inImage]; exact hpan_false sf)
    (hexit_false := fun code sf => by dsimp only [Spec.inImage]; exact hexit_false code sf)
    (hnext := fun s' hst hpc' hrun' hsp' hsp_al' hcs' hF' hsym' => by
      dsimp only [Spec.inImage]
      exact hnext s' hst hpc' hrun' hsp' hsp_al' hcs' hF' hsym')
    (hoom_false := fun sf => by dsimp only [Spec.inImage]; exact hoom_false sf)

theorem p2_drop_left_sepWPp {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P2 Q Qp) :
    SepWPp prog ret s (P1 ∗ P2) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_drop_sep_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ p2_drop_left_sepWPp h

theorem p2_rodata64_sepWPp_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s) {off : Nat}
    (h1 : libsignalSessionImage.dataOff ≤ off)
    (h2 : (off - libsignalSessionImage.dataOff) + 8 ≤ libsignalSessionImage.data.length)
    (h3 : ProofLib.ObjectLoad.noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss)
      (off - libsignalSessionImage.dataOff) 8 = true)
    (h4 : ProofLib.ObjectLoad.inLiRoData libsignalSessionImage off 8 = true)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ w : BitVec 64,
      SepWPp prog ret s (((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ w) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  let addr := img.base + BitVec.ofNat 64 off
  let bs := (libsignalSessionImage.data.drop (off - libsignalSessionImage.dataOff)).take 8
  have hbs_len : bs.length = 8 := by
    dsimp only [bs]
    rw [List.length_take_of_le (by rw [List.length_drop]; omega)]
  have hh := ProofLib.ObjectLoad.loads_rodata_holdsBytes himg hF
    (off := off) (n := 8) (bs := bs) h1 h2 h3 h4 hbs_len rfl
  obtain ⟨hRO, _⟩ := ProofLib.ObjectLoad.holdsBytes_ro hh
  rw [hbs_len] at hRO
  refine h (s.mem.read64 addr) R ?_ hL
  rw [sepConj_assoc]
  exact Satisfies.rodata64_intro hRO rfl hm

set_option maxRecDepth 2000000 in
theorem p2_missingKyber_ro0_sepWPp {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro0 : BitVec 64,
      SepWPp prog ret s
        (((img.base + bv% (ls_xref%
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗ P)
        Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_rodata64_sepWPp_intro himg hF
    (off := num% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344)))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel) (by rfl_kernel) h

set_option maxRecDepth 2000000 in
theorem p2_missingKyber_ro8_sepWPp {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro8 : BitVec 64,
      SepWPp prog ret s
        (((img.base + bv% (ls_xref%
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8) ∗ P)
        Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_rodata64_sepWPp_intro himg hF
    (off := num% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel) (by rfl_kernel) h

set_option maxRecDepth 2000000 in
theorem p2_missingKyber_ro13_sepWPp {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ ro13 : BitVec 64,
      SepWPp prog ret s
        (((img.base + bv% (ls_xref%
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
            (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13) ∗ P)
        Q Qp) :
    SepWPp prog ret s P Q Qp :=
  p2_rodata64_sepWPp_intro himg hF
    (off := num% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel) (by rfl_kernel) h

set_option maxHeartbeats 1200000 in
/-- Shared Substage P2.3 tail (`+0x0d04 -> +0x0d5c`): allocates the 21-byte
`"missing pq ciphertext"` error string, builds `SignalProtocolError::InvalidMessage`,
and drops it because `kyberCtCap ≠ 0#64`. -/
theorem stageP2_sub3_tail_kits_ext
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext)
    (hPure : StageP2PureCallees4K P A F img ext)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ sf : State,
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool ∗ stackAt sp stk ∗ Frame)
        Q (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗
       ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗
       ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗
       memRegion (sp + 0x3e0#64) 88 ∗
       A.pool ∗ stackAt sp stk ∗ Frame)
      Q (PanicOomProp s0) := by
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hs_align : (s.sp &&& 15#64 == 0#64) = true := by rw [hsp]; exact hsp_align
  have hstep8 := p2_seg3d2_alloc_hooks_ok img img.base ext hH s0 s hF hsym hpc hrun hs_align htr hx0 hx1
  rw [hsp] at hstep8
  refine p2_bind_sepWPp_steps_frame_oom hstep8 (by sep_focus)
    fun s8 hst08 hpc8 hrun8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8, htr8, herr_nz, hx19_8, hx21_8, hx22_8, hx23_8, hx25_8, hx26_8, hx27_8,
    hx28_8, hx29_8, hvregs8, hF8, hsym8⟩
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_sp_a90_5words_entails_memRegion (sp + 0xa90#64) 0xfffffffffffffffe#64 pkBuf 0x620#64 skBuf
      0xc60#64)
    (by rw [show (sp + 0xa90#64) + 8#64 = sp + 0xa98#64 by bv_omega,
            show (sp + 0xa90#64) + 16#64 = sp + 0xaa0#64 by bv_omega,
            show (sp + 0xa90#64) + 24#64 = sp + 0xaa8#64 by bv_omega,
            show (sp + 0xa90#64) + 32#64 = sp + 0xab0#64 by bv_omega,
            show (sp + 0xa90#64) + 40#64 = sp + 0xab8#64 by bv_omega]; sep_focus) ?_
  refine p2_missingKyber_ro0_sepWPp himg hF8 fun ro0 => ?_
  refine p2_missingKyber_ro8_sepWPp himg hF8 fun ro8 => ?_
  have hstep9 := p2_seg3d2a_ext_wp img.base ext s8 coroPtr (s8.readReg64 .x0) ro0 ro8
    hb herr_nz hpc8 hrun8 rfl (hx19_8.trans hx19)
  refine p2_bind_sepWP_steps_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx8_9, hx9_9, hq0_9, hx19_9, hx21_9, hx22_9, hx23_9,
    hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, hvregs9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8.trans hsp8
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((img.base + bv% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344))) ↦₆₄ᵣ ro0) ∗
      ((img.base + bv% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 8)) ↦₆₄ᵣ ro8))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_errStr_21_split16_eq (s8.readReg64 .x0)))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_88_spe_split_eq sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u8_err => SepWPp.exists_elim fun u0_err =>
    SepWPp.exists_elim fun b_400_spe => SepWPp.exists_elim fun u_3f8_spe =>
    SepWPp.exists_elim fun u_3f0_spe => SepWPp.exists_elim fun u_3e8_spe =>
    SepWPp.exists_elim fun u_3e0_spe => ?_
  refine p2_missingKyber_ro13_sepWPp himg hF9 fun ro13 => ?_
  have hstep10 := p2_seg3d2b_ext_wp img.base ext s9 coroPtr (s8.readReg64 .x0)
    ro0 ro8 ro13 u0_err u8_err u_3f0_spe b_400_spe
    hpc9 hrun9 hsp9_align hx0_9 hx8_9 hx9_9 hq0_9 hx19_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_steps_frame hF9 hsym9 hstep10 (by sep_focus)
    fun s10 hst9_10 hpc10 hrun10 hF10 hsym10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10_9, htr10_9, hx0_10, hx8_10, hx9_10, hx19_10, hx21_10, hx22_10, hx23_10,
    hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, hvregs10_9⟩
  have hsp10 : s10.sp = sp := hsp10_9
  have hsp10_align : (s10.sp &&& 15#64 == 0#64) = true := by rw [hsp10]; exact hsp_align
  refine p2_drop_sep_frame
    (Drop := ((img.base + bv% (ls_xref%
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3340)
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 3344) + 13)) ↦₆₄ᵣ ro13))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_errStr_overlap13_entails (s8.readReg64 .x0) ro8) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u13_err => ?_
  have hx22_10' : s10.readReg64 .x22 = kyberCtCap := by
    rw [hx22_10, hx22_9, hx22_8, hx22]
  have hstep11 := p2_seg3d2c_ext_wp img.base ext s10 coroPtr (s8.readReg64 .x0)
    kyberCtCap ro13 u13_err u_3e0_spe u_3e8_spe u_3f8_spe
    hkyber_nz hpc10 hrun10 hsp10_align hx0_10 hx8_10 hx9_10 hx19_10 hx22_10'
  rw [hsp10] at hstep11
  refine p2_bind_sepWP_steps_frame hF10 hsym10 hstep11 (by sep_focus)
    fun s11 hst10_11 hpc11 hrun11 hF11 hsym11 hregs11 => ?_
  rcases hregs11 with ⟨hsp11_10, htr11_10, hx0_11, hx19_11, _, hx21_11, hx22_11, hx23_11, hx25_11,
    hx26_11, hx27_11, hx28_11, hx29_11, hx30_11, hvregs11_10⟩
  have hsp11 : s11.sp = sp := hsp11_10
  have hsp11_al : s11.spAligned = true := by simpa only [State.spAligned, hsp11] using hsp_align
  refine SepWPp.weaken_frame (p2_errStr_21_rejoin_entails (s8.readReg64 .x0) ro0 ro13)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_speAt_badCiphertext_preKey_intro A sp (s8.readReg64 .x0) herr_nz)
    (by sep_focus) ?_
  have hstk_spe := p2_stackAt_split_of_le sp stk dropSpeStack
    (Nat.le_trans p2_dropSpe_le_pure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_spe) (by sep_focus) ?_
  sep_norm
  refine p2_call_inImage_nopanic_steps_frame
    (x := ⟨sp + 0x3e0#64, [], .invalidMessage .preKey .badCiphertext⟩)
    (φ := s11.readReg64 .x0 = sp + 0x3e0#64)
    (T := speAt A [] (sp + 0x3e0#64) (.invalidMessage .preKey .badCiphertext) ∗
      A.pool ∗ stackAt sp dropSpeStack)
    hF11 hsym11 hPure.dropSpe2 hpc11 hrun11 hsp11_al hx30_11
    (by dsimp only [dropSpeSpec]; rw [hsp11])
    hx0_11 (by sep_focus)
    (hnext := fun sf hst11_f hpcf hrunf hspf_11 _ hcsf hFf hsymf => ?_)
  dsimp only [dropSpeSpec]
  rcases hcsf with ⟨hcsf_19, _, hcsf_21, hcsf_22, hcsf_23, _, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_11⟩
  rw [hsp11]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htrf_11 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_spe.symm) (by sep_focus) ?_
  have hmr88_rejoin :
      memRegion (sp + 0x3e0#64) 48 ∗ memRegion (sp + 0x410#64) 40 =
        memRegion (sp + 0x3e0#64) 88 :=
    (ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 48) (k := 40)
      (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hmr88_rejoin) (by sep_focus) ?_
  have hsteps_all :=
    hst08.trans (hst89.trans (hst9_10.trans (hst10_11.trans hst11_f)))
  have hok := hOk sf hsteps_all hpcf hrunf (hspf_11.trans hsp11)
    (by rw [htrf_11, htr11_10, htr10_9, htr9_8, htr8])
    (hcsf_19.trans hx19_11)
    (by rw [hcsf_21, hx21_11, hx21_10, hx21_9, hx21_8])
    (hcsf_22.trans hx22_11)
    (by rw [hcsf_23, hx23_11, hx23_10, hx23_9, hx23_8])
    (by rw [hcsf_25, hx25_11, hx25_10, hx25_9, hx25_8])
    (by rw [hcsf_26, hx26_11, hx26_10, hx26_9, hx26_8])
    (by rw [hcsf_27, hx27_11, hx27_10, hx27_9, hx27_8])
    (by rw [hcsf_28, hx28_11, hx28_10, hx28_9, hx28_8])
    (by rw [hcsf_29, hx29_11, hx29_10, hx29_9, hx29_8])
    (by rw [hvregsf_11, hvregs11_10, hvregs10_9, hvregs9_8, hvregs8, hvregs])
    hFf hsymf
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub3_tail_kits_4k := @stageP2_sub3_tail_kits_ext
abbrev stageP2_sub3_tail_kits_hooks := @stageP2_sub3_tail_kits_ext

theorem stageP2_sub3_tail_kits
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)} {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hPure : StageP2PureCallees P A F img ext)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_pure : stageP2PureAndErrStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (ret sp coroPtr pkBuf skBuf kyberCtCap : BitVec 64)
    (Frame : SepProp) (Q : State → SepProp → Prop)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd04#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 21#64) (hx1 : s.readReg64 .x1 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = kyberCtCap)
    (hOk : ∀ sf : State,
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s.trace →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = s.readReg64 .x21 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        (memRegion (sp + 0x3e0#64) 88 ∗ memRegion (sp + 0xa90#64) 65 ∗
         A.pool ∗ stackAt sp stk ∗ Frame)
        Q (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((sp + 0xa90#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0xa98#64) ↦₆₄ pkBuf) ∗ ((sp + 0xaa0#64) ↦₆₄ 0x620#64) ∗
       ((sp + 0xaa8#64) ↦₆₄ skBuf) ∗ ((sp + 0xab0#64) ↦₆₄ 0xc60#64) ∗
       memRegion (sp + 0xab8#64) 25 ∗ memRegion (sp + 0x3e0#64) 88 ∗
       A.pool ∗ stackAt sp stk ∗ Frame)
      Q (PanicOomProp s0) :=
  stageP2_sub3_tail_kits_ext himg (.of_allocContracts hA) hPure.to_4K hb hstk_pure hstk_lt
    s0 s ret sp coroPtr pkBuf skBuf kyberCtCap Frame Q hkyber_nz hF hsym hpc hrun hsp hsp_align
    htr hvregs hx0 hx1 hx19 hx22 hOk

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
