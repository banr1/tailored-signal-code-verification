/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3

/-!
# Stage P2 Substages 1–3 Composition

Proves `stageP2_sub1_to_3_kits_ext` and `stageP2_sub1_to_3_kits` (`+0x0868 → +0x0d5c` or error exit
to `s0.readReg64 .x30` via Arms 1–2), threading `FsAt` via `stageP2Quiet` and `calleeSavedVRegs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_ro_intro_mid {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → s.mem ⊨ Ro ∗ R)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (Ro ∗ P) ∗ R := by rw [sepConj_assoc]; exact hro hm
  exact h R hm' hL

theorem p2_drop_frame_mid {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest)
    (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_intro_spk_vt {A : RustAlloc} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {spkKit : SignedPreKeyStoreSpec A img.base} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hvt : SignedPreKeyVtablesOk img spkKit) (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine p2_ro_intro_mid (hvt.getFutPoll hF) ?_
  refine p2_ro_intro_mid (hvt.getFutAlign hF) ?_
  refine p2_ro_intro_mid (hvt.getFutSize hF) ?_
  refine p2_ro_intro_mid (hvt.getFutDrop hF) ?_
  refine p2_ro_intro_mid (hvt.getSlot hF) ?_
  exact h

theorem p2_intro_kpk_vt {A : RustAlloc} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {kpkKit : KyberPreKeyStoreSpec A img.base} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hvt : KyberPreKeyVtablesOk img kpkKit) (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff)) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine p2_ro_intro_mid (hvt.getFutPoll hF) ?_
  refine p2_ro_intro_mid (hvt.getFutAlign hF) ?_
  refine p2_ro_intro_mid (hvt.getFutSize hF) ?_
  refine p2_ro_intro_mid (hvt.getFutDrop hF) ?_
  refine p2_ro_intro_mid (hvt.getSlot hF) ?_
  exact h

theorem p2_intro_pk_vt {A : RustAlloc} {img : Obj.Image} {prog : Program} {ret : BitVec 64}
    {s : State} {pkKit : PreKeyStoreSpec A img.base} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hvt : PreKeyVtablesOk img pkKit) (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (img.base + pkKit.getShimOff)) ∗
       ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
       ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((img.base + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + pkKit.getPollOff)) ∗ P)
      Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine p2_ro_intro_mid (hvt.getFutPoll hF) ?_
  refine p2_ro_intro_mid (hvt.getFutAlign hF) ?_
  refine p2_ro_intro_mid (hvt.getFutSize hF) ?_
  refine p2_ro_intro_mid (hvt.getFutDrop hF) ?_
  refine p2_ro_intro_mid (hvt.getSlot hF) ?_
  exact h

theorem p2_finish_err_arm {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre ArmOut Rest : SepProp} {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ ArmOut ∗ Rest) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := SepWPp.mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  exact SepWPp.done hpcf hrunf (hQ sf (ArmOut ∗ Rest) hst hpcf hrunf htrf (Entails.refl _) hΦ)

theorem p2_finish_err_arm_drop {prog : Program} {ret : BitVec 64} {s : State}
    {P ArmPre ArmOut Rest Drop Keep : SepProp} {Q Qp : State → SepProp → Prop}
    {Φ : State → Prop}
    (hArm : SepWPp prog ret s ArmPre
      (fun sf P_f => sf.trace = s.trace ∧ (P_f ⊢ ArmOut) ∧ Φ sf)
      (fun _ _ => False))
    (hP : P = ArmPre ∗ Rest)
    (hSplit : ArmOut ∗ Rest ⊢ Drop ∗ Keep)
    (hQ : ∀ sf P_f,
      Steps prog s sf → sf.pc = ret → sf.status = .Running →
      sf.trace = s.trace → (P_f ⊢ Keep) → Φ sf → Q sf P_f) :
    SepWPp prog ret s P Q Qp := by
  have hArm_re := SepWPp.mono_run hArm fun sf P_f h =>
    let ⟨htrf, hentf, hΦ⟩ := h
    And.intro hentf (And.intro htrf hΦ)
  refine p2_bind_sepWPp_steps_frame hArm_re hP fun sf hst hpcf hrunf ⟨htrf, hΦ⟩ => ?_
  refine SepWPp.weaken_frame hSplit (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  refine p2_drop_frame_mid (Drop := Drop) rfl ?_
  exact SepWPp.done hpcf hrunf (hQ sf Keep hst hpcf hrunf htrf (Entails.refl _) hΦ)

theorem p2_bind_sepWPp_oom_frame {prog : Program} {mid ret : BitVec 64}
    {s0 s : State} {P P_stage F : SepProp} {P_stage_post : State → SepProp}
    {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  have hstage' : SepWPp prog mid s P_stage
      (fun sm P_m => ∃ sm' : State, (sm' = sm ∧ Q_regs sm) ∧ (P_m ⊢ P_stage_post sm'))
      (PanicOomProp s0) :=
    SepWPp.mono_run hstage fun sm _ ⟨hent, hregs⟩ => ⟨sm, ⟨rfl, hregs⟩, hent⟩
  exact p2_bind_sepWPp_exists_frame hstage' hP fun sm' sm hst hpcm hrunm ⟨heq, hregs⟩ => by
    cases heq
    exact hnext sm' hst hpcm hrunm hregs

theorem p2_bytes7_937_to_cells8_930 (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At (sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (sp + 0x937#64) 57 ⊢
      cells (sp + 0x930#64) 8 := by
  rw [p2_cells8_930_split_7_57 sp]
  exact sepConj_mono_left (p2_bytes7At_to_memRegion7 (sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6)

theorem p2_pt64_to_bytes7_1 (p u : BitVec 64) :
    (p ↦₆₄ u) ⊢
      ∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
      ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 := by
  refine Entails.trans (pointsTo64_entails_memRegion p u) ?_
  rw [ProofLib.memRegion_split p 7 1 (by decide)]
  refine Entails.trans (sepConj_mono_left (p2_memRegion7_to_bytes7At p)) ?_
  sep_norm
  exact Entails.refl _

theorem p2_bytes7_1_to_pt64 (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    bytes7At p b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (p + 7#64) 1 ⊢
      ∃∗ u : BitVec 64, (p ↦₆₄ u) := by
  refine Entails.trans (sepConj_mono_left (p2_bytes7At_to_memRegion7 p b0 b1 b2 b3 b4 b5 b6)) ?_
  rw [← ProofLib.memRegion_split p 7 1 (by decide), ProofLib.memRegion_eight p]
  exact Entails.refl _

theorem p2_pt64_to_memRegion7_1 (p u : BitVec 64) :
    (p ↦₆₄ u) ⊢ memRegion p 7 ∗ memRegion (p + 7#64) 1 := by
  rw [← ProofLib.memRegion_split p 7 1 (by decide)]
  exact pointsTo64_entails_memRegion p u

theorem p2_memRegion7_1_to_pt64 (p : BitVec 64) :
    memRegion p 7 ∗ memRegion (p + 7#64) 1 ⊢ ∃∗ u : BitVec 64, (p ↦₆₄ u) := by
  rw [← ProofLib.memRegion_split p 7 1 (by decide), ProofLib.memRegion_eight p]
  exact Entails.refl _

theorem p2_logOff_eq (img : Obj.Image) :
    logOff img =
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
  rfl

theorem p2_sepWPp_frame_eq {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hw : SepWPp prog target s P' Q Qp)
    (hP : P = P') :
    SepWPp prog target s P Q Qp :=
  hP ▸ hw

theorem p2_keyPair64UnalignedAt_to_memRegion (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b63 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    keyPair64UnalignedAt a b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ⊢
      memRegion a 64 := by
  dsimp only [keyPair64UnalignedAt]
  have hm := sepConj_mono (p2_bytes7At_to_memRegion7 a b0 b1 b2 b3 b4 b5 b6)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x07#64) w0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x0f#64) w1)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x17#64) w2)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x1f#64) w3)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x27#64) w4)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x2f#64) w5)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 0x37#64) w6)
      (pointsTo8_entails_memRegion (a + 0x3f#64) b63))))))))
  have heq :
      memRegion a 7 ∗ (memRegion (a + 0x07#64) 8 ∗ (memRegion (a + 0x0f#64) 8 ∗
      (memRegion (a + 0x17#64) 8 ∗ (memRegion (a + 0x1f#64) 8 ∗ (memRegion (a + 0x27#64) 8 ∗
      (memRegion (a + 0x2f#64) 8 ∗ (memRegion (a + 0x37#64) 8 ∗ memRegion (a + 0x3f#64) 1))))))) =
      memRegion a 64 := by
    rw [← ProofLib.memRegion_split' (b := a + 0x37#64) (n := 8) (k := 1)
          (b' := a + 0x3f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x2f#64) (n := 8) (k := 9)
          (b' := a + 0x37#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x27#64) (n := 8) (k := 17)
          (b' := a + 0x2f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x1f#64) (n := 8) (k := 25)
          (b' := a + 0x27#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x17#64) (n := 8) (k := 33)
          (b' := a + 0x1f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x0f#64) (n := 8) (k := 41)
          (b' := a + 0x17#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a + 0x07#64) (n := 8) (k := 49)
          (b' := a + 0x0f#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := a) (n := 7) (k := 57)
          (b' := a + 0x07#64) rfl (by bv_omega) (by decide)]
  exact heq ▸ hm

set_option maxHeartbeats 1200000 in
/-- Kit-generic Stage P2 Substages 1–3 (`+0x0868 -> +0x0d5c` or error exit to `s0.readReg64 .x30`):
Composes `stageP2_sub1_kits_ext`, `stageP2_sub2_kits_ext` (discharging Arm 1 via `p2_arm1_err_hooks_ok`),
and `stageP2_sub3_kits_ext` (discharging Arm 2 via `p2_arm2_err_hooks_ok`), threading `FsAt` via
`stageP2Quiet` and `calleeSavedVRegs` under `StageP2ClosureHooks` and `StageP2PureCallees4K`. -/
theorem stageP2_sub1_to_3_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext) (hPure : StageP2PureCallees4K P A F img ext)
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A img.base)
    (hspkVt : SignedPreKeyVtablesOk img spkKit) (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hkpkVt : KyberPreKeyVtablesOk img kpkKit) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (pkKit : PreKeyStoreSpec A img.base)
    (stk : Nat) (hstk_p2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hb : img.base &&& 0xfff#64 = 0#64) (hkyber_nz : kyberCtCap ≠ 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = ikit.id_vt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt)
    (hErrSpk : ∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (pkBuf skBuf kyberFutPtr v90 privCap privPtr : BitVec 64) (s3 : State),
      Steps (tripleRatchetProgAtExt img.base ext) s s3 →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s3 →
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
      s3.status = .Running → s3.sp = sp →
      s3.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) →
      s3.readReg64 .x19 = coroPtr → s3.readReg64 .x21 = msgPtr + 0x90#64 →
      s3.readReg64 .x22 = kyberCtCap → s3.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s3.readReg64 .x25 = sp + 0x210#64 → s3.readReg64 .x26 = coroPtr + 0x398#64 →
      s3.readReg64 .x27 = ctxPtr → s3.readReg64 .x28 = sp + 0xa90#64 →
      s3.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s3 = calleeSavedVRegs s0 →
      img.FrozenLoaded s3 → s3.symtab = img.symtab →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
         memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
           idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
         ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 88 ∗
         memRegion (sp + 0x438#64) 280 ∗ cells (sp + 0x930#64) 8 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkKit.storeAt spkStorePtr stSpk ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗
       ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
       cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
      Q Qp := by
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp_eq ▸ hsp_align
  have hstk_pure : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans (p2_pure_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc : allocHookStack ≤ stk :=
    Nat.le_trans (p2_allocHookStack_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2
  have hstk_alloc_split := p2_stackAt_split_of_le sp stk allocHookStack hstk_alloc hstk_lt
  refine p2_intro_spk_vt hspkVt hF ?_
  refine p2_intro_kpk_vt hkpkVt hF ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_9_79 sp)) (by sep_focus) ?_
  have hsub1 := stageP2_sub1_kits_ext (P := P) (A := A) (F := F) img ext hH hPure spkKit hspkOk
    stk hstk_pure (Nat.le_trans (p2_spkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
    s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
    preKeyStorePtr pkKit.pk_vt spkStorePtr kyberStorePtr kpkKit.kpk_vt
    baseKey signedPreKeyId b_4f1 hb hF hsym hpc hrun hsp_align_s htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  rw [hsp_eq] at hsub1
  refine p2_bind_sepWPp_oom_frame_qpan hpan hsub1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx19_1, _, _, _, hx25_1, _, _, _, hx29_1,
    hvregs1, hF1, hsym1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hsp_align
  have hfs1 := hfs.of_steps hst01 (evs := []) (by rw [htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  sep_norm
  refine SepWPp.exists_elim fun spkFutPtr => SepWPp.pure_elim fun ⟨hx0_1, hx1_1, _, _⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_9_79 sp).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells2_4f8_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  refine SepWPp.weaken_frame (p2_cells8_398_to_keyPair64UnalignedAt coroPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun c0_i => SepWPp.exists_elim fun c1_i =>
    SepWPp.exists_elim fun c2_i => SepWPp.exists_elim fun c3_i =>
    SepWPp.exists_elim fun c4_i => SepWPp.exists_elim fun c5_i =>
    SepWPp.exists_elim fun c6_i => SepWPp.exists_elim fun c63_i =>
    SepWPp.exists_elim fun cw0_i => SepWPp.exists_elim fun cw1_i =>
    SepWPp.exists_elim fun cw2_i => SepWPp.exists_elim fun cw3_i =>
    SepWPp.exists_elim fun cw4_i => SepWPp.exists_elim fun cw5_i =>
    SepWPp.exists_elim fun cw6_i => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_930_split_7_57 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_memRegion7_to_bytes7At (sp + 0x930#64)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s6_b => ?_
  let Drop_vt : SepProp :=
    ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getShimOff)) ∗
    ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
    ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
    ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + spkKit.getPollOff)) ∗
    ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getShimOff)) ∗
    ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
    ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
    ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((img.base + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kpkKit.getPollOff))
  refine p2_sepWPp_frame_eq
    (stageP2_sub2_kits_ext (P := P) (A := A) (F := F) img ext hH hPure
      spkKit hspkOk kpkKit hkpkOk stk hstk_pure
      (Nat.le_trans (p2_spkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2)
      (Nat.le_trans (p2_kpkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
      (s0.readReg64 .x30) s0 s1 _ Q hpan
      coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
      (coroPtr + 0x4f2#64) v_b0 u_90 u_b8 u_d0 u_4f8 u_500
      signedPreKeyId kyberPreKeyId stSpk
      s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i
      hb hF1 hsym1 (fun sm hst htrm => p2_envOk_spk hfs1 hst htrm) hid_spk hspk_wf hkyber_nz
      hpc1 hrun1 hsp1_align (htr1 ▸ htr) hvregs1 hx0_1 hx1_1 hx19_1 ?_ ?_)
    (by rw [hsp1]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
  · -- Arm 1: spkKit .error e at +0x0f38
    intro e s2 _ hrel_spk hpc2 hrun2 hsp2 htr2_1 hx19_2 hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ _
      hvregs2 hF2 hsym2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_errArm (A := A) coroPtr)) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc_split) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (p2_bytes7_937_to_cells8_930 sp s0_b s1_b s2_b s3_b s4_b s5_b s6_b) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (Entails.trans (p2_keyPair64UnalignedAt_to_memRegion (coroPtr + 0x398#64)
        c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i)
        (Entails.of_eq (ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide))))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
      (by sep_focus) ?_
    have harm1 := p2_arm1_err_hooks_ok (Qp := fun _ _ => False) hH hspkOk s0 s2
      sp coroPtr outPtr 0#64 8#64 spkStorePtr spkFutPtr ctxPtr
      v_b0 u_90 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 u_b8 ctxPtr u_d0
      signedPreKeyId b_2c0 b_390 b_4f2 e hb (by decide) ⟨hF2, hsym2⟩ hsp2
      hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2 (hx25_2.trans hx25_1) hx26_2 hx27_2 hvregs2
    refine p2_finish_err_arm_drop (Drop := Drop_vt) harm1 (by sep_focus) ?_
      (fun sf P_f _ hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
        hErrSpk e spkFutPtr sf P_f hrel_spk hpcf hrunf (by rw [htrf, htr2_1, htr1])
          hspf hcsf hvregsf hinvf hent)
    dsimp only [Drop_vt]
    rw [hstk_alloc_split]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  · -- Substage 2 .ok -> Substage 3: +0x1460 -> +0x0d5c or Arm 2 (+0x0998)
    intro spkRec spkPubBytes spkPrivBytes
      v90_2 privCap_2 privPtr_2 _ kyberFutPtr
      b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
      w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
      s2 hst12 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
      hpub_words hpriv_words hkp_lo hkp_hi
      hpc2 hrun2 hsp2 htr2_1 hx0_2 hx1_2 _ _
      hx19_2 _ hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ hx29_2
      hvregs2 hF2 hsym2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hst02 : Steps (tripleRatchetProgAtExt img.base ext) s s2 := hst01.trans hst12
    have hfs2 := p2_fsAt_step_spk signedPreKeyId (.ok spkRec) hfs1 hst12 htr2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_keyPair64UnalignedAt_eq_bytes32_pair (coroPtr + 0x398#64)
        spkPubBytes spkPrivBytes
        b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
        w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
        hpub_words hpriv_words hkp_lo hkp_hi))
      (by sep_focus) ?_
    sep_norm
    refine SepWPp.weaken_frame
      (p2_bytes7_937_to_cells8_930 sp b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (p2_cells4_3d8_eq coroPtr)) (by sep_focus) ?_
    sep_norm
    refine SepWPp.exists_elim fun u_3d8 => SepWPp.exists_elim fun u_3e0 =>
      SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 => ?_
    refine p2_sepWPp_frame_eq
      (stageP2_sub3_kits_ext (P := P) (A := A) (F := F) img ext himg hH hPure
        kpkKit hkpkOk stk hstk_pure
        (Nat.le_trans (p2_kpkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_p2) hstk_lt
        (s0.readReg64 .x30) s0 s2 _ Q hpan
        coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
        (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 spkFutPtr (img.base + spkKit.getFutVtOff)
        v90_2 u_a8 privCap_2 ctxPtr privPtr_2
        u_3d8 u_3e0 u_3e8 u_3f0
        kyberPreKeyId 0#8 stKpk
        hb hkyber_nz hF2 hsym2 (fun sm hst htrm => p2_envOk_kpk hfs2 hst htrm) hid_kpk hkpk_wf
        hpc2 hrun2 hsp2_align
        (by rw [htr2_1, htr1]; exact htr.trans (List.prefix_append _ _))
        hvregs2 hx0_2 hx1_2 hx19_2 hx21_2 hx23_2 hx26_2 hx27_2 ?_ ?_)
      (by rw [hsp2]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
    · -- Arm 2: kpkKit .error e at +0x0998
      intro e s3 _ hrel_kpk hpc3 hrun3 hsp3 htr3_2 hx19_3 hx21_3 hx23_3 hx25_3 hx26_3 hx27_3 _ _
        hvregs3 hF3 hsym3
      try rw [hsp2] at hsp3
      try rw [hsp2]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hsp_align
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_sessionRecordEmptyHeaderAt_errArm (A := A) coroPtr)) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc_split) (by sep_focus) ?_
      have h3d8_fold :
          ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ⊢
          cells (coroPtr + 0x3d8#64) 4 := by
        refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _)))) ?_
        rw [← ProofLib.memRegion_split' (b := coroPtr + 0x3e8#64) (n := 8) (k := 8)
              (b' := coroPtr + 0x3f0#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3e0#64) (n := 8) (k := 16)
              (b' := coroPtr + 0x3e8#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3d8#64) (n := 8) (k := 24)
              (b' := coroPtr + 0x3e0#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide)]
        exact Entails.refl _
      refine SepWPp.weaken_frame h3d8_fold (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      have harm2 := p2_arm2_err_hooks_ok (Qp := fun _ _ => False) hH hkpkOk s0 s3
        sp coroPtr outPtr 0#64 8#64 kyberStorePtr kyberFutPtr ctxPtr
        v_b0 v90_2 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 privCap_2 ctxPtr privPtr_2
        kyberPreKeyId b_2c0 b_390 0#8 b_4f2 e hb (by decide) ⟨hF3, hsym3⟩ hsp3
        hpc3 hrun3 hsp3_align hx19_3 hx21_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1]) hx26_3 hx27_3 hvregs3
      refine p2_finish_err_arm_drop (Drop := Drop_vt) harm2 (by sep_focus) ?_
        (fun sf P_f _ hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hinvf⟩ =>
          hErrKpk spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f
            hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq hrel_kpk
            hpcf hrunf (by rw [htrf, htr3_2, htr2_1, htr1])
            hspf hcsf hvregsf hinvf hent)
      dsimp only [Drop_vt]
      rw [hstk_alloc_split]
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    · -- Substage 3 .ok -> hOk at +0x0d5c
      intro kpkRec kyberPubBytes kyberPrivBytes pkBuf skBuf v90_3 privCap_3 privPtr_3 s3
        hst23 hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3 htr3_2
        hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
        hvregs3 hF3 hsym3
      try rw [hsp2] at hsp3
      try rw [hsp2] at hx28_3
      try rw [hsp2]
      have hst03 : Steps (tripleRatchetProgAtExt img.base ext) s s3 := hst02.trans hst23
      have hfs3 := p2_fsAt_step_kpk kyberPreKeyId (.ok kpkRec) hfs2 hst23 htr3_2
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      refine p2_drop_frame_mid (Drop := Drop_vt) (by dsimp only [Drop_vt]; sep_focus) ?_
      have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        pkBuf skBuf kyberFutPtr v90_3 privCap_3 privPtr_3 s3
        hst03 hfs3 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
        hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3
        (by rw [htr3_2, htr2_1, htr1])
        hx19_3 hx21_3 hx22_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1])
        hx26_3 hx27_3 hx28_3
        (by rw [hx29_3, hx29_2, hx29_1])
        hvregs3 hF3 hsym3
      exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_sub1_to_3_kits_4k := @stageP2_sub1_to_3_kits_ext

/-- Kit-generic Stage P2 Substages 1–3 (`+0x0868 -> +0x0d5c` or error exit to `s0.readReg64 .x30`). -/
theorem stageP2_sub1_to_3_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext) (hPure : StageP2PureCallees P A F img ext)
    {ikit : IdentityStoreSpec A img.base} (skit : IdentitySelfStoreSpec ikit) :
    ∀ (spkKit : SignedPreKeyStoreSpec A img.base),
      SignedPreKeyVtablesOk img spkKit → SignedPreKeyStoreKitOkImgE img spkKit ext →
      ∀ (kpkKit : KyberPreKeyStoreSpec A img.base),
      KyberPreKeyVtablesOk img kpkKit → KyberPreKeyStoreKitOkImgE img kpkKit ext →
      ∀ (pkKit : PreKeyStoreSpec A img.base)
        (stk : Nat), stageP2CallStack spkKit kpkKit pkKit skit ≤ stk → stk ≤ 2 ^ 64 →
      ∀ (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
        {Qp : State → SepProp → Prop} (_hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
        (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
         idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
         v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
        (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
        (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
        (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8),
      img.base &&& 0xfff#64 = 0#64 → kyberCtCap ≠ 0#64 →
      img.FrozenLoaded s → s.symtab = img.symtab →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s →
      spkKit.idOk signedPreKeyId →
      (∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
        spkKit.RecOk r →
        ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
          spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
          r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes) →
      kpkKit.getIdOk kyberPreKeyId →
      (∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
        kpkKit.RecOk r →
        ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
          kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
          r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
          r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes) →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64 →
      s.status = .Running → s.sp = sp →
      (sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x8 = kyberStorePtr → s.readReg64 .x9 = msgPtr →
      s.readReg64 .x10 = kpkKit.kpk_vt → s.readReg64 .x11 = preKeyStorePtr →
      s.readReg64 .x12 = remoteAddrPtr → s.readReg64 .x13 = pkKit.pk_vt →
      s.readReg64 .x14 = localAddrPtr → s.readReg64 .x15 = idStorePtr →
      s.readReg64 .x16 = ikit.id_vt → s.readReg64 .x19 = coroPtr →
      s.readReg64 .x22 = spkStorePtr → s.readReg64 .x23 = coroPtr + 0xe0#64 →
      s.readReg64 .x24 = spkKit.spk_vt →
      (∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
        spkKit.getRel stSpk signedPreKeyId (.error e) →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
        sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (P_f ⊢
          speErrAt spkKit.getErr outPtr e ∗
          spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
          kpkKit.storeAt kyberStorePtr stKpk ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
          cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
        Q sf P_f) →
      (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
        spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
        spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
        spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
        spkRec.signedPreKey.privateKey = spkPrivBytes →
        kpkKit.getRel stKpk kyberPreKeyId (.error e) →
        sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
          kpkKit.getEvs kyberPreKeyId (.error e) →
        sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → ImgCallInv img sf →
        (P_f ⊢
          speErrAt kpkKit.getErr outPtr e ∗
          spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
          kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
          ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
          cells (coroPtr + 0x3d8#64) 4 ∗
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
          cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
        Q sf P_f) →
      (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (pkBuf skBuf kyberFutPtr v90 privCap privPtr : BitVec 64) (s3 : State),
        Steps (tripleRatchetProgAtExt img.base ext) s s3 →
        FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
          (stageP2Quiet spkKit kpkKit pkKit skit) (tripleRatchetProgAtExt img.base ext) s3 →
        spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
        spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
        spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
        spkRec.signedPreKey.privateKey = spkPrivBytes →
        kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
        kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
        kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
        kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
        pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
        s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xd5c#64 →
        s3.status = .Running → s3.sp = sp →
        s3.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
          kpkKit.getEvs kyberPreKeyId (.ok kpkRec) →
        s3.readReg64 .x19 = coroPtr → s3.readReg64 .x21 = msgPtr + 0x90#64 →
        s3.readReg64 .x22 = kyberCtCap → s3.readReg64 .x23 = coroPtr + 0x4f2#64 →
        s3.readReg64 .x25 = sp + 0x210#64 → s3.readReg64 .x26 = coroPtr + 0x398#64 →
        s3.readReg64 .x27 = ctxPtr → s3.readReg64 .x28 = sp + 0xa90#64 →
        s3.readReg64 .x29 = s.readReg64 .x29 →
        calleeSavedVRegs s3 = calleeSavedVRegs s0 →
        img.FrozenLoaded s3 → s3.symtab = img.symtab →
        SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
          (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
           kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
           (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
           (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
           ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
           memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
           ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
           ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
           ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
           ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
           ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
           processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
             idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
           ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
           ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
           ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
           ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
           ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
           ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
           ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
           ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ 3169#64) ∗
           ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ privCap) ∗
           ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
           ((sp + 0xd0#64) ↦₆₄ privPtr) ∗
           memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 88 ∗
           memRegion (sp + 0x438#64) 280 ∗ cells (sp + 0x930#64) 8 ∗
           memRegion (sp + 0xa90#64) 65 ∗
           decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
           memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
          Q Qp) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
        (spkKit.storeAt spkStorePtr stSpk ∗
         kpkKit.storeAt kyberStorePtr stKpk ∗
         ResponderClosure.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
         memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
         cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
         ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
         cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp stk ∗ Frame)
        Q Qp :=
  stageP2_sub1_to_3_kits_ext img ext himg
    (StageP2ClosureHooks.of_allocContracts hA) hPure.to_4K skit

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
