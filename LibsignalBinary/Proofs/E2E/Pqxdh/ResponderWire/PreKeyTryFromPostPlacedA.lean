/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPost
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp

/-!
# Relocatable `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Post-Loop Part A

Proves the shared vector-deallocation tails (`+2060 .. +2648` → `+1284`) and post-loop Segment 1
(`+1120 .. +1476` → `+1668`) for Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8

noncomputable abbrev preKeyPlacedProg [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  (blkPC_111).rebase (blkPl_111).base H

abbrev KeepsFrozenInv (Inv : Memory → Prop) : Prop :=
  ∀ ⦃m m' : Memory⦄, Inv m → m.KeepsFrozen m' → Inv m'

theorem keepsFrozenInv_codeLoaded [LibsignalPlacement] :
    KeepsFrozenInv (LibsignalCodeLoaded lsmpl) :=
  fun _ _ h hk => h.of_keepsFrozen hk

theorem keepsFrozenInv_codeRoLoaded [LibsignalPlacement] :
    KeepsFrozenInv (LibsignalCodeRoLoaded lsmpl) :=
  fun _ _ h hk => h.of_keepsFrozen hk

abbrev withPreKeyInv {α : Type} (Inv : Memory → Prop) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜Inv s0.mem⌝ }

theorem extract_withPreKeyInv {α : Type} {Inv : Memory → Prop} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withPreKeyInv Inv spec).pre x s0 ∗ R) :
    Inv s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withPreKeyInv] at hpre
  rwa [sepConj_comm (spec.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withPreKeyInv_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {Inv : Memory → Prop} {spec : Spec α} (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withPreKeyInv Inv spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withPreKeyInv hp).2) (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withPreKeyInv_of_cl [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64}
    {Inv : Memory → Prop} (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {spec : Spec α} (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withPreKeyInv Inv spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hinv, hpre⟩ := extract_withPreKeyInv hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_comm (spec.pre _ s0), sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hcl_of_inv s0.mem hinv, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem ls_subroutine_ok_pk_of_cl [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {Inv : Memory → Prop} (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withPreKeyInv Inv spec) :=
  subroutine_ok_withPreKeyInv_of_cl hcl_of_inv
    (ls_subroutine_ok_of_block (callerProg := callerProg) hcallee hi hj hj_unmut)

theorem ls_subroutine_ok_pk_of_plain [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {Inv : Memory → Prop} (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withPreKeyInv Inv spec) :=
  ls_subroutine_ok_pk_of_cl hcl_of_inv
    (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut

theorem panic_at_prekey_placed [LibsignalPlacement] {H : LibsignalHooks}
    (h_panic : H lsAllocHandleErrorSym = some Rust.panicked) :
    (preKeyPlacedProg H).externAt? ((blkPl_111).ρ lsAllocHandleErrorSym) =
      some Rust.panicked :=
  new_externAt?_handle_alloc_error h_panic

theorem SepWPp.of_sepWP_pk {prog : Program} {ret mid : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s : Arm64.State} {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog mid s P (fun sm Pm =>
      VRegsAt s sm ∧ (Inv sm.mem → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hv, hnext⟩ | hoom⟩
  · have hinv_m := hkf hinv hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc, hrun, Pf, hmf, hq, hvf⟩ | hpan⟩ :=
      hnext hinv_m R hmm (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc, hrun, Pf, hmf, hq, hvf.trans hv.eq⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpan⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem SepWPp.of_sepWP_end_pk {prog : Program} {ret : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s0 s : Arm64.State} {P : SepProp} {Q : Arm64.State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : ProofLib.SepWP prog ret s P (fun sf Pf =>
      VRegsAt s sf ∧ (Inv sf.mem → Q sf Pf))) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hv, hq⟩ | ⟨_, hoom⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf,
      hq (hkf hinv hsteps.keepsFrozen), hv.eq⟩⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem SepWPp.call_noPanic_pk {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withPreKeyInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hinv : Inv s.mem) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → Inv sf.mem →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withPreKeyInv Inv spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withPreKeyInv]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withPreKeyInv] at hpost
    have hinv_m := hkf hinv hsteps.keepsFrozen
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hinv_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withPreKeyInv] at hpost
    rw [hpan sm] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withPreKeyInv] at hpost
    rw [hexit sm code] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withPreKeyInv] at hpost
    rw [hoom sm] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem SepWPp.call_tryFrom_pk {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (withPreKeyInv Inv spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      sf.spAligned = true → Inv sf.mem →
      CalleeSavedPreserved s sf → SepWPp prog ret sf (spec.post x s sf ∗ F) Q (tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) :=
      by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q (tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withPreKeyInv Inv spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withPreKeyInv]
    rw [hspec]
    have hcomm : ((⌜φ⌝ ∗ T) ∗ ⌜Inv s.mem⌝) ∗ (F ∗ R') =
        ⌜φ⌝ ∗ (⌜Inv s.mem⌝ ∗ ((T ∗ F) ∗ R')) := by ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [satisfies_pure_sepConj, ← hP]
    exact ⟨hinv, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ := hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · dsimp only [withPreKeyInv] at hpost
    rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    have hinv_m := hkf hinv hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hinv_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [withPreKeyInv] at hpost
    rw [← sepConj_assoc, hpan sm] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, tryFromQp_of_call htr⟩)⟩
  · dsimp only [withPreKeyInv] at hpost
    rw [hexit sm code] at hpost; exact (allowPanic_not_exited hpost).elim
  · dsimp only [withPreKeyInv] at hoom
    rw [hoom_eq sm] at hoom; exact (not_satisfies_false_sepConj hoom).elim

def PreKeyPostState (Inv : Memory → Prop) (s0 : State) (sp' : BitVec 64) (s : State) : Prop :=
  s.sp = sp' ∧ s.spAligned = true ∧ Inv s.mem ∧ s.trace = s0.trace

theorem PreKeyPostState.of_steps {Inv : Memory → Prop} {s0 s1 s2 : State} {sp' : BitVec 64}
    (hinv : Inv s2.mem) (hsp : s2.sp = sp') (hsp0 : s1.sp = sp') (hal : s1.spAligned = true)
    (htr : s2.trace = s0.trace) :
    PreKeyPostState Inv s0 sp' s2 := by
  refine ⟨hsp, ?_, hinv, htr⟩
  rw [State.spAligned, hsp, ← hsp0, ← State.spAligned]
  exact hal

def PreKeyDeallocOk [LibsignalPlacement] (Inv : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) ((blkPl_111).ρ lsRustDeallocSym)
    (withPreKeyInv Inv (rustDeallocSpec A))

theorem preKeyDeallocOk_of_hookSat [LibsignalPlacement] {Inv : Memory → Prop} {A : RustAlloc}
    {H : LibsignalHooks} (hsat : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    PreKeyDeallocOk Inv A H :=
  subroutine_ok_withPreKeyInv_of_plain (ls_hook_ok_of_mem hsat)

def PreKeyDropSpeOk [LibsignalPlacement] (Inv : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 5)
    (withPreKeyInv Inv (Getters.dropSpeSpec A))

/-! ## Shared Cleanup Tails (`+2060 .. +2648` → `+1284`) -/

theorem cleanup_33c_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
    {s0 s : State} {sp' ptr cap : BitVec 64} (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2060#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = ptr) (hx1 : s.readReg64 .x1 = cap)
    (_hpos : 0 < cap.toNat) (_hlt : cap.toNat < 2 ^ 63) (_hptr : ptr ≠ 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧ (Pf ⊢ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  refine SepWPp.call_noPanic_pk hkf (ptr, cap.toNat, 1) hdealloc
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2068#64) (by simp_all [arm64_norm])
    (T := A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗ stackAt s.sp allocHookStack)
    (φ := s.readReg64 (Reg.gpr 0#5) = ptr ∧ (s.readReg64 (Reg.gpr 1#5)).toNat = cap.toNat ∧
      (1#64 : BitVec 64).toNat = 1)
    (by simp [rustDeallocSpec, arm64_norm])
    ⟨hx0, by simp [hx1], rfl⟩ (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 _
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  refine SepWPp.of_sepWP_end_pk hkf hinv2 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv3
  refine ⟨PreKeyPostState.of_steps hinv3 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
    (by simp [htr2, htr, arm64_norm]), ?_⟩
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl

theorem cleanup_57c_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
    {s0 s : State} {sp' bkCap bkPtr : BitVec 64} (bk : List (BitVec 8))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2636#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hnext := @cleanup_33c_placed_wp _ Inv hkf A H hdealloc s0
  by_cases hcap : bkCap = 0#64
  · clear hnext
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_end_pk hkf hinv ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    exact ⟨PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
      (by simp [htr, arm64_norm]), Entails.refl _⟩
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A bkCap bkPtr bk
        hcap)))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2060#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    refine SepWPp.mono_pre
      (P' := (A.live bkPtr bkCap.toNat 1 ∗ memRegion bkPtr bkCap.toNat ∗ A.pool ∗
        stackAt sp' smallRootStack) ∗ (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap)))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp [arm64_norm]) (by simp_all [arm64_norm]) hpos hlt hptr)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl

theorem cleanup_568_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
    {s0 s : State} {sp' ikCap ikPtr bkCap bkPtr : BitVec 64} (ik bk : List (BitVec 8))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2616#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hnext := @cleanup_57c_placed_wp _ Inv hkf A H hdealloc s0
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  by_cases hcap : ikCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2636#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack) ∗ ((sp' +
          104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · refine SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (vecU8Buf_dealloc A ikCap ikPtr ik hcap))))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    refine SepWPp.call_noPanic_pk hkf (ikPtr, ikCap.toNat, 1) hdealloc
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hsp) hinv1
      (ret_pc := (blkPl_111).base + 2636#64) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live ikPtr ikCap.toNat 1 ∗ memRegion ikPtr ikCap.toNat ∗
        stackAt s.sp allocHookStack)
      (φ := ikPtr = ikPtr ∧ ikCap.toNat = ikCap.toNat ∧ (1#64 : BitVec 64).toNat = 1)
      (by simp_all [rustDeallocSpec, arm64_norm])
      ⟨rfl, rfl, rfl⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 _
    dsimp only [rustDeallocSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack) ∗ ((sp' +
          104#64) ↦₆₄ ikPtr))
      (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hnext bk (PreKeyPostState.of_steps hinv2 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
        (by simp [htr2, htr, arm64_norm])) hpc2 hrun2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl

theorem cleanup_558_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hcap : msgCap ≠ 0#64) (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2600#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hnext := @cleanup_568_placed_wp _ Inv hkf A H hdealloc s0
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A msgCap msgPtr msg hcap)))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun ⟨hpos, hlt, hptr⟩ => ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  refine SepWPp.call_noPanic_pk hkf (msgPtr, msgCap.toNat, 1) hdealloc
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2616#64) (by simp_all [arm64_norm])
    (T := A.pool ∗ A.live msgPtr msgCap.toNat 1 ∗ memRegion msgPtr msgCap.toNat ∗
      stackAt s.sp allocHookStack)
    (φ := msgPtr = msgPtr ∧ msgCap.toNat = msgCap.toNat ∧ (1#64 : BitVec 64).toNat = 1)
    (by simp_all [rustDeallocSpec, arm64_norm])
    ⟨rfl, rfl, rfl⟩ (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨_, _, _, _, hx23_cs, _⟩
  have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, hx23, arm64_norm]
  refine SepWPp.mono_pre
    (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
        stackAt sp' smallRootStack) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr))
    (by apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (hnext ik bk (PreKeyPostState.of_steps hinv2 (by tryFromPost_sp [hsp2, hsp_eq]) hsp_eq hsp
        (by simp [htr2, htr, arm64_norm]))
      hpc2 hrun2 hx23_2)
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl

theorem cleanup_554_placed_wp [LibsignalPlacement] {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8)) (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2596#64)
    (hrun : s.status = .Running) (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧ (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' +
        88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have h558 := @cleanup_558_placed_wp _ Inv hkf A H hdealloc s0
  have h568 := @cleanup_568_placed_wp _ Inv hkf A H hdealloc s0
  by_cases hcap : msgCap = 0#64
  · clear h558
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗
          stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (h568 ik bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm])) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp [hx23, arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · clear h568
    have hbeq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    exact h558 msg ik bk hcap
      (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp (by simp [htr,
        arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp [hx23, arm64_norm]) (by simp [hx26, arm64_norm])

/-! ## Segment 1 (`+1120 .. +1476` → `+1668`) -/

theorem post_seg1a_f90_to_0ac_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hDropSpe : PreKeyDropSpeOk Inv A H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {opkVal : BitVec 32}
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hinv : Inv s.mem)
    (htr : s.trace = s0.trace) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1404#64) s
      (memRegion (sp' + 16#64) 96 ∗ vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧ kyberCap.toNat < 2 ^ 63 ∧ bkCap.toNat < 2 ^ 63 ∧
        ikCap.toNat < 2 ^ 63 ∧ msgCap.toNat < 2 ^ 63 ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 312#64) 48 ∗
          memRegion (sp' + 360#64) 72 ∗
          memRegion (sp' + 432#64) 8 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗ A.pool ∗
          stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have hsp_eq := hregs.sp
  have h29 := hregs.x29
  have h27 := hregs.x27
  have h22 := hregs.x22
  have h21 := hregs.x21
  have h20 := hregs.x20
  have h19 := hregs.x19
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  rw [← sepConj_assoc (vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes),
      ← sepConj_assoc (vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes),
      ← sepConj_assoc (vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes)]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion96_seg1_unpack sp') (sepConj_mono_left (post_vecU8At4_lt A
        (sp' + 312#64) kyberCap kyberPtr (sp' + 336#64) bkCap bkPtr
        (sp' + 360#64) ikCap ikPtr (sp' + 384#64) msgCap msgPtr
        x.kyberBytes x.bkBytes x.ikBytes x.inner))) ?_
  simp only [sepConj_assoc, sepExists_sepConj_left]
  refine SepWPp.exists_pre fun w16 => SepWPp.exists_pre fun w20 =>
    SepWPp.exists_pre fun w24 => SepWPp.exists_pre fun w28 =>
    SepWPp.exists_pre fun w32 => SepWPp.exists_pre fun w40 =>
    SepWPp.exists_pre fun w48 => SepWPp.exists_pre fun w52 =>
    SepWPp.exists_pre fun w56 => SepWPp.exists_pre fun w68 =>
    SepWPp.exists_pre fun w72 => SepWPp.exists_pre fun w80 =>
    SepWPp.exists_pre fun w88 => SepWPp.exists_pre fun w96 =>
    SepWPp.exists_pre fun w104 => ?_
  rw [← sepConj_assoc ((sp' + 16#64) ↦₃₂ w16), ← sepConj_assoc (_ ∗ ((sp' + 20#64) ↦₃₂ w20)),
      ← sepConj_assoc (_ ∗ ((sp' + 24#64) ↦₃₂ w24)), ← sepConj_assoc (_ ∗ ((sp' + 28#64) ↦₃₂ w28)),
      ← sepConj_assoc (_ ∗ ((sp' + 32#64) ↦₆₄ w32)), ← sepConj_assoc (_ ∗ ((sp' + 40#64) ↦₆₄ w40)),
      ← sepConj_assoc (_ ∗ ((sp' + 48#64) ↦₃₂ w48)), ← sepConj_assoc (_ ∗ ((sp' + 52#64) ↦₃₂ w52)),
      ← sepConj_assoc (_ ∗ ((sp' + 56#64) ↦₆₄ w56)),
      ← sepConj_assoc (_ ∗ memRegion (sp' + 64#64) 4),
      ← sepConj_assoc (_ ∗ ((sp' + 68#64) ↦₃₂ w68)), ← sepConj_assoc (_ ∗ ((sp' + 72#64) ↦₆₄ w72)),
      ← sepConj_assoc (_ ∗ ((sp' + 80#64) ↦₆₄ w80)), ← sepConj_assoc (_ ∗ ((sp' + 88#64) ↦₆₄ w88)),
      ← sepConj_assoc (_ ∗ ((sp' + 96#64) ↦₆₄ w96)), sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun ⟨hky_lt, hbk_lt, hik_lt, hmsg_lt⟩ => ?_
  rw [vecU8At_eq_header_buf A (sp' + 312#64), vecU8At_eq_header_buf A (sp' + 336#64),
      vecU8At_eq_header_buf A (sp' + 360#64), vecU8At_eq_header_buf A (sp' + 384#64)]
  simp only [PreKeyTryFromArgs.kyberBytes_length, PreKeyTryFromArgs.bkBytes_length,
    PreKeyTryFromArgs.ikBytes_length]
  have hky_ne := cap_add2_ne_of_lt hky_lt
  have hbk_eq := cap_add1_eq_of_lt hbk_lt
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  have hw5 :
      ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
      ((sp' + 352#64) ↦₆₄ 33#64) ⊢ memRegion (sp' + 320#64) 40 := by
    simpa [words5At, BitVec.add_assoc, BitVec.reduceAdd] using
      words5At_entails_memRegion (sp' + 320#64) kyberPtr 1569#64 bkCap bkPtr 33#64
  have hhdr80 := post_headers_entails_memRegion80 sp' ikCap ikPtr msgCap msgPtr
    (BitVec.ofNat 64 x.inner.length) x.regId (opkTag x) opkVal x.spkId x.kpkId
  dsimp only [vecHeader] at hhdr80
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hhdr80
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (P' := (speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗
      stackAt s.sp dropSpeStack) ∗
      (seg1SpillsAt sp' x opkVal bkCap bkPtr msgPtr ikPtr ∗ memRegion (sp' + 360#64) 72 ∗
        memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
    (by
      rw [hspe, hstackSpe, hsp_eq]
      dsimp only [seg1SpillsAt]
      refine Entails.trans (Q :=
        (((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ 1569#64) ∗ ((sp' + 336#64) ↦₆₄ bkCap) ∗
        ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ 33#64)) ∗ (((sp' + 360#64) ↦₆₄ ikCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ 33#64) ∗
          ((sp' + 384#64) ↦₆₄ msgCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' +
          400#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗ ((sp' + 416#64) ↦₃₂ opkTag x) ∗
          ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗ ((sp' + 432#64) ↦₃₂ 1#32) ∗
          ((sp' + 436#64) ↦₃₂ x.kpkId)) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ A.pool ∗ stackAt sp' dropSpeStack ∗
          ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗
          ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
          ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₆₄ 33#64) ∗
          memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
          80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono hw5 (sepConj_mono_left hhdr80)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_pk hkf (⟨sp' + 312#64, [], .invalidProtobufEncoding⟩ : DropSpeGhost)
    hDropSpe
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 1404#64) (by simp_all [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp_all [Getters.dropSpeSpec, arm64_norm])
    rfl (by sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [Getters.dropSpeSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs⟩
  refine SepWPp.of_sepWP_end_pk hkf hinv2 ?_
  refine SepWP.done hpc2 hrun2 ?_
  intro hinv3
  refine ⟨⟨by tryFromPost_sp [hsp2, hsp_eq], hsp2_align, hinv3, by simp [htr2, htr,
    arm64_norm]⟩, hky_lt, hbk_lt, hik_lt, hmsg_lt,
    by simp [hx29_cs, h29, arm64_norm],
    by simp [hx28_cs, arm64_norm],
    by simp [hx27_cs, h27, arm64_norm],
    by simp [hx26_cs, arm64_norm],
    by simp [hx25_cs, arm64_norm],
    by simp [hx24_cs, arm64_norm],
    by simp [hx23_cs, arm64_norm],
    by simp [hx22_cs, h22, arm64_norm],
    by simp [hx21_cs, h21, arm64_norm],
    by simp [hx20_cs, h20, arm64_norm],
    by simp [hx19_cs, h19, arm64_norm], ?_⟩
  simp only [hstackSpe, hsp_eq, arm64_norm]
  apply entails_of_eq; ac_rfl

theorem post_seg1b_0ac_to_1b4_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks} (hDropSpe : PreKeyDropSpeOk Inv A H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64}
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) (hik_lt : ikCap.toNat < 2 ^ 63) (hmsg_lt : msgCap.toNat < 2 ^ 63)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx24 : s.readReg64 .x24 = 1#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1668#64) s
      (((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ memRegion (sp' + 312#64) 48 ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
        sf.readReg64 .x28 = kyberCap ∧
        sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
        sf.readReg64 .x25 = kyberPtr ∧
        sf.readReg64 .x24 = 1#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
          ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
          memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ lsLogOff ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hcallDeser := ls_subroutine_ok_pk_of_plain
    (callerProg := preKeyPlacedProg H) hcl_of_inv (deserialize_placed_ok H)
  have hik_eq := cap_add1_eq_of_lt hik_lt
  have hmsg_eq := cap_add1_eq_of_lt hmsg_lt
  have hstackSpe := stackAt_sub_split sp' dropSpeStack smallRootStack (by decide) (by decide)
  have hspe : speAt A [] (sp' + 312#64) .invalidProtobufEncoding =
      ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 := by
    simp [speAt, speWord, BitVec.reduceAdd]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (post_memRegion48_split8 (sp' +
      312#64))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  refine SepWPp.exists_pre fun w312_1 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  refine SepWPp.call_noPanic_pk hkf (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hDropSpe
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hinv1
    (ret_pc := (blkPl_111).base + 1424#64) (by simp_all [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp_all [Getters.dropSpeSpec, arm64_norm])
    rfl (by rw [hspe, hstackSpe]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [Getters.dropSpeSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h27_2 : s2.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_2, hx27, arm64_norm]
  have h26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_2, hx26, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = 1#64 := by simp [hx24_2, hx24, arm64_norm]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_2 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv3
  refine SepWPp.call_noPanic_pk hkf (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hDropSpe
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hinv3
    (ret_pc := (blkPl_111).base + 1444#64) (by simp_all [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp_all [Getters.dropSpeSpec, arm64_norm])
    rfl (by simp only [hspe, hsp_eq, arm64_norm]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hinv4 hcs4
  dsimp only [Getters.dropSpeSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr4 => ?_
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4⟩
  have hsp4_eq : s4.sp = sp' := by tryFromPost_sp [hsp4, hsp2_eq]
  have h29_4 : s4.readReg64 .x29 = sp' + 512#64 := by simp [hx29_4, h29_2, arm64_norm]
  have h27_4 : s4.readReg64 .x27 = 0x8000000000000002#64 := by simp [hx27_4, h27_2, arm64_norm]
  have h24_4 : s4.readReg64 .x24 = 1#64 := by simp [hx24_4, h24_2, arm64_norm]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w312_3 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv4 (mid := lsmpl.base 5) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv5
  refine SepWPp.call_noPanic_pk hkf (⟨sp' + 312#64, [],
    .invalidProtobufEncoding⟩ : DropSpeGhost) hDropSpe
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp4_align) hinv5
    (ret_pc := (blkPl_111).base + 1460#64) (by simp_all [arm64_norm])
    (T := speAt A [] (sp' + 312#64) .invalidProtobufEncoding ∗ A.pool ∗ stackAt sp' dropSpeStack)
    (φ := sp' + 312#64 = sp' + 312#64)
    (by simp_all [Getters.dropSpeSpec, arm64_norm])
    rfl (by simp only [hspe, hsp2_eq, arm64_norm]; sep_focus)
    ?_
  intro s6 hpc6 hrun6 hsp6 hsp6_align hinv6 hcs6
  dsimp only [Getters.dropSpeSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr6 => ?_
  rcases hcs6 with ⟨hx19_6, hx20_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, hx27_6, hx28_6,
    hx29_6⟩
  have hsp6_eq : s6.sp = sp' := by tryFromPost_sp [hsp6, hsp4_eq]
  have h29_6 : s6.readReg64 .x29 = sp' + 512#64 := by simp [hx29_6, h29_4, arm64_norm]
  refine SepWPp.mono_pre
    (P' := ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ (bkPtr ↦ₛ x.bkBytes) ∗
      vecU8Rest A bkCap bkPtr x.bkBytes ∗
      memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ lsLogOff ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [post_memRegion48_split33_15 sp']
      simp only [hstackSpe, hsp4_eq, sepConj_assoc, arm64_norm]
      refine Entails.trans
        (Q := Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ (memRegion (sp' + 312#64) 33 ∗
          memRegion (sp' + 345#64) 15 ∗
          A.pool ∗ stackAt sp' dropSpeStack ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' +
          80#64) ↦₆₄ bkPtr) ∗ lsLogOff ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - dropSpeStack)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left (vecU8Buf_to_slice_rest A bkCap bkPtr x.bkBytes)) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv6 (mid := lsmpl.base 201) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv7
  have hbk_deser : PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩ := deserialize_djb_ok x.baseKey
  have hbk_len : (33#64 : BitVec 64).toNat = x.bkBytes.length := by simp
  have hbk_lt63 : x.bkBytes.length < 2 ^ 63 := by simp
  refine SepWPp.call_noPanic_pk hkf (bkPtr, x.bkBytes, ⟨x.baseKey⟩, sp' + 312#64) hcallDeser
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp6_align) hinv7
    (ret_pc := (blkPl_111).base + 1472#64) (by simp_all [arm64_norm])
    (T := (bkPtr ↦ₛ x.bkBytes) ∗ memRegion (sp' + 312#64) 33 ∗ lsLogOff)
    (φ := bkPtr = bkPtr ∧ (33#64 : BitVec 64).toNat = x.bkBytes.length ∧ sp' + 312#64 = sp' +
      312#64 ∧ x.bkBytes.length < 2 ^ 63 ∧ PublicKey.deserialize x.bkBytes = .ok ⟨x.baseKey⟩)
    (by simp_all [deserializeOk33PlacedSpec, arm64_norm])
    ⟨rfl, hbk_len, rfl, hbk_lt63, hbk_deser⟩ (by sep_focus)
    ?_
  clear hcallDeser
  intro s8 hpc8 hrun8 hsp8 hsp8_align hinv8 hcs8
  dsimp only [deserializeOk33PlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr8 => ?_
  rcases hcs8 with ⟨hx19_8, hx20_8, hx21_8, hx22_8, hx23_8, hx24_8, hx25_8, hx26_8, hx27_8, hx28_8,
    hx29_8⟩
  have hsp8_eq : s8.sp = sp' := by tryFromPost_sp [hsp8, hsp6_eq]
  have h29_8 : s8.readReg64 .x29 = sp' + 512#64 := by simp [hx29_8, h29_6, arm64_norm]
  refine SepWPp.of_sepWP_end_pk hkf hinv8 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv9
  refine ⟨⟨by simp [hsp8_eq, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp8_align,
      hinv9, by simp [htr8, htr6, htr4, htr2, htr, arm64_norm]⟩,
    by simp [h29_8, arm64_norm],
    by simp [hx28_8, hx28_6, hx28_4, hx28_2, hx28, arm64_norm],
    by simp [hx27_8, hx27_6, h27_4, arm64_norm],
    by simp [hx26_8, hx26_6, hx26_4, h26_2, arm64_norm],
    by simp [hx25_8, hx25_6, hx25_4, hx25_2, hx25, arm64_norm],
    by simp [hx24_8, hx24_6, h24_4, arm64_norm],
    by simp [hx23_8, hx23_6, hx23_4, hx23_2, hx23, arm64_norm],
    by simp [hx22_8, hx22_6, hx22_4, hx22_2, hx22, arm64_norm],
    by simp [hx21_8, hx21_6, hx21_4, hx21_2, hx21, arm64_norm],
    by simp [hx20_8, hx20_6, hx20_4, hx20_2, hx20, arm64_norm],
    by simp [hx19_8, hx19_6, hx19_4, hx19_2, hx19, arm64_norm], ?_⟩
  have hrepack := slice_rest_to_vecU8Buf A bkCap bkPtr x.bkBytes
  refine Entails.trans
    (Q := (bkPtr ↦ₛ x.bkBytes) ∗ vecU8Rest A bkCap bkPtr x.bkBytes ∗ (((sp' + 312#64) ↦₈ 0#8) ∗
      ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
        lsLogOff ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 345#64) 15 ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by apply entails_of_eq; ac_rfl) ?_
  rw [← sepConj_assoc (bkPtr ↦ₛ x.bkBytes)]
  refine Entails.trans (sepConj_mono_left hrepack) ?_
  apply entails_of_eq; ac_rfl

end CryptoVerification.E2E.Pqxdh.ResponderWire
