/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbEk
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded `<EkSentCt1Received>::from_pb` Contract

Relocatable Block-`348` `subroutine_ok` proof for `<EkSentCt1Received>::from_pb` and its
cross-block lift to `lsProg_333` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudgetAux

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_348 blkPl_348 extract_withLsCodeLoaded
   lsProg_348 ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl lsρ sepWP_seq_lscl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator CIPHERTEXT1_SIZE DECAPSULATION_KEY_SIZE ProtoAuthenticator V1State spqrAuthApi)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth
  (AuthFromPbPinnedGhost authFromPbStack authenticatorAt)
open CryptoVerification.SpqrV1.Drop
  (Saved48Preserved TwoVecGhost cap_add_one_beq_zero_false optProtoAuthenticatorAt
   optProtoAuthenticatorAt_some protoAuthenticatorAt_entails_dealloc protoUnchunked2VecHeadersAt
   protoUnchunkedEkSentCt1ReceivedAt twoVecHeadersAt twoVecHeadersAt_entails_memRegion_48
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.ProtoRepr (AuthenticatorPBGhost authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.Unchunked
  (EkSentCt1ReceivedFromPbGhost auth48HeadersAt auth48HeadersAt_entails_memRegion_48
   authPBPinnedTailAt authenticatorAt_unpack authenticatorPBPinnedAt_entails_dealloc
   authenticatorPBPinnedAt_eq_cap_tail ekSentCt1ReceivedAt ekSentCt1ReceivedAt_pack
   ekSentCt1ReceivedFromPbStack ekSentCt1ReceivedResultAt extractLsb'_0_64_append
   extractLsb'_64_64_append memRegion_104_eq_cells13 memRegion_104_err_split
   memRegion_48_auth48_8_entails_104 memRegion_ekSentCt1Received_scratch_restore ofNat_beq_lit_iff
   optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
   optProtoAuthenticatorAt_some_unpack protoUnchunkedEkSentCt1ReceivedAt_unpack
   stackAt_authFromPb_split_allocHook_sub144 stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook
   stackAt_ekSentCt1ReceivedFromPb_split stackAt_ekSentCt1ReceivedFromPb_split_allocHook
   stackAt_ekSentCt1ReceivedFromPb_tail_allocHook twoVecHeadersAt_48_eq
   unpacked_ekSentCt1Received_entails_dealloc unpacked_ekSentCt1Received_headers_entails_memRegion_48_8
   vecU8Payload)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget rustAllocEvents rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Auth.FromPbBudget
  (AuthFromPbEnv authFromPbEvents authFromPbPinnedSpec authKeyCloneEvents)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux (FromPbAllocHooksBudget)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlacedBudgetAux
  (v9_auth_from_pb_pinned_cl_on)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
  (EkSentCt1ReceivedFromPbPostEnv EkSentCt1ReceivedFromPbPreEnv authFromPbAllocEvents
   ekSentCt1ReceivedFromPb ekSentCt1ReceivedFromPbAllocEvents ekSentCt1ReceivedFromPbSpec
   ekSentCt1ReceivedFromPbSpecOfEnv)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## Private Helpers -/

@[local simp]
private theorem spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

@[local arm64_norm]
private theorem sub_beq_zero_eq_beq (x y : BitVec 64) :
    (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm]
private theorem bne_eq_not_beq (x y : BitVec 64) : (x != y) = !(x == y) := rfl

private theorem authKeyCloneEvents_eq (bs : List (BitVec 8)) :
    authKeyCloneEvents bs = (if bs = [] then [] else rustAllocEvents bs.length 1) := by
  cases bs <;> rfl

private theorem authFromPbEvents_eq_allocEvents (auth : ProtoAuthenticator) :
    authFromPbEvents auth = authFromPbAllocEvents auth := by
  simp only [authFromPbEvents, authFromPbAllocEvents, authKeyCloneEvents_eq]

private theorem ekFromPbAllocEvents_of_cond_false (F : ShaCompress)
    (pb : V1State.Unchunked.EkSentCt1Received)
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false) :
    ekSentCt1ReceivedFromPbAllocEvents F pb = [] := by
  simp [ekSentCt1ReceivedFromPbAllocEvents, ekSentCt1ReceivedFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb, hcond]

private theorem ekFromPbAllocEvents_of_auth_none (F : ShaCompress)
    (pb : V1State.Unchunked.EkSentCt1Received) (hauth : pb.auth = none) :
    ekSentCt1ReceivedFromPbAllocEvents F pb = [] := by
  simp [ekSentCt1ReceivedFromPbAllocEvents, hauth]

private theorem ekFromPbAllocEvents_of_ok (F : ShaCompress)
    (pb : V1State.Unchunked.EkSentCt1Received) (auth : ProtoAuthenticator)
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth) :
    ekSentCt1ReceivedFromPbAllocEvents F pb = authFromPbAllocEvents auth := by
  simp [ekSentCt1ReceivedFromPbAllocEvents, ekSentCt1ReceivedFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb, hcond, hauth]

private theorem fitsEnv_auth_of_ek {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {F : ShaCompress} {pb : V1State.Unchunked.EkSentCt1Received} {auth : ProtoAuthenticator}
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hfits : FitsEnv M lim st (EkSentCt1ReceivedFromPbPreEnv F pb)) :
    FitsEnv M lim st (AuthFromPbEnv auth) := by
  intro evs hevs; apply hfits
  simp only [EkSentCt1ReceivedFromPbPreEnv, ekFromPbAllocEvents_of_ok F pb auth hcond hauth]
  simpa only [AuthFromPbEnv, authFromPbEvents_eq_allocEvents] using hevs

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem align_pre_st {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  subst heq; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem authenticatorPBPinnedAt_48_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 48#64) auth ⊢
      auth48HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_48_eq]
  exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 48#64) auth

private theorem protoUnchunked2VecHeadersAt_entails_memRegion_104
    (a : BitVec 64) (g : TwoVecGhost) :
    protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢
      memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (twoVecHeadersAt_entails_memRegion_48 a g)

private theorem authenticatorAt_sub144_unpack (A : RustAlloc) (sp : BitVec 64)
    (auth : Authenticator) :
    authenticatorAt A (sp - 144#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 144#64) ↦₆₄ ca1) ∗ ((sp - 136#64) ↦₆₄ pa1) ∗
         ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 120#64) ↦₆₄ ca2) ∗ ((sp - 112#64) ↦₆₄ pa2) ∗
         ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 144#64) auth
  have h1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  have h3 : (sp - 144#64) + 24#64 = sp - 120#64 := by bv_omega
  have h4 : (sp - 144#64) + 32#64 = sp - 112#64 := by bv_omega
  have h5 : (sp - 144#64) + 40#64 = sp - 104#64 := by bv_omega
  rwa [h1, h2, h3, h4, h5] at h

private theorem memRegion_144_96_split_48_48 (sp : BitVec 64) :
    memRegion (sp - 144#64) 96 = memRegion (sp - 144#64) 48 ∗ memRegion (sp - 96#64) 48 :=
  ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 48) (b' := sp - 96#64) rfl (by bv_omega) (by decide)

private abbrev RetPost {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private theorem close_ek_post {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress} {pbA : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received}
    {st0 : M.σ} {s0 sf : State} {Pf Res R : SepProp} {evsAll : List AllocEvent}
    (hp : Pf ⊢ Res ∗ memRegion pbA 104 ∗ A.pool lim (M.stepEvents evsAll st0) sf ∗
      stackAt s0.sp ekSentCt1ReceivedFromPbStack)
    (htr : sf.trace = s0.trace)
    (hevs : EkSentCt1ReceivedFromPbPostEnv F pb evsAll)
    (hm : sf.mem ⊨ Pf ∗ R) :
    sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ Res ∗ memRegion pbA 104 ∗
      (∃∗ evs : List AllocEvent, ⌜EkSentCt1ReceivedFromPbPostEnv F pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf) ∗
      stackAt s0.sp ekSentCt1ReceivedFromPbStack) ∗ R := by
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hp) hm)⟩
  refine Entails.trans (Entails.of_eq (show _ =
    A.pool lim (M.stepEvents evsAll st0) sf ∗
      (Res ∗ memRegion pbA 104 ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack ∗ R) by sep_ac_rfl)) ?_
  have hex : A.pool lim (M.stepEvents evsAll st0) sf ⊢
      ∃∗ evs : List AllocEvent, ⌜EkSentCt1ReceivedFromPbPostEnv F pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st0) sf :=
    Entails.sepExists_right evsAll (Entails.pure_right hevs (Entails.refl _))
  exact Entails.trans (sepConj_mono_left hex) (Entails.of_eq (by sep_ac_rfl))

private theorem sepWP_cut {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} (mid : BitVec 64) (Q : State → SepProp → Prop)
    (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q sm Pm → SepWP prog target sm Pm post) :
    SepWP prog target s P post := SepWP.seq h1 h2

private theorem sepWP_cut_lscl [LibsignalPlacement] {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (mid : BitVec 64) (Q : State → SepProp → Prop)
    (h1 : SepWP prog mid s P Q)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm Pm → SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hq hclm => h2 sm Pm hpc hrun hclm hq)

private theorem sepWP_strengthen_entails {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 : State → SepProp} {R : State → Prop}
    (h : ∀ sm, Q1 sm ⊢ Q2 sm)
    (hwp : SepWP prog target s P (fun sm Pm => (Pm ⊢ Q1 sm) ∧ R sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ Q2 sm) ∧ R sm) :=
  SepWP.mono hwp fun sm _ _ _ ⟨hp, hr⟩ => ⟨Entails.trans hp (h sm), hr⟩

private theorem sepWP_evs_step {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (evs : List AllocEvent) (hevs : FreeOnlyEvs evs)
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs evs sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs', FreeOnlyEvs evs' ∧ (Pm ⊢ P_evs evs' sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨evs, hevs, hp, hq⟩

private theorem sepWP_close_ret {prog : Program} {s0 s : State} {P : SepProp}
    {Post : State → SepProp → Prop}
    (Q_out : State → SepProp)
    (h : SepWP prog (s0.readReg64 .lr) s P (fun sf Pf =>
      (Pf ⊢ Q_out sf) ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ CalleeSavedPreserved s0 sf))
    (hpost : ∀ sf Pf, (Pf ⊢ Q_out sf) → sf.sp = s0.sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → Post sf Pf) :
    SepWP prog (s0.readReg64 .lr) s P Post :=
  SepWP.mono h fun sf Pf _ _ ⟨hp, hsp_f, htr_f, hcs_f⟩ => hpost sf Pf hp hsp_f htr_f hcs_f

/-! ## Error-Branch, Auth-None & Post-Auth Sub-Proofs (Block `348`) -/

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_err_drop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    {out pbA : BitVec 64} {pb : V1State.Unchunked.EkSentCt1Received} {st0 : M.σ}
    {R : SepProp} {s0 s1 : State} {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) pb.auth ∗
          memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        A.pool lim st0 s1 ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ekSentCt1ReceivedFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have halloc_nil := ekFromPbAllocEvents_of_cond_false F pb hcond
  unfold RetPost ekSentCt1ReceivedFromPbSpec ekSentCt1ReceivedFromPbSpecOfEnv; dsimp only
  simp only [ekSentCt1ReceivedFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb, hcond,
    Bool.false_eq_true, ↓reduceIte, ekSentCt1ReceivedResultAt]
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  refine seq_clean_evs (mid := (blkPl_348).base + 236#64)
    (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
      (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗
      memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_48_none]
      apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      refine sepWP_strengthen_entails (fun _ =>
        sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc pbA))))) ?_
      wp_steps_sync_pool ((blkPl_348).base + 236#64)
      simp only [State.setMem_setMem]; dsimp only [noneCap]; wp_done
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (protoAuthenticatorAt_entails_dealloc A.repAlloc (pbA + 48#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [twoVecHeadersAt_48_eq]
      have hpull_ga :
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗
              (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗ auth48HeadersAt pbA ga ∗
                vecCapPtrDealloc A.repAlloc ga.v1.cap ga.v1.ptr ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
            A.pool lim st0 s1 ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) =
          (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
            (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
              (protoUnchunked2VecHeadersAt pbA g ∗
                (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A.repAlloc ga.v1.cap ga.v1.ptr ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
                memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              A.pool lim st0 s1 ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by sep_ac_rfl
      rw [hpull_ga]; apply SepWP.pure_elim; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean_evs (mid := (blkPl_348).base + 216#64)
        (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
          (protoUnchunked2VecHeadersAt pbA g ∗ (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗
            memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
          A.pool lim (M.stepEvents evs st0) sm ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [auth48HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
          wp_steps_sync_pool ((blkPl_348).base + 216#64)
          simp only [State.setMem_setMem]; dsimp only [noneCap]; wp_done
        · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
          wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          simp only [State.setMem_setMem]
          have hsp_sub : ((s0.sp - 144#64) &&& 15#64 == 0#64) = true :=
            ProofLib.spAligned_sub s0.sp 144#64 hsp_align (by decide)
          wp_apply
          refine align_pre_st (by rw [hsp_1]; dsimp only [noneCap]; sep_ac_rfl) ?_; wp_done
      · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1⟩
        let sta1 := M.stepEvents evsa1 st0
        dsimp only [auth48HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_step evsa1 hevsa1
          wp_steps
          refine SepWP.weaken_pre
            (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth48HeadersAt_entails_memRegion_48 pbA ga))))) ?_
          wp_done
        · apply sepWP_evs_step (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
            (hevsa1.append (FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
          have heq_st : M.stepEvents (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1) st0 =
              M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1 := by
            simp only [sta1, AllocCostModel.stepEvents_append]
          rw [heq_st]
          have hsp_sub : ((s0.sp - 144#64) &&& 15#64 == 0#64) = true :=
            ProofLib.spAligned_sub s0.sp 144#64 hsp_align (by decide)
          wp_steps; wp_apply
          refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
              (protoUnchunked2VecHeadersAt pbA g ∗ auth48HeadersAt pbA ga ∗ memRegion (pbA + 96#64) 8 ∗
                vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
              A.pool lim (M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1) _ ∗
              memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by
              rw [hsp_a1]; unfold auth48HeadersAt vecCapPtrDealloc
              dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]; sep_ac_rfl))
            (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
              (auth48HeadersAt_entails_memRegion_48 pbA ga)))))) ?_
          dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs (mid := (blkPl_348).base + 256#64)
      (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        have hsp_sub : ((s0.sp - 144#64) &&& 15#64 == 0#64) = true :=
          ProofLib.spAligned_sub s0.sp 144#64 hsp_align (by decide)
        wp_steps; wp_apply; refine align_pre_st (by rw [hsp_2]; sep_ac_rfl) ?_; wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      let st2 := M.stepEvents evs2 st1
      dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_close_ret
          (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
            memRegion pbA 104 ∗ A.pool lim (M.stepEvents (evs1 ++ evs2) st0) sf ∗
            stackAt s0.sp ekSentCt1ReceivedFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f
            ⟨evs1 ++ evs2, hevs1.append hevs2, by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (evs1 ++ evs2) st0 = st2 := by
          simp only [st1, st2, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_done
      · refine sepWP_close_ret
          (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
            memRegion pbA 104 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1) st0) sf ∗
            stackAt s0.sp ekSentCt1ReceivedFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f
            ⟨evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1,
              (hevs1.append hevs2).append (FreeOnlyEvs.singleton 1 g.v2.cap.toNat),
              by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents g.v2.cap.toNat 1) st0 =
            M.stepEvents (rustDeallocEvents g.v2.cap.toNat 1) st2 := by
          simp only [st1, st2, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans
            (Entails.of_eq (show _ =
              (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
              (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
                unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; sep_ac_rfl))
            (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        have hlr0' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
        wp_apply; rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_auth_none_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    {out pbA : BitVec 64} {pb : V1State.Unchunked.EkSentCt1Received} {st0 : M.σ}
    {R : SepProp} {s0 s1 : State} {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
        A.pool lim st0 s1 ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ekSentCt1ReceivedFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have halloc_nil := ekFromPbAllocEvents_of_auth_none F pb hauth
  unfold RetPost ekSentCt1ReceivedFromPbSpec ekSentCt1ReceivedFromPbSpecOfEnv; dsimp only
  simp only [ekSentCt1ReceivedFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb, hcond, hauth,
    ↓reduceIte, ekSentCt1ReceivedResultAt]
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  refine seq_clean_evs (mid := (blkPl_348).base + 328#64)
    (P_evs := fun evs sm => (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
      (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr) ∗
      A.pool lim (M.stepEvents evs st0) sm ∗
      memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]
      wp_steps_sync_pool ((blkPl_348).base + 328#64)
      simp only [State.setMem_setMem]; dsimp only [noneCap]; wp_done
    · apply sepWP_evs_dealloc g.v1.cap.toNat 1
      wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      simp only [State.setMem_setMem]
      have hsp_sub : ((s0.sp - 144#64) &&& 15#64 == 0#64) = true :=
        ProofLib.spAligned_sub s0.sp 144#64 hsp_align (by decide)
      wp_apply
      refine align_pre_st (by rw [hsp_1]; dsimp only [noneCap]; sep_ac_rfl) ?_; wp_done
  · intro evs1 s2 hevs1 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    let st1 := M.stepEvents evs1 st0
    dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc,
      LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · refine sepWP_close_ret
        (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
          memRegion pbA 104 ∗ A.pool lim (M.stepEvents evs1 st0) sf ∗
          stackAt s0.sp ekSentCt1ReceivedFromPbStack)
        ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f
          ⟨evs1, hevs1, by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
      wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
      wp_done
    · refine sepWP_close_ret
        (fun sf => ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
          memRegion pbA 104 ∗
          A.pool lim (M.stepEvents (evs1 ++ rustDeallocEvents g.v2.cap.toNat 1) st0) sf ∗
          stackAt s0.sp ekSentCt1ReceivedFromPbStack)
        ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f
          ⟨evs1 ++ rustDeallocEvents g.v2.cap.toNat 1,
            hevs1.append (FreeOnlyEvs.singleton 1 g.v2.cap.toNat),
            by rw [halloc_nil, List.nil_append]⟩, hsp_f, hcs_f⟩)
      have heq_st : M.stepEvents (evs1 ++ rustDeallocEvents g.v2.cap.toNat 1) st0 =
          M.stepEvents (rustDeallocEvents g.v2.cap.toNat 1) st1 := by
        simp only [st1, AllocCostModel.stepEvents_append]
      rw [heq_st]; wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (Entails.trans
          (Entails.of_eq (show _ =
            (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
              unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; sep_ac_rfl))
          (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
      have hlr0' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
      wp_apply; rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done

private theorem ek_sent_ct1_received_from_pb_err_drop_unpacked_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {st0 : M.σ} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) pb.auth ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim st0 s1 ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ekSentCt1ReceivedFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (unpacked_ekSentCt1Received_entails_dealloc A.repAlloc pbA c1 p1
      (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.dk pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0
  apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (ek_sent_ct1_received_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8)
      (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩) hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align hlr0)

private theorem ek_sent_ct1_received_from_pb_auth_none_unpacked_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {st0 : M.σ} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) none ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim st0 s1 ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ekSentCt1ReceivedFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (Entails.trans
      (unpacked_ekSentCt1Received_entails_dealloc A.repAlloc pbA c1 p1
        (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch none pb.dk pb.ct1)
      (sepConj_mono_right (sepConj_mono_left (by
        rw [optProtoAuthenticatorAt_48_none]
        exact optProtoAuthenticatorAt_48_none_entails_memRegion_48 A.repAlloc pbA)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0
  apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (ek_sent_ct1_received_from_pb_auth_none_placed (v_out0 := v_out0) (v_out8 := v_out8)
      (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩) hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align hlr0)

set_option maxHeartbeats 1200000 in
private theorem ek_sent_ct1_received_from_pb_ok_after_auth_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {auth : ProtoAuthenticator} {st0 : M.σ}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (blkPl_348).base + 80#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx19_1 : s1.readReg64 .x19 = pbA) (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch) (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlr0 : LsRetAddr624 (s0.readReg64 .lr)) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         authenticatorPBPinnedAt A.repAlloc ga (pbA + 48#64) auth ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim (M.stepEvents (authFromPbAllocEvents auth) st0) s1 ∗
        stackAt (s0.sp - 144#64) authFromPbStack ∗
        authenticatorAt A.repAlloc (s0.sp - 144#64) (Authenticator.fromPb auth) ∗
        memRegion (s0.sp - 96#64) 48 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (RetPost (ekSentCt1ReceivedFromPbSpec M A lim F) (⟨out, pbA, pb⟩, st0) R s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have halloc_ok := ekFromPbAllocEvents_of_ok F pb auth hcond hauth
  let stA := M.stepEvents (authFromPbAllocEvents auth) st0
  unfold RetPost ekSentCt1ReceivedFromPbSpec ekSentCt1ReceivedFromPbSpecOfEnv; dsimp only [spqrAuthApi]
  simp only [ekSentCt1ReceivedFromPb,
    CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb, hcond, hauth,
    ↓reduceIte, ekSentCt1ReceivedResultAt]
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
  refine sepWP_cut ((blkPl_348).base + 140#64)
    (fun sm Pm => (Pm ⊢ (ekSentCt1ReceivedAt A.repAlloc (F := F) out
        { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
      (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
      A.pool lim stA sm ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
      Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (authenticatorPBPinnedAt_48_entails_dealloc A.repAlloc ga pbA auth))))))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (authenticatorAt_sub144_unpack A.repAlloc s0.sp (Authenticator.fromPb auth))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 96#64) 6 (by decide), memRegion_104_eq_cells13 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists
    wp_steps_sync_pool ((blkPl_348).base + 140#64)
    simp only [State.setMem_setMem]; rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
    have hpack_out := ekSentCt1ReceivedAt_pack A.repAlloc (F := F) out
      ca1 pa1 ca2 pa2 c1 p1 c2 p2 pb.epoch (Authenticator.fromPb auth) pb.dk pb.ct1
    have hpack_sp := memRegion_ekSentCt1Received_scratch_restore s0.sp
      ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)
      c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ekSentCt1Received_headers_entails_memRegion_48_8 pbA
      c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗
        ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗
        ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗
        ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((out + 96#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A.repAlloc ca1 pa1 (Authenticator.fromPb auth).rootKey ∗
       vecU8Payload A.repAlloc ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((pbA + 96#64) ↦₆₄ pb.epoch)) ∗
       auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
       vecCapPtrDealloc A.repAlloc ga.rootKey.cap ga.rootKey.ptr ∗
       vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
      ((((s0.sp - 144#64) ↦₆₄ ca1) ∗ ((s0.sp - 136#64) ↦₆₄ pa1) ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((s0.sp - 120#64) ↦₆₄ ca2) ∗ ((s0.sp - 112#64) ↦₆₄ pa2) ∗
        ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
       (((s0.sp - 96#64) ↦₆₄ c1) ∗ ((s0.sp - 88#64) ↦₆₄ p1) ∗
        ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((s0.sp - 72#64) ↦₆₄ c2) ∗ ((s0.sp - 64#64) ↦₆₄ p2) ∗
        ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool lim stA _ ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) by sep_ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre_st (by sep_ac_rfl) ?_; wp_done
  · intro s2 _Pm hpc2 hrun2 ⟨hent2, ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
    refine SepWP.weaken_pre hent2 ?_
    refine seq_clean_evs (mid := (blkPl_348).base + 160#64)
      (P_evs := fun evs sm => (ekSentCt1ReceivedAt A.repAlloc (F := F) out
          { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
        (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A.repAlloc ga.macKey.cap ga.macKey.ptr) ∗
        A.pool lim (M.stepEvents evs stA) sm ∗
        memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [auth48HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;>
        simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [AllocCostModel.stepEvents_nil]; wp_steps; wp_done
      · apply sepWP_evs_dealloc ga.rootKey.cap.toNat 1
        have hsp_sub : ((s0.sp - 144#64) &&& 15#64 == 0#64) = true :=
          ProofLib.spAligned_sub s0.sp 144#64 hsp_align (by decide)
        wp_steps; wp_apply; refine align_pre_st (by rw [hsp_2]; sep_ac_rfl) ?_; wp_done
    · intro evs1 s3 hevs1 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      let st1 := M.stepEvents evs1 stA
      dsimp only [auth48HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_close_ret
          (fun sf => ekSentCt1ReceivedAt A.repAlloc (F := F) out
              { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
            memRegion pbA 104 ∗ A.pool lim (M.stepEvents (authFromPbAllocEvents auth ++ evs1) st0) sf ∗
            stackAt s0.sp ekSentCt1ReceivedFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f ⟨evs1, hevs1, by rw [halloc_ok]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (authFromPbAllocEvents auth ++ evs1) st0 = st1 := by
          simp only [stA, st1, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_done
      · refine sepWP_close_ret
          (fun sf => ekSentCt1ReceivedAt A.repAlloc (F := F) out
              { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
            memRegion pbA 104 ∗
            A.pool lim (M.stepEvents (authFromPbAllocEvents auth ++ (evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1)) st0) sf ∗
            stackAt s0.sp ekSentCt1ReceivedFromPbStack)
          ?_ (fun sf Pf hp hsp_f htr_f hcs_f => ⟨close_ek_post hp htr_f
            ⟨evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1,
              hevs1.append (FreeOnlyEvs.singleton 1 ga.macKey.cap.toNat), by rw [halloc_ok]⟩, hsp_f, hcs_f⟩)
        have heq_st : M.stepEvents (authFromPbAllocEvents auth ++ (evs1 ++ rustDeallocEvents ga.macKey.cap.toNat 1)) st0 =
            M.stepEvents (rustDeallocEvents ga.macKey.cap.toNat 1) st1 := by
          simp only [stA, st1, AllocCostModel.stepEvents_append]
        rw [heq_st]; wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans
            (Entails.of_eq (show _ =
              (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8) ∗
              (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by
                unfold auth48HeadersAt; sep_ac_rfl))
            (sepConj_mono_left (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        have hlr0' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr0
        wp_apply; rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done

/-! ## Relocatable `withLsCodeLoaded` Contracts (Block `348` & Lift to Block `333`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`) meets
    `withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec M A lim F)` under explicit
    `subroutine_ok` hypotheses for `__rust_dealloc` and `withLsCodeLoaded`-guarded Block `330`. -/
theorem v4c_ek_sent_ct1_received_from_pb_cl_placed_ok_of_sub [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hauth_cl : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim))) :
    subroutine_ok ((blkPC_348).rebase (blkPl_348).base H) (blkPl_348).base
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec M A lim F)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨out, pbA, pb⟩, st0⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have hpre' : s0.mem ⊨
      (memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A.repAlloc pbA pb ∗
        A.pool lim st0 s0 ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack) ∗ R ∧
      s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA ∧
      FitsEnv M lim st0 (EkSentCt1ReceivedFromPbPreEnv F pb) ∧
      LsRetAddr624 (s0.readReg64 .lr) := by
    simp only [ekSentCt1ReceivedFromPbSpec, ekSentCt1ReceivedFromPbSpecOfEnv] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact ⟨hpre.2, hpre.1⟩
  rcases hpre' with ⟨hm0, hx0, hx1, hfits, hlr0⟩
  refine ⟨memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A.repAlloc pbA pb ∗
    A.pool lim st0 s0 ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack, R, hm0,
    SepWPp.of_sepWP_ret ?_⟩
  rw [stackAt_ekSentCt1ReceivedFromPb_split s0.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_unpack A.repAlloc pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro c1; apply ProofLib.SepWP.exists_left; intro p1
  apply ProofLib.SepWP.exists_left; intro c2; apply ProofLib.SepWP.exists_left; intro p2
  have hfocus1 :
      memRegion out 104 ∗
        (⌜pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
          (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
          ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
          optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) pb.auth ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
          vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim st0 s0 ∗
        (stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ cells (s0.sp - 48#64) 6) =
      ⌜pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63⌝ ∗
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
          ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
          optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) pb.auth ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
          vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim st0 s0 ∗
        (stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ cells (s0.sp - 48#64) 6)) := by sep_ac_rfl
  rw [hfocus1]; apply SepWP.pure_elim; intro ⟨hl1, hl2, _⟩
  cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x22_old x21_old x20_old x19_old
  by_cases hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hdk_t : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_48_none]
      refine sepWP_cut ((blkPl_348).base + 296#64)
        (fun sm Pm => (Pm ⊢ (memRegion out 104 ∗
          ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
           ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
           optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) none ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
           vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
          A.pool lim st0 sm ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
           ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
          Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · wp_steps_sync_pool ((blkPl_348).base + 296#64)
        simp only [State.setMem_setMem]; rw [optProtoAuthenticatorAt_48_none]
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19, noneCap]; sep_ac_rfl) ?_
        wp_done
      · intro s1 _Pm hpc1 hrun1 ⟨hent1, hpres1, hx0_1, hx19_1⟩
        exact SepWP.weaken_pre hent1
          (ek_sent_ct1_received_from_pb_auth_none_unpacked_placed hdealloc_raw hcond hauth
            hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv hlr0)
    | some auth =>
      have hfits_auth := fitsEnv_auth_of_ek hcond hauth hfits
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) (some auth) ∗
        (memRegion out 104 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1 ∗
         A.pool lim st0 s0 ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
         ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
         ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old)) by sep_ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A.repAlloc (pbA + 48#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga
      have hfocus_ga :
          ((⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗ ((pbA + 48#64) ↦₆₄ ga.rootKey.cap) ∗
            authPBPinnedTailAt A.repAlloc ga (pbA + 48#64) auth) ∗
           (memRegion out 104 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 96#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1 ∗
            A.pool lim st0 s0 ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
            ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
            ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old))) =
          ⌜ga.rootKey.cap.toNat < 2 ^ 63⌝ ∗
          (((pbA + 48#64) ↦₆₄ ga.rootKey.cap) ∗ authPBPinnedTailAt A.repAlloc ga (pbA + 48#64) auth ∗
            memRegion out 104 ∗ (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 96#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1 ∗
            A.pool lim st0 s0 ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
            ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗ ((s0.sp - 32#64) ↦₆₄ x22_old) ∗
            ((s0.sp - 24#64) ↦₆₄ x21_old) ∗ ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old)) := by sep_ac_rfl
      rw [hfocus_ga]; apply SepWP.pure_elim; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_144_96_split_48_48 s0.sp]
      refine sepWP_cut_lscl hcl (lsmpl.base 330)
        (fun sm Pm => (Pm ⊢ (memRegion (s0.sp - 144#64) 48 ∗
          authenticatorPBPinnedAt A.repAlloc ga (pbA + 48#64) auth ∗
          A.pool lim st0 sm ∗ stackAt (s0.sp - 144#64) authFromPbStack) ∗
          (memRegion out 104 ∗
           ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 96#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
           memRegion (s0.sp - 96#64) 48 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
          Saved48Preserved s0 sm (s0.sp - 144#64) ∧
          sm.readReg64 .x0 = s0.sp - 144#64 ∧ sm.readReg64 .x1 = pbA + 48#64 ∧
          sm.readReg64 .lr = (blkPl_348).base + 80#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧
          sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps_sync_pool (lsmpl.base 330); simp only [State.setMem_setMem]
        rw [← sepConj_assoc ((pbA + 48#64) ↦₆₄ ga.rootKey.cap),
            ← authenticatorPBPinnedAt_eq_cap_tail A.repAlloc ga (pbA + 48#64) auth]
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_
        wp_done
      · intro sm _Pm hpcm hrunm hclm ⟨hentm, ⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        refine SepWP.weaken_pre hentm ?_
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m]
          exact ProofLib.spAligned_sub s0.sp 144#64 hsp_align_bv (by decide)
        refine SepWP.call_subroutine_frame hauth_cl
          (x := (⟨s0.sp - 144#64, pbA + 48#64, ga, auth⟩, st0))
          (F := memRegion out 104 ∗
           ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 96#64) ↦₆₄ pb.epoch) ∗ vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
           memRegion (s0.sp - 96#64) 48 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          hpcm hrunm hsp_align_m hlr_m ?_
          (fun _ _ _ hm => not_satisfies_false_sepConj hm)
          (fun _ _ _ _ hm => not_satisfies_false_sepConj hm) ?_
        · intro R' hm'
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
          refine ⟨hclm, ?_⟩
          rw [sepConj_assoc] at hm'
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_m, hx1_m, hfits_auth⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by rw [hsp_m]; try sep_ac_rfl)) hm'
        · intro s1 hpc1 hrun1 hsp1 hcs1
          rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
            hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepExists_sepConj_left]
          apply ProofLib.SepWP.exists_left; intro evsAuth
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; rintro ⟨htrace_s1, hevsAuth⟩
          rw [htrace_m] at htrace_s1
          have hevsAuth_eq : evsAuth = authFromPbAllocEvents auth := by
            simpa only [AuthFromPbEnv, authFromPbEvents_eq_allocEvents] using hevsAuth
          subst hevsAuth_eq
          have hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64) :=
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; sep_ac_rfl))
            (ek_sent_ct1_received_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth
              hpc1 hrun1 hpres1 hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv hlr0)
  · have hcond_f : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
        pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine sepWP_cut ((blkPl_348).base + 176#64)
      (fun sm Pm => (Pm ⊢ (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A.repAlloc (pbA + 48#64) pb.auth ∗ ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A.repAlloc c1 p1 pb.dk ∗ vecU8Payload A.repAlloc c2 p2 pb.ct1) ∗
        A.pool lim st0 sm ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
        Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
        · exfalso; apply hcond
          rw [ofNat_beq_lit_iff hl1 (by decide)] at h1; rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
          simp [h1, h2, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
        · have h2_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps_sync_pool ((blkPl_348).base + 176#64); simp only [State.setMem_setMem]
          refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.dk.length == 2400#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps_sync_pool ((blkPl_348).base + 176#64); simp only [State.setMem_setMem]
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done
    · intro s1 _Pm hpc1 hrun1 ⟨hent1, hpres1, hx0_1, hx19_1⟩
      exact SepWP.weaken_pre hent1
        (ek_sent_ct1_received_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f
          hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv hlr0)

/-- Relocatable `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`) meets
    `withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec M A lim F)` on `lsProg_348` under
    `FromPbAllocHooksBudget`. -/
theorem v4c_ek_sent_ct1_received_from_pb_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_348 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 348)]
  change subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
    (blkPl_348).base _
  exact v4c_ek_sent_ct1_received_from_pb_cl_placed_ok_of_sub
    (spqr_hook_ok_of_mem hA.dealloc)
    (v9_auth_from_pb_pinned_cl_on hA)

theorem v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok_of_sub [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hauth_cl : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec M A lim))) :
    Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext := by
  unfold Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt
  have hcl348 : subroutine_ok (lsProg_348 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec M A lim F)) := by
    rw [← ls_blockPlacement_base (i := 348)]
    exact v4c_ek_sent_ct1_received_from_pb_cl_placed_ok_of_sub hdealloc_raw hauth_cl
  exact ls_subroutine_ok_of_block hcl348

theorem v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooksBudget M A lim ext) :
    Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt M A lim F ext := by
  unfold Variant4PlacedBudget.EkSentCt1ReceivedFromPbPlacedOkExt
  exact ls_subroutine_ok_of_block (v4c_ek_sent_ct1_received_from_pb_cl_placed_ok hA)

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4cPlacedBudgetAux
