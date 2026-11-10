/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable T5 Pre-Key Encrypt Error Tail (`+0xc38..+0xc64` → `+0x46c`)

Proves `kyber_placed_run` and `tailPreKeyEncryptErr_placed_ok` on Block `464` (`lsProg_464 Hk`)
under `RustCliAllocBudget M` and `[LibsignalPlacement]`, freeing any non-empty `KyberPayload`
ciphertext (`FreeOnlyEvs`) before entering T1 `+0x46c`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet)
open CryptoGames.LibsignalSessionApi
  (ApiError CiphertextMessage KyberPayload SessionRecord StoreAnswers)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsRustDeallocSym ls_hook_ok_ultra_of_mem lsρ)
open CryptoVerification.CliRatchet.EncPlaced (blkPC_464 blkPl_464 lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (encEntryPlaced)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost optKyberAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost cmScratch curScratch encSubStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
  (SpeStaged TailModel dropRecordSlots pollWith tailRegs words64At)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr
  (kyberDropRecordPoll_eq kyberNone_entails kyberPoll_eq kyberPost_four kyberPost_four'
   kyberPost_two kyberSome_entails memRegion_24_eq words64At_three_entails)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser boxU8At)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (EncTailVBudget SegExitBudget SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncTailVPlaced SegExitPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
  (encCommonPlacedFr encCommonPlaced_eq encTailBudget_run_withEncCommon
   encTail_placed_run_withEncCommon segExitBudget_of_run segExit_placed_of_run)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. `Tails` ↔ `ProtocolErr` Definitional Alignment Bridges -/

private theorem tails_dropRecordSlots_eq (A : RustAlloc) (sp : BitVec 64)
    (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots A sp scratch g rec ot cm poll =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots
        A sp scratch g rec ot cm poll :=
  rfl

private theorem tails_pollWith_3_eq (sp : BitVec 64) (off : Nat) (w3 w4 w5 : BitVec 64) :
    pollWith sp off [w3, w4, w5] =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.pollWith
        sp off [w3, w4, w5] :=
  rfl

private theorem tails_words64At_3_eq (a w3 w4 w5 : BitVec 64) :
    words64At a [w3, w4, w5] =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At
        a [w3, w4, w5] :=
  rfl

/-! ## 2. Packet `SepWP` (`+0xc38 → (bl __rust_dealloc) → +0x46c`) -/

set_option maxHeartbeats 800000 in
theorem kyber_placed_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (w0 w1 w2 w3 w4 w5 kyPtr : BitVec 64) (kp : Option KyberPayload) (st : M.σ) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xc38#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hx29 : s.readReg64 .x29 = s.sp + 0xb80#64)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x46c#64) s
      (memRegion (s.sp + 0x9d0#64) 24 ∗ words64At (s.sp + 0xb00#64) [w3, w4, w5] ∗
        optKyberAt A.repAlloc (s.sp + 0x8a0#64) kyPtr kp ∗
        A.pool lim st s ∗ stackAt s.sp allocHookStack)
      (fun s' P =>
        s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s' = calleeSavedVRegs s ∧
        tailRegs w0 w1 w2 s.sp s' ∧
        ∃ evs, FreeOnlyEvs evs ∧
          ∀ mem F, (mem ⊨ P ∗ F) →
            (mem ⊨ (words64At (s.sp + 0x9d0#64) [w3, w4, w5] ∗
              memRegion (s.sp + 0xb00#64) 24 ∗
              memRegion (s.sp + 0x8a0#64) 24 ∗
              A.pool lim (M.stepEvents evs st) s' ∗
              stackAt s.sp allocHookStack) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hal
  have hdealloc : subroutine_ok ((blkPC_464).rebase (blkPl_464).base Hk)
      (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    ls_hook_ok_ultra_of_mem (prog := lsProg_464 Hk) hdealloc_sat
  unfold encEntryPlaced at hpc ⊢
  rw [memRegion_24_eq]
  simp only [← tails_words64At_3_eq, sepExists_sepConj_left]
  refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  dsimp only [lsProg_464, ite_true]
  cases kp with
  | none =>
    dsimp only [optKyberAt]
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps_sync_pool ((blkPl_464).base + 1132#64)
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       ?_, ⟨[], FreeOnlyEvs.nil, ?_⟩⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro mem F hm
      have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
      simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
        sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
      have hk := kyberNone_entails (s.sp + 2208#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
      have hm1 : mem ⊨
          ((s.sp + 2512#64) ↦₆₄ w3) ∗ ((s.sp + 2520#64) ↦₆₄ w4) ∗
          ((s.sp + 2528#64) ↦₆₄ w5) ∗ ((s.sp + 2816#64) ↦₆₄ w3) ∗
          ((s.sp + 2824#64) ↦₆₄ w4) ∗ ((s.sp + 2832#64) ↦₆₄ w5) ∗
          ((s.sp + 2208#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 2216#64) 16 ∗
          A.pool lim st _ ∗ stackAt s.sp allocHookStack ∗ F :=
        Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm
      have hm2 := Satisfies.mono (kyberPost_two hb hk) hm1
      dsimp only [AllocCostModel.stepEvents, List.foldl]
      exact Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm2
  | some k =>
    dsimp only [optKyberAt, boxU8At, RustCliAllocBudget.repAlloc_live]
    simp only [sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
    wp_focus_pure
    rintro ⟨hptr_ne, hlen_lt⟩
    have hptr_beq : (kyPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hptr_ne
    by_cases hbs : k.ciphertext = []
    · simp only [hbs, List.length_nil, ite_true, emp_sepConj]
      wp_steps_sync_pool ((blkPl_464).base + 1132#64)
      refine SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *],
         ?_, ⟨[], FreeOnlyEvs.nil, ?_⟩⟩
      · unfold tailRegs
        simp only [wp_norm, arm64_norm, *]
      · intro mem F hm
        have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
        simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
          sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
        have hk := kyberSome_entails (s.sp + 2208#64) kyPtr 0#64 k.preKeyId
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
        have hm1 : mem ⊨
            ((s.sp + 2512#64) ↦₆₄ w3) ∗ ((s.sp + 2520#64) ↦₆₄ w4) ∗
            ((s.sp + 2528#64) ↦₆₄ w5) ∗ ((s.sp + 2816#64) ↦₆₄ w3) ∗
            ((s.sp + 2824#64) ↦₆₄ w4) ∗ ((s.sp + 2832#64) ↦₆₄ w5) ∗
            ((s.sp + 2208#64) ↦₆₄ kyPtr) ∗ ((s.sp + 2216#64) ↦₆₄ 0#64) ∗
            ((s.sp + 2224#64) ↦₃₂ k.preKeyId) ∗ memRegion (s.sp + 2228#64) 4 ∗
            A.pool lim st _ ∗ stackAt s.sp allocHookStack ∗ F :=
          Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm
        have hm2 := Satisfies.mono (kyberPost_four hb hk) hm1
        dsimp only [AllocCostModel.stepEvents, List.foldl]
        exact Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm2
    · have hpos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hbs
      have hlen_toNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hlen_ne : BitVec.ofNat 64 k.ciphertext.length ≠ 0#64 := by
        intro h
        have ht := congrArg BitVec.toNat h
        rw [hlen_toNat] at ht
        change k.ciphertext.length = 0 at ht
        omega
      have hlen_beq0 : (BitVec.ofNat 64 k.ciphertext.length == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hlen_ne
      simp only [hbs, ite_false]
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      let F_kyber : SepProp :=
        ((s.sp + 2512#64) ↦₆₄ w3) ∗ ((s.sp + 2520#64) ↦₆₄ w4) ∗
        ((s.sp + 2528#64) ↦₆₄ w5) ∗ ((s.sp + 2816#64) ↦₆₄ w3) ∗
        ((s.sp + 2824#64) ↦₆₄ w4) ∗ ((s.sp + 2832#64) ↦₆₄ w5) ∗
        ((s.sp + 2208#64) ↦₆₄ kyPtr) ∗
        ((s.sp + 2216#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
        ((s.sp + 2224#64) ↦₃₂ k.preKeyId) ∗ memRegion (s.sp + 2228#64) 4
      refine SepWP.call_subroutine_frame hdealloc
        (x := (kyPtr, k.ciphertext.length, 1, st))
        (F := F_kyber)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.spAligned, wp_norm, arm64_norm] at hal ⊢; exact hal)
        rfl
        ?_
        (fun _ _ _ hp => by
          dsimp only [rustCliDeallocBudgetSpec, Spec.onPanic] at hp
          exact not_satisfies_false_sepConj hp)
        (fun _ _ _ _ he => by
          dsimp only [rustCliDeallocBudgetSpec, Spec.onExit] at he
          exact not_satisfies_false_sepConj he)
        ?_
        (fun _ _ _ ho => by
          dsimp only [rustCliDeallocBudgetSpec, Spec.onOom] at ho
          exact False.elim (not_satisfies_false_sepConj ho))
      · intro R hm
        dsimp only [rustCliDeallocBudgetSpec, F_kyber]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨by simp only [wp_norm, arm64_norm],
                 by simp only [wp_norm, arm64_norm]; exact hlen_toNat,
                 by simp only [wp_norm, arm64_norm],
                 by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩, ?_⟩
        simp only [wp_norm, arm64_norm] at hm ⊢
        refine Satisfies.mono ?_ hm
        rw [sepConj_left_comm (A.live kyPtr k.ciphertext.length 1) (memRegion kyPtr k.ciphertext.length),
            sepConj_left_comm (A.pool lim st _) (memRegion kyPtr k.ciphertext.length)]
        refine Entails.trans ?_ (sepConj_mono_left (pointsToBytes_entails_memRegion kyPtr k.ciphertext))
        exact Entails.of_eq (by sep_ac_rfl)
      · intro sm hpcm hrunm hspm hcsm
        simp only [wp_norm, arm64_norm] at hpcm hspm
        obtain ⟨hx19m, _, hx21m, _, hx23m, _, _, hx26m, hx27m, hx28m, hx29m, hvregsm⟩ := hcsm
        simp only [wp_norm, arm64_norm] at hx19m hx21m hx23m hx26m hx27m hx28m hx29m hvregsm
        dsimp only [rustCliDeallocBudgetSpec, F_kyber]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun hpost_pure => ?_
        have htrm : sm.trace = s.trace := by
          have h1 := hpost_pure.1.2.1
          simp only [wp_norm, arm64_norm] at h1
          exact h1
        wp_steps
        refine SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *],
           ?_,
           ⟨rustDeallocEvents k.ciphertext.length 1,
            FreeOnlyEvs.singleton 1 k.ciphertext.length, ?_⟩⟩
        · unfold tailRegs
          simp only [wp_norm, arm64_norm, *]
        · intro mem F hm
          simp only [wp_norm, arm64_norm] at hm
          have hb := words64At_three_entails (s.sp + 2816#64) w3 w4 w5
          simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.words64At,
            sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd] at hb
          have hk := kyberSome_entails (s.sp + 2208#64) kyPtr
            (BitVec.ofNat 64 k.ciphertext.length) k.preKeyId
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hk
          have hm1 : mem ⊨
              A.pool lim (M.stepEvents (rustDeallocEvents k.ciphertext.length 1) st) sm ∗
              stackAt s.sp allocHookStack ∗
              ((s.sp + 2512#64) ↦₆₄ w3) ∗ ((s.sp + 2520#64) ↦₆₄ w4) ∗
              ((s.sp + 2528#64) ↦₆₄ w5) ∗ ((s.sp + 2816#64) ↦₆₄ w3) ∗
              ((s.sp + 2824#64) ↦₆₄ w4) ∗ ((s.sp + 2832#64) ↦₆₄ w5) ∗
              ((s.sp + 2208#64) ↦₆₄ kyPtr) ∗
              ((s.sp + 2216#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗
              ((s.sp + 2224#64) ↦₃₂ k.preKeyId) ∗ memRegion (s.sp + 2228#64) 4 ∗ F :=
            Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm
          have hm2 := Satisfies.mono (kyberPost_four' hb hk) hm1
          simp only [RustCliAllocBudget.pool_setPC]
          exact Eq.mp (congrArg (mem ⊨ ·) (by sep_ac_rfl)) hm2

/-! ## 3. Tail Steppers & `EncTailsVPlaced` / `EncEnvFullBudget` Dischargers -/

theorem tailPreKeyEncryptErrPlaced [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {x : WithStoresEncGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {Hp : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {kyPtr : BitVec 64} {kp : Option KyberPayload}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ Hp)
      R s0 s)
    (hT1 : ∀ st' s',
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s' →
      EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st' answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
        R s0 s' →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        encRecord Hk x st_init R s0 s' (fun _ => False)) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) := by
  have hn : allocHookStack ≤ encSubStack := by decide
  have hrun : (lsProg_464 Hk).CodeLoaded s.mem →
      ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
        ∃ st', EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
          x st_init st' answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
          R s0 s' := fun hL => by
    obtain ⟨st', s', hsteps, htr, htail⟩ :=
      encTail_placed_run_withEncCommon (C := C) (Hk := Hk)
        (pc' := encEntryPlaced + 0x46c#64)
        (regs' := tailRegs w0 w1 w2)
        (slots' := fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
        (Act := memRegion (s0.sp - 0xbe0#64 + 0x9d0#64) 24 ∗
          words64At (s0.sp - 0xbe0#64 + 0xb00#64) [w3, w4, w5] ∗
          optKyberAt A.repAlloc (s0.sp - 0xbe0#64 + 0x8a0#64) kyPtr kp ∗
          A.pool lim st s ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
        (Act' := fun st' s' => words64At (s0.sp - 0xbe0#64 + 0x9d0#64) [w3, w4, w5] ∗
          memRegion (s0.sp - 0xbe0#64 + 0xb00#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x8a0#64) 24 ∗
          A.pool lim st' s' ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
        (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x436 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x8b8#64) 0x118 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x118 ∗
            memRegion (s0.sp - 0xbe0#64 + 0xb18#64) 0x68) ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordBase
            A.repAlloc (s0.sp - 0xbe0#64) scratch g rec ot ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlotAt
            A.repAlloc (s0.sp - 0xbe0#64) none ∗
          Hp ∗ encCommonPlacedFr A.repAlloc ctl x (x.draws S answers) s0 allocHookStack)
        hs
        (by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st s ctl x (x.draws S answers) s0 _ hn,
            kyberPoll_eq]
          sep_ac_rfl)
        (fun st' s' => by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq, tails_pollWith_3_eq, tails_words64At_3_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st' s' ctl x (x.draws S answers) s0 _ hn,
            kyberDropRecordPoll_eq]
          sep_ac_rfl)
        (fun hpc hmeta hregs => by
          obtain ⟨hrun, hssp, _, hspal, hx29, _, _, _⟩ := hmeta
          rw [← hssp] at hregs ⊢
          exact kyber_placed_run hdealloc_sat w0 w1 w2 w3 w4 w5 kyPtr kp st s hpc hrun hspal
            (by rw [hx29, hssp]; bv_omega) hregs)
        hL
    exact ⟨s', hsteps, htr, st', htail⟩
  exact segExit_placed_of_run hm hrun fun s' hm' hnext =>
    let ⟨st', htail⟩ := hnext
    hT1 st' s' hm' htail

theorem tailPreKeyEncryptErrBudgetPlaced [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {x : WithStoresEncGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {Hp : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {kyPtr : BitVec 64} {kp : Option KyberPayload}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ Hp)
      R s0 s)
    (hT1 : ∀ st' s',
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s' →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st' answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
        (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
        R s0 s' →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        encRecord Hk x st_init R s0 s' (fun _ => False)) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) := by
  have hn : allocHookStack ≤ encSubStack := by decide
  have hrun : (lsProg_464 Hk).CodeLoaded s.mem →
      ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
        ∃ st', EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
          x st_init st' answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
          (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
            (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
          R s0 s' := fun hL => by
    obtain ⟨st', s', hsteps, htr, htail⟩ :=
      encTailBudget_run_withEncCommon (C := C) (Hk := Hk)
        (pc' := encEntryPlaced + 0x46c#64)
        (regs' := tailRegs w0 w1 w2)
        (slots' := fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
        (Act := memRegion (s0.sp - 0xbe0#64 + 0x9d0#64) 24 ∗
          words64At (s0.sp - 0xbe0#64 + 0xb00#64) [w3, w4, w5] ∗
          optKyberAt A.repAlloc (s0.sp - 0xbe0#64 + 0x8a0#64) kyPtr kp ∗
          A.pool lim st s ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
        (Act' := fun st' s' => words64At (s0.sp - 0xbe0#64 + 0x9d0#64) [w3, w4, w5] ∗
          memRegion (s0.sp - 0xbe0#64 + 0xb00#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x8a0#64) 24 ∗
          A.pool lim st' s' ∗ stackAt (s0.sp - 0xbe0#64) allocHookStack)
        (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x436 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x8b8#64) 0x118 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x118 ∗
            memRegion (s0.sp - 0xbe0#64 + 0xb18#64) 0x68) ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordBase
            A.repAlloc (s0.sp - 0xbe0#64) scratch g rec ot ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlotAt
            A.repAlloc (s0.sp - 0xbe0#64) none ∗
          Hp ∗ encCommonPlacedFr A.repAlloc ctl x (x.draws S answers) s0 allocHookStack)
        hs
        (by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st s ctl x (x.draws S answers) s0 _ hn,
            kyberPoll_eq]
          sep_ac_rfl)
        (fun st' s' => by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq, tails_pollWith_3_eq, tails_words64At_3_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st' s' ctl x (x.draws S answers) s0 _ hn,
            kyberDropRecordPoll_eq]
          sep_ac_rfl)
        (fun hpc hmeta hregs => by
          obtain ⟨hrun, hssp, _, hspal, hx29, _, _, _⟩ := hmeta
          rw [← hssp] at hregs ⊢
          exact kyber_placed_run hdealloc_sat w0 w1 w2 w3 w4 w5 kyPtr kp st s hpc hrun hspal
            (by rw [hx29, hssp]; bv_omega) hregs)
        hL
    exact ⟨s', hsteps, htr, st', htail⟩
  exact segExitBudget_of_run hm hrun fun s' hm' hnext =>
    let ⟨st', htail⟩ := hnext
    hT1 st' s' hm' htail

theorem tailPreKeyEncryptErr_placed_ok [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hDropRecord :
      ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
        (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
        (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
        (scratch = curScratch ∨ scratch = cmScratch) →
        ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
          (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
          TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
          SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
          EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
            x st_init st answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
            (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
              (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
          SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
            encRecord Hk x st_init R s0 s (fun _ => False))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (kyPtr : BitVec 64) (kp : Option KyberPayload)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ Hp) R s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) :=
  tailPreKeyEncryptErrPlaced hdealloc_sat hm hs fun st' s' hm' hs' =>
    hDropRecord x st_init st' R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot
      hm' hst hs'

theorem tailPreKeyEncryptErrBudget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdealloc_sat : HookSat Hk lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hDropRecord :
      ∀ (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
        (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
        (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp),
        (scratch = curScratch ∨ scratch = cmScratch) →
        ∀ (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
          (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))),
          TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s →
          SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp →
          EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
            x st_init st answers (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
            (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
              (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s →
          SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
            encRecord Hk x st_init R s0 s (fun _ => False))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (Hp : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (kyPtr : BitVec 64) (kp : Option KyberPayload)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A.repAlloc (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ Hp) R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) :=
  tailPreKeyEncryptErrBudgetPlaced hdealloc_sat hm hs fun st' s' hm' hs' =>
    hDropRecord x st_init st' R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot
      hm' hst hs'

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlacedBudget
