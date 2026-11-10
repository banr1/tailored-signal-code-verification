/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CmDropPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable `CiphertextMessage` Drop Tail (`+0xd40..+0xd4c` → `+0x46c`)

Proves `cmDrop_placed_run` and `tailCmDrop_placed_ok` on Block `464` (`lsProg_464 Hk`) under
`RustCliAllocBudget M` and `[LibsignalPlacement]`, invoking `cmDropSpec` (`FreeOnlyEvs`) and
continuing into `tailDropRecord`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CmDropPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet)
open CryptoGames.LibsignalSessionApi
  (ApiError CiphertextMessage SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (blkPC_464 blkPl_464 lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (encEntryPlaced)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost apiEncResultAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost cmScratch curScratch encSubStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
  (SpeStaged TailModel dropRecordSlots pollWith tailRegs)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (cmDropSpec)
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

/-! ## 1. Representation & `ProtocolErr` Alignment Bridges -/

private theorem apiEncResultAt_ok_atState_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (p : BitVec 64) (m : CiphertextMessage) :
    apiEncResultAt (A.atState lim st s) p (.ok m) = apiEncResultAt A.repAlloc p (.ok m) := by
  cases m <;> rfl

private theorem tails_dropRecordSlots_eq (A : RustAlloc) (sp : BitVec 64)
    (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots A sp scratch g rec ot cm poll =
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots
        A sp scratch g rec ot cm poll :=
  rfl

/-! ## 2. Packet `SepWP` (`+0xd40 → bl 438 → +0x46c`) -/

theorem cmDrop_placed_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {Hk : LibsignalHooks}
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)))
    (w0 w1 w2 : BitVec 64) (m : CiphertextMessage) (st : M.σ) (s : State)
    (hpc : s.pc = encEntryPlaced + 0xd40#64) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : tailRegs w0 w1 w2 s.sp s) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x46c#64) s
      (apiEncResultAt A.repAlloc (s.sp + 0x370#64) (.ok m) ∗
        A.pool lim st s ∗ stackAt s.sp (allocHookStack + 0x40))
      (fun s' P =>
        s'.sp = s.sp ∧ s'.trace = s.trace ∧
        s'.readReg64 .x19 = s.readReg64 .x19 ∧
        s'.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s' = calleeSavedVRegs s ∧
        tailRegs w0 w1 w2 s.sp s' ∧
        ∃ evs, FreeOnlyEvs evs ∧
          ∀ mem F, (mem ⊨ P ∗ F) →
            (mem ⊨ (memRegion (s.sp + 0x370#64) 248 ∗
              A.pool lim (M.stepEvents evs st) s' ∗
              stackAt s.sp (allocHookStack + 0x40)) ∗ F)) := by
  obtain ⟨hx26, hx28, hx27, hx21, hx23⟩ := hregs
  have hcall : subroutine_ok ((blkPC_464).rebase (blkPl_464).base Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)) := by
    simpa only [lsProg_464, ite_true] using hdrop
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps
  refine SepWP.call_subroutine_frame hcall
    (x := (s.sp + 0x370#64, m, st))
    (F := emp)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm] at hal ⊢; exact hal)
    rfl
    ?_
    (fun _ _ _ hp => by
      dsimp only [withLsRoCl, cmDropSpec, Spec.onPanic] at hp
      exact not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => by
      dsimp only [withLsRoCl, cmDropSpec, Spec.onExit] at he
      exact not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => by
      dsimp only [withLsRoCl, cmDropSpec, Spec.onOom] at ho
      exact False.elim (not_satisfies_false_sepConj ho))
  · intro R hm
    dsimp only [withLsRoCl, cmDropSpec,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.cmDropSpec]
    rw [apiEncResultAt_ok_atState_eq, emp_sepConj]
    simp (config := { decide := true }) only [RustCliAllocBudget.atState_pool, wp_norm, arm64_norm] at hm ⊢
    exact ⟨hcrl, hm⟩
  · intro sm hpcm hrunm hspm hcsm
    simp only [wp_norm, arm64_norm] at hpcm hspm
    obtain ⟨hx19m, _, hx21m, _, hx23m, _, _, hx26m, hx27m, hx28m, hx29m, hvregsm⟩ := hcsm
    simp only [wp_norm, arm64_norm] at hx19m hx21m hx23m hx26m hx27m hx28m hx29m hvregsm
    simp only [wp_norm, arm64_norm] at hx26 hx28 hx27 hx21 hx23
    rw [sepConj_emp]
    dsimp only [withLsRoCl, cmDropSpec,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.cmDropSpec,
      RustCliAllocBudget.atState_pool]
    refine SepWP.pure_elim fun _hcrlm =>
      SepWP.exists_elim fun evs =>
        SepWP.pure_elim fun hevs =>
          SepWP.pure_elim fun htrm => ?_
    simp only [wp_norm, arm64_norm] at htrm ⊢
    wp_steps
    refine SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *],
       ?_, ⟨evs, hevs, ?_⟩⟩
    · unfold tailRegs
      simp only [wp_norm, arm64_norm, *]
    · intro mem F hm
      simpa only [sepConj_assoc, RustCliAllocBudget.pool_setPC,
        RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_advancePC] using hm

/-! ## 3. Tail Stepper & `EncTailsVPlaced` / `EncEnvBudget` Dischargers -/

theorem tailCmDropPlaced [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)))
    {x : WithStoresEncGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {Hp : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {m : CiphertextMessage}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
        (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
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
  have hn : allocHookStack + 0x40 ≤ encSubStack := by decide
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
        (Act := apiEncResultAt A.repAlloc (s0.sp - 0xbe0#64 + 0x370#64) (.ok m) ∗
          A.pool lim st s ∗ stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
        (Act' := fun st' s' => memRegion (s0.sp - 0xbe0#64 + 0x370#64) 248 ∗
          A.pool lim st' s' ∗ stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
        (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x350#64) 0x20 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x468#64) 1) ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordBase
            A.repAlloc (s0.sp - 0xbe0#64) scratch g rec ot ∗
          pollWith (s0.sp - 0xbe0#64) 0x9d0 [w3, w4, w5] ∗
          Hp ∗ encCommonPlacedFr A.repAlloc ctl x (x.draws S answers) s0 (allocHookStack + 0x40))
        hs
        (by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st s ctl x (x.draws S answers) s0 _ hn]
          simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlotAt]
          sep_ac_rfl)
        (fun st' s' => by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st' s' ctl x (x.draws S answers) s0 _ hn,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlot_none_eq]
          sep_ac_rfl)
        (fun hpc hmeta hregs => by
          obtain ⟨hrun, hssp, _, hspal, _, _, hcrl, _⟩ := hmeta
          rw [← hssp] at hregs ⊢
          exact cmDrop_placed_run hdrop w0 w1 w2 m st s hpc hrun hspal hcrl hregs)
        hL
    exact ⟨s', hsteps, htr, st', htail⟩
  exact segExit_placed_of_run hm hrun fun s' hm' hnext =>
    let ⟨st', htail⟩ := hnext
    hT1 st' s' hm' htail

theorem tailCmDropBudgetPlaced [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
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
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)))
    {x : WithStoresEncGhost} {st_init st : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {e : ApiError AddrVal Unit}
    {w0 w1 w2 w3 w4 w5 : BitVec 64} {Hp : SepProp} {scratch : BitVec 64 → SepProp}
    {g : RecordGhost} {rec : SessionRecord (List (BitVec 8))}
    {ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8)))}
    {m : CiphertextMessage}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
        (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp)
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
  have hn : allocHookStack + 0x40 ≤ encSubStack := by decide
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
        (Act := apiEncResultAt A.repAlloc (s0.sp - 0xbe0#64 + 0x370#64) (.ok m) ∗
          A.pool lim st s ∗ stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
        (Act' := fun st' s' => memRegion (s0.sp - 0xbe0#64 + 0x370#64) 248 ∗
          A.pool lim st' s' ∗ stackAt (s0.sp - 0xbe0#64) (allocHookStack + 0x40))
        (Fr := (memRegion (s0.sp - 0xbe0#64 + 0x350#64) 0x20 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x468#64) 1) ∗
          CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordBase
            A.repAlloc (s0.sp - 0xbe0#64) scratch g rec ot ∗
          pollWith (s0.sp - 0xbe0#64) 0x9d0 [w3, w4, w5] ∗
          Hp ∗ encCommonPlacedFr A.repAlloc ctl x (x.draws S answers) s0 (allocHookStack + 0x40))
        hs
        (by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st s ctl x (x.draws S answers) s0 _ hn]
          simp only [CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlotAt]
          sep_ac_rfl)
        (fun st' s' => by
          refine Entails.of_eq ?_
          rw [tails_dropRecordSlots_eq,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.dropRecordSlots_eq,
            encCommonPlaced_eq A lim st' s' ctl x (x.draws S answers) s0 _ hn,
            CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.cmSlot_none_eq]
          sep_ac_rfl)
        (fun hpc hmeta hregs => by
          obtain ⟨hrun, hssp, _, hspal, _, _, hcrl, _⟩ := hmeta
          rw [← hssp] at hregs ⊢
          exact cmDrop_placed_run hdrop w0 w1 w2 m st s hpc hrun hspal hcrl hregs)
        hL
    exact ⟨s', hsteps, htr, st', htail⟩
  exact segExitBudget_of_run hm hrun fun s' hm' hnext =>
    let ⟨st', htail⟩ := hnext
    hT1 st' s' hm' htail

theorem tailCmDrop_placed_ok [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)))
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
    (m : CiphertextMessage)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
        (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) :=
  tailCmDropPlaced hdrop hm hs fun st' s' hm' hs' =>
    hDropRecord x st_init st' R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot
      hm' hst hs'

theorem tailCmDropBudget_placed_ok [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
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
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 438)
      (withLsRoCl lsmpl (cmDropSpec M A lim)))
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
    (m : CiphertextMessage)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] Hp)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A.repAlloc sp scratch g rec ot (some m)
        (pollWith sp 0x9d0 [w3, w4, w5]) ∗ Hp) R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord Hk x st_init R s0 s (fun _ => False) :=
  tailCmDropBudgetPlaced hdrop hm hs fun st' s' hm' hs' =>
    hDropRecord x st_init st' R s0 s' answers e w0 w1 w2 w3 w4 w5 Hp scratch hscr g rec ot
      hm' hst hs'

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CmDropPlacedBudget
