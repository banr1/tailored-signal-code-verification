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
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable T5 Protocol-Error Tail Bridges

Provides `FreeOnlyEvs` budget-advancement helpers (`seamBudget_step_freeOnly`), retag transport
lemmas, and `encTail_placed_run*` / `segExit_placed_of_run` combinators on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi
  (ApiError CiphertextMessage SessionRecord StoreAnswers StoreCall)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (encCommonPlaced encMidMetaPlaced encStoreExtraPlaced)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost encSpillsAtV encSubStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon (TailModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser protocolAddressAt)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (EncTailVBudget SeamBudget SegExitBudget SpqrSendBudgetEnv retagIdentityStore retagSessionStore)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncTailVPlaced SegExitPlaced toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (encTailVPlaced_eq_tempTwins segExitPlaced_eq_tempTwins)

set_option maxRecDepth 200000

/-! ## 1. `SeamBudget` & Retag Transport Helpers -/

theorem seamBudget_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st FreeOnlyEvs) (hstep : FreeOnlyEvs evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) FreeOnlyEvs :=
  (h.narrow (by rintro _ (h1 | ⟨_, _, rfl, h1, h2⟩); exact h1; exact h1.append h2)).advance hstep

theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc :=
  rfl

theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S parse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S parse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S parse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S parse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

theorem encCommonPlaced_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 s1 s2 : State)
    (hvm : VmPreserved s1 s2) :
    encCommonPlaced (A.atState lim st s1) ctl x draws s0 =
      encCommonPlaced (A.atState lim st s2) ctl x draws s0 := by
  rw [(A.atState_eq_of_vmPreserved lim st hvm).symm]

/-! ## 2. `TempTwins` Steppers (`encTailBudget_run*`, `segExitBudget_of_run`) -/

theorem encTailBudget_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init st : M.σ}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' Act Fr : BitVec 64 → SepProp}
    {Act' : BitVec 64 → SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers pc regs slots R s0 s)
    (hsplit : ∀ sp, slots sp ⊢ Act sp ∗ Fr sp)
    (hjoin : ∀ sp, Act' sp ∗ Fr sp ⊢ slots' sp)
    (hwp : ∀ sp, s.pc = pc → encMidMetaPlaced x s0 s → regs sp s → sp = s0.sp - 0xbe0#64 →
      SepWP (lsProg_464 Hk) pc' s (Act sp)
        (fun s' P => VmPreserved s s' ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' sp s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' sp ∗ F)))
    (hL : (lsProg_464 Hk).CodeLoaded s.mem) :
    ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st answers pc' regs' slots' R s0 s' := by
  rcases hs with ⟨hbud, hpc, hmeta, hregs, hstk, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers
      (slots (s0.sp - 0xbe0#64)) R s0)) hmem
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hcrl, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act (s0.sp - 0xbe0#64) ∗ (Fr (s0.sp - 0xbe0#64) ∗
      (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗
        (encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
          ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R))) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hsplit _)) hmem
  obtain ⟨s', hsteps,
      ⟨hpc', hrun', P, hmP, hvm', hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ |
      ⟨_, _hoom⟩⟩ :=
    (hwp _ hpc hmeta hregs rfl).elim hmem2 hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', hbud, hpc',
    ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
      hcrl.of_keepsFrozen hsteps.keepsFrozen, hvregs'.trans hvregs⟩,
    hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · refine Eq.mpr (congrArg (s'.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers
        (slots' (s0.sp - 0xbe0#64)) R s0)) ?_
    have h1 := hent _ _ hmP
    rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s' hvm',
        ← sepConj_assoc] at h1
    exact Satisfies.mono (sepConj_mono_left (hjoin _)) h1

theorem segExitBudget_of_run [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
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
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit}
    {res : Except (ApiError AddrVal Unit) CiphertextMessage} {next : State → Prop}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s)
    (hrun : (lsProg_464 Hk).CodeLoaded s.mem →
      ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧ next s')
    (hnext : ∀ s', TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s' →
      next s' →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R s0 s' (fun _ => False)) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨s', h1, htr, hn⟩ := hrun hL
  obtain ⟨sf, h2, hout⟩ := hnext s' ⟨hm.1, htr.trans hm.2⟩ hn (h1.codeLoaded hL)
  exact ⟨sf, h1.trans h2, hout⟩

theorem encTailBudget_run_withEncCommon [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init st : M.σ}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' : BitVec 64 → SepProp}
    {Act Fr : SepProp} {Act' : M.σ → State → SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers pc regs slots R s0 s)
    (hsplit :
      slots (s0.sp - 0xbe0#64) ∗ encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ⊢
        Act ∗ Fr)
    (hjoin : ∀ st' s',
      Act' st' s' ∗ Fr ⊢
        slots' (s0.sp - 0xbe0#64) ∗
          encCommonPlaced (A.atState lim st' s') ctl x (x.draws S answers) s0)
    (hwp : s.pc = pc → encMidMetaPlaced x s0 s → regs (s0.sp - 0xbe0#64) s →
      SepWP (lsProg_464 Hk) pc' s Act
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s' = calleeSavedVRegs s ∧
          regs' (s0.sp - 0xbe0#64) s' ∧
          ∃ evs, FreeOnlyEvs evs ∧
            ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' (M.stepEvents evs st) s' ∗ F)))
    (hL : (lsProg_464 Hk).CodeLoaded s.mem) :
    ∃ st' s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st' answers pc' regs' slots' R s0 s' := by
  let R' := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R
  rcases hs with ⟨hbud, hpc, hmeta, hregs, hstk, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers
      (slots (s0.sp - 0xbe0#64)) R s0)) hmem
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hcrl, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act ∗ (Fr ∗ (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗ R')) := by
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left hsplit) ?_
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; sep_ac_rfl)) hmem
  obtain ⟨s', hsteps,
      ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', evs, hevs, hent⟩ |
      ⟨_, _hoom⟩⟩ :=
    (hwp hpc hmeta hregs).elim hmem2 hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨M.stepEvents evs st, s', hsteps, htr', seamBudget_step_freeOnly hbud hevs, hpc',
    ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
      hcrl.of_keepsFrozen hsteps.keepsFrozen, hvregs'.trans hvregs⟩,
    hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · refine Eq.mpr (congrArg (s'.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers
        (slots' (s0.sp - 0xbe0#64)) R s0)) ?_
    have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    have h2 := Satisfies.mono (sepConj_mono_left (hjoin (M.stepEvents evs st) s')) h1
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; sep_ac_rfl)) h2

/-! ## 3. Canonical `PlacedDefsBudget` Steppers (`encTail_placed_run*`, `segExit_placed_of_run`) -/

theorem encTail_placed_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init st : M.σ}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' Act Fr : BitVec 64 → SepProp}
    {Act' : BitVec 64 → SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers pc regs slots R s0 s)
    (hsplit : ∀ sp, slots sp ⊢ Act sp ∗ Fr sp)
    (hjoin : ∀ sp, Act' sp ∗ Fr sp ⊢ slots' sp)
    (hwp : ∀ sp, s.pc = pc → encMidMetaPlaced x s0 s → regs sp s → sp = s0.sp - 0xbe0#64 →
      SepWP (lsProg_464 Hk) pc' s (Act sp)
        (fun s' P => VmPreserved s s' ∧ s'.sp = s.sp ∧ s'.trace = s.trace ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' sp s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' sp ∗ F)))
    (hL : (lsProg_464 Hk).CodeLoaded s.mem) :
    ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st answers pc' regs' slots' R s0 s' := by
  rw [encTailVPlaced_eq_tempTwins] at hs
  simpa only [encTailVPlaced_eq_tempTwins] using encTailBudget_run hs hsplit hjoin hwp hL

theorem segExit_placed_of_run [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit}
    {res : Except (ApiError AddrVal Unit) CiphertextMessage} {next : State → Prop}
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s)
    (hrun : (lsProg_464 Hk).CodeLoaded s.mem →
      ∃ s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧ next s')
    (hnext : ∀ s', TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s' →
      next s' →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R s0 s' (fun _ => False)) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  rw [segExitPlaced_eq_tempTwins]
  exact segExitBudget_of_run hm hrun fun s' hm' hn' => by
    simpa only [segExitPlaced_eq_tempTwins] using hnext s' hm' hn'

theorem encTail_placed_run_withEncCommon [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init st : M.σ}
    {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' : BitVec 64 → SepProp}
    {Act Fr : SepProp} {Act' : M.σ → State → SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers pc regs slots R s0 s)
    (hsplit :
      slots (s0.sp - 0xbe0#64) ∗ encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ⊢
        Act ∗ Fr)
    (hjoin : ∀ st' s',
      Act' st' s' ∗ Fr ⊢
        slots' (s0.sp - 0xbe0#64) ∗
          encCommonPlaced (A.atState lim st' s') ctl x (x.draws S answers) s0)
    (hwp : s.pc = pc → encMidMetaPlaced x s0 s → regs (s0.sp - 0xbe0#64) s →
      SepWP (lsProg_464 Hk) pc' s Act
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧
          s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s' = calleeSavedVRegs s ∧
          regs' (s0.sp - 0xbe0#64) s' ∧
          ∃ evs, FreeOnlyEvs evs ∧
            ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' (M.stepEvents evs st) s' ∗ F)))
    (hL : (lsProg_464 Hk).CodeLoaded s.mem) :
    ∃ st' s', Steps (lsProg_464 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st' answers pc' regs' slots' R s0 s' := by
  rw [encTailVPlaced_eq_tempTwins] at hs
  simpa only [encTailVPlaced_eq_tempTwins] using
    encTailBudget_run_withEncCommon hs hsplit hjoin hwp hL

/-! ## 4. `encCommonPlacedFr` & `encCommonPlaced_eq` -/

abbrev encCommonPlacedFr [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) (n : Nat) : SepProp :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonPlacedFr
    A ctl x draws s0 n

theorem encCommonPlaced_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 : State)
    (n : Nat) (hn : n ≤ encSubStack) :
    encCommonPlaced (A.atState lim st s) ctl x draws s0 =
      (A.pool lim st s ∗ stackAt (s0.sp - 0xbe0#64) n) ∗
        encCommonPlacedFr A.repAlloc ctl x draws s0 n :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr.encCommonPlaced_eq
    (A.atState lim st s) ctl x draws s0 n hn

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.ProtocolErrCommonPlacedBudget
