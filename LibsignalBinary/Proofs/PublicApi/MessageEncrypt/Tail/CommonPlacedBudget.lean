/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlaced

/-!
# Budget-Threaded Relocatable Tail Definitions and `SegExitPlaced` Bridges

Pairs `SeamBudget ... FreeOnlyEvs` with `Pf.TailCommon.EncTailVPlaced` over `A.atState lim st s` on
Block `198` (`lsProg_198 H`), and lifts `SepWP` proofs to `PlacedDefsBudget.SegExitPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
  (SegExitPlaced WithStoresEncEnv encStoreExtraPlaced_retag idFinal_retag storeFinal_retag
   withStoresEncPlacedSpecV)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_198)
open CryptoVerification.LibsignalPublicApi.StoreKit (IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost encCommonPlaced encSpillsAtV encStoreExtraPlaced)

/-- Budget-threaded relocatable tail entry state on Block `198` (`lsProg_198 H`) with
`FreeOnlyEvs` remaining until return. -/
def EncTailVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  SeamBudget M lim
    (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x)
    st_init st FreeOnlyEvs ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 C ctl parse S
    x answers pc regs slots R s0 s

abbrev EncTailVBudget := @EncTailVPlaced

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
  have hs := storeFinal_retag (A' := A') kit st0 answers (x.model C S parse answers).2
  have hi := idFinal_retag (A' := A') ikit ist0 answers (x.model C S parse answers).2
  have hext :
      encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S parse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S parse answers).2)
        x s0 =
      encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S parse answers).2)
        x s0 := by
    rw [encStoreExtraPlaced_retag, hs, hi]
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

theorem segExit_placed_of_sepWP_ret [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {P R : SepProp} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_198 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) ∧
        (P_f ⊢ (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
          C ctl parse S sendEnv encRecord).post (x, st_init) s0 sf))) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf⟩, hent⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩)⟩
  exact Satisfies.mono (sepConj_mono_left hent) hmf

theorem segExit_placed_of_sepWP [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {target_pc : BitVec 64} {P R' R : SepProp}
    {post : State → SepProp → Prop} {Next : State → Prop} {s0 s : State}
    (hm : s.mem ⊨ P ∗ R')
    (hwp : SepWP (lsProg_198 H) target_pc s P post)
    (hnext : ∀ s1 P_f, Steps (lsProg_198 H) s s1 →
      s1.pc = target_pc → s1.status = .Running → (s1.mem ⊨ P_f ∗ R') → post s1 P_f →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl parse S sendEnv encRecord H x st_init R s0 s1 Next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R s0 s Next := by
  intro hL
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hmf1, hpost1⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps2, hout⟩ :=
    hnext s1 P_f hsteps1 hpc1 hrun1 hmf1 hpost1 (hsteps1.codeLoaded hL)
  exact ⟨sf, hsteps1.trans hsteps2, hout⟩

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
