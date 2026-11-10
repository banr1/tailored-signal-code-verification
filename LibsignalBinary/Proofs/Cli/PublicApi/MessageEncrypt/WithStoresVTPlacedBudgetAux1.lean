/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalErrPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalOk
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalErr
public import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Aux 1): Environment Bridges and `SegSignal`

Bridges `Seg1PlacedBudgetAux.EncEnvTPlaced` to `EncEnvTBudget` and `EncEnvTFullBudget`, lifts
`h45_segLoad_placed_okVT` and `h45_segIdentity_placed_okVT` to `PlacedDefsBudget` seam types, and
proves `h45_segSignal_placed_okVT` on Block `464` (`lsProg_464 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget (
  SegSignalRetStateVPlaced
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced
  SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced
  SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName
  cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced
  encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym
  lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec
  otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced
  withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed
  withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding
  EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok
  tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok
  tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `EncEnvTPlaced` → `EncEnvTBudget` / `EncEnvTFullBudget` Bridges & `SegLoad`/`SegIdentity` Wrappers -/

private theorem subroutine_ok_dropSs_tempTwins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (StoreKit.withLsRoCl lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim))) :
    subroutine_ok prog entry
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)) :=
  subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => by
      dsimp only [StoreKit.withLsRoCl,
        LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
        dropSessionStructureLocal2BudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec,
        RustCliAllocBudget.atState] at hp ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.2.1, hp.1⟩, hp.2.2⟩)
    (fun ⟨x, st⟩ _ s0 sf hq => by
      dsimp only [StoreKit.withLsRoCl,
        LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
        dropSessionStructureLocal2BudgetSpec,
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      refine ⟨hq.1, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq
      rw [sepExists_sepConj_left, satisfies_sepExists]
      obtain ⟨evs, hevs⟩ := hq.2
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hevs
      rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hevs.1.2, hevs.1.1, hevs.2⟩)

theorem h45_envTBudget_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H) :
    WithStoresVT.Seg4PlacedBudget.EncEnvTBudget F A lim kit (PlacedDefsBudget.toTempTwinsKitEnv kitEnv) st0
      ikit (PlacedDefsBudget.toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl parse S sendEnv encRecord H where
  hooks := hEnv.hooks.toTempTwins
  ikitOk := PlacedDefsBudget.toTempTwinsIkitOk hEnv.ikitOk
  callees := {
    remoteIk := hEnv.callees.remoteIk
    otrEnc := hEnv.callees.otrEnc
    unack := hEnv.callees.unack
  }
  vtables := hEnv.vtables
  idVtables := hEnv.idVtables
  scopeIn := hEnv.scopeIn
  scopeQ := hEnv.scopeQ
  recOk := hEnv.recOk

theorem h45_envTFullBudget_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H)
    (hTails : WithStoresVT.Seg1PlacedBudgetAux.EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl parse S sendEnv encRecord H) :
    WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F A lim kit (PlacedDefsBudget.toTempTwinsKitEnv kitEnv) st0
      ikit (PlacedDefsBudget.toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl parse S sendEnv encRecord H where
  toEncEnvTBudget := h45_envTBudget_of_placed hEnv
  kitOk := PlacedDefsBudget.toTempTwinsKitOk hEnv.kitOk
  calleesFull := {
    toEncCalleesTBudget := (h45_envTBudget_of_placed hEnv).callees
    otrFrom := hEnv.callees.otrFrom
    otrApply := hEnv.callees.otrApply
    kyber := hEnv.callees.kyber
    psmNew := hEnv.callees.psmNew
    dropSs := subroutine_ok_dropSs_tempTwins hEnv.callees.dropSs
  }
  timeAddVm := hEnv.hooks.timeAdd
  durationSinceVm := hEnv.hooks.durationSince
  memcpyVm := hEnv.hooks.memcpy
  tailDropRecord := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailDropRecord
  tailSignalEncryptErr := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailSignalEncryptErr
  tailCmDrop := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailCmDrop
  tailStoreHookErr := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailStoreHookErr
  tailFromSessionStateErr := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailFromSessionStateErr
  tailPreKeyEncryptErr := fun {Scope'} =>
    (hTails (kit := kit) (kitEnv := kitEnv) (st0 := st0) (Scope := Scope')).tailPreKeyEncryptErr

theorem h45_segLoad_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : WithStoresVT.Seg1PlacedBudgetAux.EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨
      (PlacedDefsBudget.withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).pre
        (x, st_init) s0 ∗ R) :
    PlacedDefsBudget.SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s0
      (fun s' => ∃ st' r g sess,
        PlacedDefsBudget.CurStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') :=
  WithStoresVT.Seg5PlacedBudget.h45_segLoad_placed_okVT (h45_envTFullBudget_of_placed hEnv hTails)
    x st_init R s0 hfs hpc0 hrun0 hal0 hm0

theorem h45_segIdentity_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (hotr : PlacedDefsBudget.OtrStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr R0 s0 s) :
    PlacedDefsBudget.SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ k,
        PlacedDefsBudget.KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st r sess otr taken pqCap pqPtr k R0 s0 s') :=
  WithStoresVT.Seg4PlacedBudget.h45_segIdentity_placed_okVT (h45_envTBudget_of_placed hEnv)
    x st_init st r sess otr taken pqCap pqPtr R0 s0 s hotr

/-! ## 2. `SegSignal` (`h45_segSignal_ok_path_placed`, `h45_segSignal_err_path_pf_placed`, `h45_segSignal_placed_okVT`) -/

private theorem pqCap_add_one_ne_zero_placed {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem segSignal_list_len3_placed {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

private theorem signalMessageWordsAt_eq_words64At_placed (gm : SignalMessageGhost) (sm : SignalMessage)
    (a : BitVec 64) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt gm sm a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [gm.pqCap, gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
        BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
        m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem signalMessageAt_relocate_placed (A : RustAlloc) (gm : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A gm src sm ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) := by
  have hm' := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A gm src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨hpq, hm'⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨m7, m8, m9, m10, m11, m12, m14, hm'⟩ := hm'
  rw [signalMessageWordsAt_eq_words64At_placed, sepConj_assoc] at hm'
  refine ⟨gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
    BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A gm sm m7 m8 m9 m10 m11 m12 m14,
    pqCap_add_one_ne_zero_placed hpq, hm', ?_⟩
  intro dst
  rw [← signalMessageWordsAt_eq_words64At_placed]
  exact signalMessageAt_pack A gm dst sm m7 m8 m9 m10 m11 m12 m14

private def segSignalOkFramePlaced [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (draws : Nat) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x3f0#64) 120 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x508 ∗
  memRegion (sp + 0xb18#64) 0x68 ∗
  memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_ok_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (k : IdentityKey) (sm : SignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp)
    (s0 s : State)
    (hm : s.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :
    ∃ (pqCap' pqPtr' : BitVec 64) (gm : SignalMessageGhost)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) ∧
      (s.mem ⊨ (words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15]) ∗
        (segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr'
          k draws sp H s0 ∗ R)) := by
  unfold signalMessageResultAt at hm
  dsimp only at hm
  have hm1 : s.mem ⊨
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqCap', hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqPtr', hm1⟩ := hm1
  have hm2 : s.mem ⊨
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨gm, hm2⟩ := hm2
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H, hpq, hm3, hpack⟩ :=
    signalMessageAt_relocate_placed A gm (sp + 0x580#64) sm hm2
  have h370 : memRegion (sp + 0x370#64) 0xf8 =
      memRegion (sp + 0x370#64) 128 ∗ memRegion (sp + 0x3f0#64) 120 :=
    segSignal_memRegion_cut (sp + 0x370#64) (sp + 0x3f0#64) 0xf8 128 120 (by bv_omega) (by decide) (by decide)
  have h5f8 : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗
        (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68) := by
    rw [segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  rw [h370, h5f8] at hm3
  have hm_d : s.mem ⊨ memRegion (sp + 0x370#64) (8 * 16) ∗
      (memRegion (sp + 0xb00#64) (8 * 3) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) := by
    unfold segSignalOkFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm3
  obtain ⟨ds, hds_len, hm_d⟩ := memRegion_exists_words64At 16 (sp + 0x370#64) (by decide) hm_d
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :=
    segSignal_list_len16 ds hds_len
  have hm_v : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗
      (words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15] ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_d
  obtain ⟨vs, hvs_len, hm_v⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm_v
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3_placed vs hvs_len
  refine ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_v

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_ok_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (sm : SignalMessage) (gm : SignalMessageGhost)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp) (s0 s1 : State)
    (hpack : ∀ dst : BitVec 64,
      words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ⊢ signalMessageAt A gm dst sm)
    (hPm : Pm ⊢ words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗
      words64At (sp + 0xb00#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14])
    (hm : s1.mem ⊨ Pm ∗ (segSignalOkFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g sess taken otr'
      pqCap' pqPtr' k draws sp H s0 ∗ R)) :
    s1.mem ⊨ cmSlots A sp sess taken otr' pqCap' pqPtr' k (.signalMessage sm) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold segSignalOkFramePlaced at hm1
  have h370_hd :
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14] =
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
        words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14] := rfl
  rw [h370_hd] at hm1
  have h580 :
      words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14] ⊢ memRegion (sp + 0x580#64) 120 :=
    words64At_entails_memRegion
      [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
      (sp + 0x580#64) (by simp only [List.length_cons, List.length_nil]; decide)
  have hb00 :
      words64At (sp + 0xb00#64) [w4, w5, w6] ⊢ memRegion (sp + 0xb00#64) 24 :=
    words64At_entails_memRegion [w4, w5, w6] (sp + 0xb00#64)
      (by simp only [List.length_cons, List.length_nil]; decide)
  have hsm_ex :
      words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗ H ⊢
      ∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm :=
    Entails.trans (hpack ((sp + 0x370#64) + 8#64)) (Entails.sepExists_right gm (Entails.refl _))
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.sepExists_right g (Entails.refl _)
  have hm_rearr : s1.mem ⊨
      ((words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        words64At (sp + 0xb00#64) [w4, w5, w6]) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗ memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x508 ∗
      memRegion (sp + 0xb18#64) 0x68 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hsm_ex (sepConj_mono hrec_ex (sepConj_mono h580 hb00))))
    hm_rearr
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68))) := by
    rw [segSignal_memRegion_cut (sp + 0x46a#64) (sp + 0x580#64) 0x716 0x116 0x600 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x580#64) (sp + 0x5f8#64) 0x600 120 0x588 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  have h3f0 : (sp + 0x370#64) + 0x80#64 = sp + 0x3f0#64 := by bv_omega
  have hm_poll : s1.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68)))) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
      (∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm) ∗
      memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold cmSlots takenSlots apiEncResultAt
  dsimp only
  rw [h3f0]
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm_poll

theorem h45_segSignal_ok_path_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
      x st_init st r sess otr taken k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hbud, hcur, hsc, hfrom, hrem, hnone, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, g, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]
    change s0.sp - 0x60#64 = (s0.sp - 0xbe0#64) + 0xb80#64
    bv_omega
  rw [hok] at hm
  obtain ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, hm_unp⟩ :=
    segSignal_placed_ok_unpack (A.atState lim st s) ctl x g sess taken (segSignalRes C S x otr).2 k sm
      (S.draws otr.pqrState x.rest) sp R s0 s hm
  refine SegExitBudget.of_sepWP hm_unp
    (segSignal_placed_step_ok hs_pc hrun hsp hal hx25 hx26 hx29' hpq) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x19, hs1_x20, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_ok := segSignal_placed_ok_pack (A.atState lim st s) ctl x g sess taken (segSignalRes C S x otr).2
    pqCap' pqPtr' k sm gm w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
    (S.draws otr.pqrState x.rest) sp H R Pm1 s0 s1 hpack hPm1 hm1
  rw [(A.atState_eq_of_vmPreserved lim st hvm01).symm] at hm1_ok
  have hbud' : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess (segSignalRes C S x otr).2 taken k) :=
    hbud.narrow (fun _ hev => Or.inr hev)
  have hstep5 : EncEncryptStep C S uuidTryParse x sess otr (.signalMessage sm) (segSignalRes C S x otr).2 := by
    unfold EncEncryptStep
    rw [hnone]
    exact ⟨sm, execOk_of_exec_ok hok, rfl⟩
  refine SegExitBudget.next ⟨st, .signalMessage sm, (segSignalRes C S x otr).2, pqCap', pqPtr',
    hbud', ⟨hcur, hsc, hfrom, hrem, hstep5⟩, ?_⟩
  dsimp only [retagSessionStore, retagIdentityStore]
  exact ⟨hs1_pc, ⟨hs1_run, hs1_sp, hal0, hs1_al, hs1_x29.trans hx29, hs1_x19.trans hx19,
      hcrl1, hs1_vregs.trans hvregs⟩, hs1_tr.trans htr,
    ⟨hs1_x20.trans hx20, hs1_x25.trans hx25, hs1_x26.trans hx26, hs1_x28.trans hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm1_ok⟩

set_option maxHeartbeats 800000 in
theorem h45_segSignal_err_path_pf_placed [LibsignalPlacement]
    {F0 : SepProp} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
      x st_init st r sess otr taken k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  obtain ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hnp, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr, _hx20, hx25, hx26, hx28,
    _hpt, _hrest, _hloc, _hnow, hstk, g, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hp_pan : p ≠ .panic := by
    rintro rfl
    exact hnp herr
  rw [herr] at hm
  simp only [signalMessageResultAt, errResultAt, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨pqCap', pqPtr', hm⟩ := hm
  rw [show speAt (A.atState lim st s) = speAt A.repAlloc from rfl] at hm
  have hst : speAt A.repAlloc (utf8 "encrypt") (sp + 0x588#64) p ⊢
      ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
        ⌜SpeStaged A.repAlloc x.ret (.protocol p) ws H⌝ ∗ words64At (sp + 0x588#64) ws ∗ H :=
    speStaged_of_encErrAt A.repAlloc (sp + 0x588#64) x.ret (.protocol p) (by intro h; cases h)
  have hm1 := segSignal_apply hst (by sep_focus) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ws, H, hm1⟩ := hm1
  obtain ⟨hstg, hm1⟩ := segSignal_pure_front hm1
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := segSignal_list_len6 ws hstg.2.1
  have hsplit : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb00#64) 24 ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    rw [show (0x588 : Nat) = 0x508 + (24 + 0x68) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x508 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x508) 24 _ (by decide)]
  have hm2 := segSignal_apply (Entails.of_eq_explicit hsplit) (by sep_focus) hm1
  have hm2' : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗ _ :=
    segSignal_apply (Entails.refl _) (by sep_focus) hm2
  obtain ⟨vs, hvs, hm3⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm2'
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3 vs hvs
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, hsp0]
    bv_omega
  have hm4 := segSignal_focusR (T := ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗ words64At (sp + 0xb00#64) [v0, v1, v2])
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm3
  refine SegExitBudget.of_sepWP hm4 (segSignal_placed_step_err hs_pc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 _hL hsteps hs3_pc hs3_run hm5
    ⟨hvm03, hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm6 := Satisfies.mono (sepConj_mono_left hPm3) hm5
  rw [← sepConj_assoc] at hm6
  have hm7 := segSignal_apply (segSignal_err_tail_ent (A.atState lim st s) sp g sess taken k pqCap' pqPtr'
    (segSignalRes C S x otr).2 w0 w1 w2 w3 w4 w5) (by sep_focus) hm6
  rw [show dropRecordSlots (A.atState lim st s) = dropRecordSlots A.repAlloc from rfl,
    (A.atState_eq_of_vmPreserved lim st hvm03).symm] at hm7
  have hmod := segSignal_model_err (C := C) (S := S) (x := x) hcur hnone hfrom hrem
    (execOk_of_exec_error herr)
  have hdraws := (segSignal_sendState (S := S) (x := x) (c := .newOrUnchanged) hcur hnone hfrom hrem).2
  refine hEnv.tailSignalEncryptErr x st_init st R0 s0 s3
    (okAnswers r .newOrUnchanged) (.protocol p)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) g (takenRecord sess taken)
    (some (pqCap', pqPtr', (segSignalRes C S x otr).2)) ?_ hstg ⟨hbud.narrow (fun _ hev => Or.inl hev), ?_⟩
  · refine ⟨⟨by rw [hmod, segSignal_ofProtocol hp_pan], by rw [hmod]; exact ⟨hsc.2, trivial⟩,
      by rw [hmod]; trivial⟩, ?_⟩
    rw [hs3_tr, htr, hmod, ikit.traceOfWith_load]; rfl
  · refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19,
      hcrl3, hs3_vregs.trans hvregs⟩, ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstk, ?_⟩
    dsimp only [retagSessionStore, retagIdentityStore]
    rw [hdraws, hmod, ← hsp0]
    dsimp [encStoreExtraPlaced, encSpillsAtV]
    unfold encStoreExtraPlaced encSpillsAtV at hm7
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm7

theorem h45_segSignal_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg1PlacedBudgetAux.EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : WithStoresVT.Seg1PlacedBudgetAux.EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hnone : sess.pendingPreKey = none)
    (hkey : PlacedDefsBudget.KeyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R0) s0 s) :
    WithStoresVT.Seg4PlacedBudget.h45_SegExitVTPlaced F0 A lim kit (PlacedDefsBudget.toTempTwinsKitEnv kitEnv) st0
      ikit (PlacedDefsBudget.toTempTwinsIkitEnv ikitEnv) ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        PlacedDefsBudget.CmStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R0) s0 s') := by
  let envT := h45_envTBudget_of_placed hEnv
  let envFull := h45_envTFullBudget_of_placed hEnv hTails
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segSignal_to_ack_placed envT x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R0) s0 s hnone hkey)) ?_
  intro s1 hack
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segSignal_ack_to_enc_placed envT x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R0) s0 s1 hack)) ?_
  intro s2 henc
  refine WithStoresVT.Seg4PlacedBudget.h45_segExitVT_trans_placed
    (WithStoresVT.Seg5PlacedBudgetAux.h45_segSignal_enc_to_ret_pf_placed envT x st_init st r sess otr taken pqCap pqPtr k R0 s0 s2 h64 henc) ?_
  rintro s3 ⟨st3, hret⟩
  cases hres : (segSignalRes C S x otr).1 with
  | ok sm =>
    exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
      (h45_segSignal_ok_path_placed x st_init st3 r sess otr taken k (F0 ∗ R0) s0 s3 sm hres hret)
  | error p =>
    exact WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_false_placed
      (WithStoresVT.Seg4PlacedBudget.h45_segExitVT_of_segExit_placed
        (h45_segSignal_err_path_pf_placed envFull x st_init st3 r sess otr taken k (F0 ∗ R0) s0 s3 p hres hret))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1
