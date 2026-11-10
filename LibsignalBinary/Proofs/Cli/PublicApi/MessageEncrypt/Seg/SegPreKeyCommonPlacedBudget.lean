/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget

/-!
# Budget-Threaded Shared Helpers for `segPreKey`

Defines `FromPreKeyRetEnv` and `FromPreKeyEncEnv` allocation envelopes with non-vacuity witnesses,
external hook `subroutine_ok` lemmas, and `SegExitBudget` / panic bridges on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins

export LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (pendingKyberPayload preKeyMsgFromItems PreKeyPostEncryptEnv)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. `SegPreKey` Allocation Sub-Envelopes (`FromPreKeyRetEnv`, `FromPreKeyEncEnv`) -/

/-- Remaining allocation envelope after `bl OTR::encrypt` returns on the `PreKey` path (`+0x8c8`). -/
def FromPreKeyRetEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs' : List AllocEvent) : Prop :=
  PreKeyPostEncryptEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items evs'

/-- Remaining allocation envelope at `+0x8b4` right before `bl OTR::encrypt` on the `PreKey` path. -/
def FromPreKeyEncEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs : List AllocEvent) : Prop :=
  SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext (some x.loc) x.rem x.rest)
    (FromPreKeyRetEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items) evs

/-- Non-vacuity witness for `FromPreKeyRetEnv`. -/
theorem fromPreKeyRetEnv_fitsEnv_witness :
    FitsEnv LibsignalBinary.Heap.Fine.fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      LibsignalBinary.Heap.Fine.fineCostModel.init
      (FromPreKeyRetEnv
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessCrypto
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessSpqrModel
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessUuidParse
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessKit
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessKitEnv ()
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessIkit
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessIkitEnv ()
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessWithStoresGhost
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessEncSession
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessOtr
        { LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessEncSession.state with pqRatchetState := [] }
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessIdentityKey
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessPendingPreKey) := by
  exact LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget.preKeyFromRetEnv_fitsEnv_witness

/-- Non-vacuity witness for `FromPreKeyEncEnv`. -/
theorem fromPreKeyEncEnv_fitsEnv_witness :
    FitsEnv LibsignalBinary.Heap.Fine.fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      LibsignalBinary.Heap.Fine.fineCostModel.init
      (FromPreKeyEncEnv
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessCrypto
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessSpqrModel
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessSendEnv
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessUuidParse
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessKit
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessKitEnv ()
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessIkit
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessIkitEnv ()
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessWithStoresGhost
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessEncSession
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessOtr
        { LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessEncSession.state with pqRatchetState := [] }
        LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.witnessIdentityKey
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.witnessPendingPreKey) := by
  exact LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget.preKeyFromEncryptEnv_fitsEnv_witness

/-! ## 2. External Hook `subroutine_ok` Lemmas (`timeAddBudgetSpec`, `durationSinceBoundedBudgetSpec`) -/

theorem timeAdd_budget_ok_at_enc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_464 Hk)
      (lsρ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        timeAddBudgetSpec) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem
    (by decide : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym ∈
      libsignalSessionExterns)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) env.timeAddVm

theorem durationSince_budget_ok_at_enc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk) :
    subroutine_ok (lsProg_464 Hk)
      (lsρ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsDurationSinceSym)
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet
        durationSinceBoundedBudgetSpec) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem
    (by decide : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsDurationSinceSym ∈
      libsignalSessionExterns)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) env.durationSinceVm

/-! ## 3. `SegExitBudget` / `SepWPp` Combinators & Panic / Retag Bridges -/

theorem segExitBudget_trans [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s mid)
    (h2 : ∀ sm, mid sm → SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord Hk x st_init R0 s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem onPanicBudget_absorb_extra [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {s0 sf : State} {R0 : SepProp}
    (h : sf.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) :
    sf.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R0 := by
  dsimp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨h.1, ?_⟩
  rw [← sepConj_assoc] at h
  exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) h.2

theorem segExitBudget_of_sepWPp_lscro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 s : State} {target : BitVec 64}
    {P : SepProp} {next : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ P ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWPp (lsProg_464 Hk) target s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
        (sf.mem ⊨ P_f ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) → next sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)) →
        (sf.mem ⊨
          (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
            (x, st_init) s0 sf ∗
          (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0)))) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, onPanicBudget_absorb_extra (hqp hmf)⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem onPanic_of_unack_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hm : sf.mem ⊨ (⌜(∃ items', ({ sess with state := taken } : Session (List (BitVec 8))).pendingPreKey = some items' ∧
        SystemTime.unixEpoch.checkedAddSecs items'.timestamp.toNat = none) ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R := by
  dsimp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨⟨items', hpk', hts⟩, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  simp only [hpk, Option.some.injEq] at hpk'
  subst hpk'
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, preKeyErrAnswers r, hsc.2, ?_, ?_⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_unack_panic hcur hfrom hrem hpk hts)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem onPanic_of_timeAdd_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts : SystemTime} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hm : sf.mem ⊨ (⌜ts.checkedAddSecs maxUnacknowledgedSessionAge = none ∧
      s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R := by
  dsimp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hexp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  refine ⟨⟨hpref0, preKeyErrAnswers r, hsc.2, ?_, ?_⟩, ?_⟩
  · rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  · exact Or.inl (model_of_timeAdd_panic hcur hfrom hrem hpk hts hexp)
  · exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm

theorem onPanic_of_otrEnc_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {items : PendingPreKey}
    {ts expiry : SystemTime} {sp pqCap pqPtr : BitVec 64} {s0 s sf : State} {F R : SepProp}
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hts : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts)
    (hexp : ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry)
    (hlt : expiry.lt x.now = false)
    (hm : sf.mem ⊨ (⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
        S.sendPanics otr.pqrState x.rest) ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ∗ R) :
    sf.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R := by
  dsimp only [withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
  rcases hm with ⟨⟨hp, hpref⟩, hm⟩
  rw [← sepConj_assoc] at hm
  have hpref0 : s0.trace <+: sf.trace := by
    refine List.IsPrefix.trans ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩ ?_
    rwa [← htr]
  have htr' : s0.trace ++ kit.loadEvs encRecord x.rem.val (preKeyErrAnswers r).loadSession <+: sf.trace := by
    rw [show (preKeyErrAnswers r).loadSession = .ok (some r) from rfl, ← htr]
    exact hpref
  refine ⟨⟨hpref0, preKeyErrAnswers r, hsc.2, htr', ?_⟩,
    Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm⟩
  rcases hp with hotr | hsp
  · exact Or.inl (model_of_otr_panic hcur hfrom hrem hpk hts hexp hlt hotr)
  · refine Or.inr ?_
    unfold EncryptGhost.sendPanics
    rw [sendState_of_not_stale hcur hfrom hrem hpk hts hexp hlt]
    exact ⟨otr.pqrState, rfl, hsp⟩

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
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

theorem preKey_encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
