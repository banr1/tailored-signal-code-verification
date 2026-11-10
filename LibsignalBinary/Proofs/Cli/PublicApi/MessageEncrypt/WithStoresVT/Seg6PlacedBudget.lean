/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 6): `SegSignal` Ok/Err and `SegPreKey` Prefix

Completes `h45_segSignal_placed_okVT` and exports the `SegPreKey` prefix lemmas (`+0x344..+0x8b4`)
on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg6PlacedBudget

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal (segSignalRes)
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  CmStateVBudget EncEnvBudget IdentityStoreBudgetEnv KeyStateVBudget SegExitBudget
  SessionStoreBudgetEnv SpqrSendBudgetEnv
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  EncEnvFullBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget (
  SegSignalRetStateVPlaced segSignal_placed_ok_path
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalErrPlacedBudget (
  segSignal_placed_err_path_pf
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlacedBudget (
  StalenessAddStateBudget StalenessDurStateBudget
  segPreKey_staleness_to_add_placed_ok segPreKey_unackItems_to_dur_placed_ok
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailPlacedBudget (
  PreKeyEncryptStateBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStalePlacedBudget (
  segPreKey_stale_placed_ok
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget (
  segPreKey_regId_kyber_placed_ok
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget (
  EncEnvTBudget h45_SegExitVTPlaced h45_segExitVT_of_false_placed h45_segExitVT_of_segExit_placed
  h45_segExitVT_trans_placed h45_segSignal_ack_to_enc_placed h45_segSignal_to_ack_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget (
  h45_segSignal_enc_to_ret_pf_placed
)

/-! ## 1. `SegSignal` `Ok`/`Err` Paths & `h45_segSignal_placed_okVT` -/

theorem h45_segSignal_ok_path_placed [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (envB : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope (fun _ => False) C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st r sess otr taken k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') :=
  segSignal_placed_ok_path envB x st_init st r sess otr taken k R0 s0 s sm hok hs

theorem h45_segSignal_err_path_pf_placed [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (envB : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope (fun _ => False) C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st r sess otr taken k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  segSignal_placed_err_path_pf envB x st_init st r sess otr taken k R0 s0 s p herr hs

theorem h45_segSignal_placed_okVT [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (envB : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope (fun _ => False) C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hpk : sess.pendingPreKey = none)
    (hs : KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k (F0 ∗ R_frame) s0 s) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R_frame s0 s
      (fun s' => ∃ st' m otr' pqCap' pqPtr',
        CmStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R_frame) s0 s') := by
  refine h45_segExitVT_trans_placed
    (h45_segExitVT_of_segExit_placed (h45_segSignal_to_ack_placed hEnv x st_init st r sess otr taken pqCap pqPtr k
      (F0 ∗ R_frame) s0 s hpk hs))
    fun sm h =>
      h45_segExitVT_trans_placed
        (h45_segExitVT_of_segExit_placed (h45_segSignal_ack_to_enc_placed hEnv x st_init st r sess otr taken pqCap pqPtr k
          (F0 ∗ R_frame) s0 sm h))
        fun sn h' =>
          h45_segExitVT_trans_placed
            (h45_segSignal_enc_to_ret_pf_placed hEnv x st_init st r sess otr taken pqCap pqPtr k R_frame s0 sn h64 h')
            fun sr ⟨st_ret, hret⟩ => ?_
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact h45_segExitVT_of_false_placed
      (h45_segExitVT_of_segExit_placed (h45_segSignal_err_path_pf_placed hEnv envB x st_init st_ret r sess otr taken k
        (F0 ∗ R_frame) s0 sr p hres hret))
  · exact h45_segExitVT_of_segExit_placed
      (h45_segSignal_ok_path_placed hEnv envB x st_init st_ret r sess otr taken k
        (F0 ∗ R_frame) s0 sr m hres hret)

/-! ## 2. `SegPreKey` Prefix (`+0x344..+0x8b4`) -/

theorem h45_segPreKey_unackItems_to_dur_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        StalenessDurStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') :=
  segPreKey_unackItems_to_dur_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items R0 s0 s hpk hkey

theorem h45_segPreKey_staleness_to_add_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : StalenessDurStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ expiry,
        StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') :=
  segPreKey_staleness_to_add_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
    prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s hcur hscope hotr hrem hpk hdur

theorem h45_segPreKey_stale_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) :=
  segPreKey_stale_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
    prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s hcur hscope hotr hrem hpk hlt hadd

theorem h45_segPreKey_regId_kyber_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = false)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 s
      (fun sf => ∃ st',
        PreKeyEncryptStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken pqCap pqPtr k items R s0 sf) :=
  segPreKey_regId_kyber_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
    prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s hcur hscope hpk hlt hadd

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg6PlacedBudget
