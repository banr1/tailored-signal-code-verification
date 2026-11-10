/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk

/-!
# Relocatable Token-Framed CLI `decrypt_signal` (`WithStoresVTPlaced`)

Specializes `WithStoresVT.CorePlaced` (`withStoresDecPlacedSpecVTP` and `withStoresDecPlacedSpecVT`
on `lsProg_463`) to `Slots.trTrapExternsPlaced H` and the placed CLI program
`lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))`, including concrete file-kit
and `withLsFrozen`-guarded corollaries.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.Variant CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record hiding
  recordDecryptPlacedSpec recEntryPlaced recExitPlaced LibsignalCodeRoLoaded
open CryptoVerification.Cli.LibsignalTripleRatchet.Record hiding lsProg_463 LibsignalCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (ScopePq decryptRecord)
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

export WithStoresVT (
  withStoresDecPlacedSpecVTF
  withStoresDecPlacedSpecVT
  withStoresDecPlacedSpecVTPF
  withStoresDecPlacedSpecVTP
  recordDecryptPlacedSpecP
  recordDecryptPlacedSpecTF
  recordDecryptPlacedSpecT
  recordDecryptPlacedSpecTPTightF
  recordDecryptPlacedSpecTPTight
  DecFsCtxExtPlaced
  DecHypsExtPlaced
  DecCalleesTPFPlaced
  DecCalleesTPPlaced
  DecCalleesTPFFrozenPlaced
  DecCalleesTPFrozenPlaced
  DecCalleesTFPlaced
  DecCalleesTPlaced
  withStoresDec_reachVTPF_fs_placed
  withStoresDec_reachVTP_fs_placed
  withStoresDec_reachVTPF_frozen_fs_placed
  withStoresDec_reachVTP_frozen_fs_placed
  withStoresDec_okVTPF_fs_placed
  withStoresDec_okVTP_fs_placed
  withStoresDec_okVTPF_frozen_fs_placed
  withStoresDec_okVTP_frozen_fs_placed
  withStoresDec_okVTPF_distinct_fs_placed
  withStoresDec_okVTP_distinct_fs_placed
  withStoresDec_okVTPF_distinct_frozen_fs_placed
  withStoresDec_okVTP_distinct_frozen_fs_placed
  withStoresDec_okVTPF_placed
  withStoresDec_okVTP_placed
  withStoresDec_okVTF_fs_placed
  withStoresDec_okVT_fs_placed
  withStoresDec_okVTF_placed
  withStoresDec_okVT_placed
)

/-! ## Entry-address and `TrapsOnly` transfer helpers -/

theorem wsEntryPCPlaced_eq_base463 [LibsignalPlacement] :
    wsEntryPCPlaced = lsmpl.base 463 := rfl

theorem wsEntryPCPlaced_eq_fnAddr [LibsignalPlacement] :
    wsEntryPCPlaced =
      libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName :=
  (CryptoVerification.ls_fnAddr_block_ultra (pl := lsmpl) (i := 463) (by decide)).symm

/-- `TrapsOnly` relation from `lsProg_463 (Slots.trTrapExternsPlaced ...)` to `lsProg_463 (RunGlue.cliGhostExterns ...)`. -/
theorem trapsOnly_lsProg_463_trTrap_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks) :
    TrapsOnly
      (lsProg_463 (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  Slots.trapsOnly_rebase_trTrapPlaced_cli blkPC_463 (blkPl_463).base mmpl gh W

/-- Transfers `DecCalleesTPFPlaced` from `Slots.trTrapExternsPlaced` to `RunGlue.cliGhostExterns`. -/
theorem DecCalleesTPFPlaced.of_trTrap_cli [LibsignalPlacement] {F0 : SepProp}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {Q : List (BitVec 8) → Prop}
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (h : DecCalleesTPFPlaced F0 W.C A ctl S
      (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) Q) :
    DecCalleesTPFPlaced F0 W.C A ctl S (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) Q where
  region := region_ok_of_trapsOnly (trapsOnly_lsProg_463_trTrap_cli mmpl gh W) h.region
  remoteIk := Slots.subroutine_ok_cliPlaced_of_trTrap h.remoteIk
  dropSs := Slots.subroutine_ok_cliPlaced_of_trTrap h.dropSs

/-- Transfers `DecCalleesTFPlaced` from `Slots.trTrapExternsPlaced` to `RunGlue.cliGhostExterns`. -/
theorem DecCalleesTFPlaced.of_trTrap_cli [LibsignalPlacement] {F0 : SepProp}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {Q : List (BitVec 8) → Prop}
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (h : DecCalleesTFPlaced F0 W.C A ctl S
      (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) Q) :
    DecCalleesTFPlaced F0 W.C A ctl S (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) Q where
  region := region_ok_of_trapsOnly (trapsOnly_lsProg_463_trTrap_cli mmpl gh W) h.region
  remoteIk := Slots.subroutine_ok_cliPlaced_of_trTrap h.remoteIk
  dropSs := Slots.subroutine_ok_cliPlaced_of_trTrap h.dropSs

/-! ## Trap-program specializations (`Slots.trTrapExternsPlaced H`) -/

/-- Weak-precondition (`RecordInScopeP`) hypothesis bundle at `Slots.trTrapExternsPlaced H`. -/
abbrev DecHypsPPlaced_trap [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A 0#64) (id : IdentityStoreSpec A 0#64)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsExtPlaced C A parse S encRecord (Slots.trTrapExternsPlaced H) ss id st0 Scope

/-- Tight-panic, weak-precondition callee bundle at `Slots.trTrapExternsPlaced H`. -/
abbrev DecCalleesTPFPlaced_trap [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPFPlaced F0 C A ctl S (Slots.trTrapExternsPlaced H) Q

abbrev DecCalleesTPPlaced_trap [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPPlaced C A ctl S (Slots.trTrapExternsPlaced H) Q

/-- `F0`-framed `recordDecryptPlacedSpecTF` callee bundle at `Slots.trTrapExternsPlaced H`. -/
abbrev DecCalleesTFPlaced_trap [LibsignalPlacement] (F0 : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTFPlaced F0 C A ctl S (Slots.trTrapExternsPlaced H) Q

abbrev DecCalleesTPlaced_trap [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : LibsignalHooks) (Q : List (BitVec 8) → Prop) : Prop :=
  DecCalleesTPlaced C A ctl S (Slots.trTrapExternsPlaced H) Q

/-- Constructs `DecCalleesTPFPlaced_trap` at `Q := fun _ => True` from an unconditional region proof. -/
theorem DecCalleesTPFPlaced_trap.of_uncond [LibsignalPlacement] {F0 : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : LibsignalHooks}
    (hDealloc : HookSat (Slots.trTrapExternsPlaced H) lsRustDeallocSym (rustDeallocSpec A))
    (hreg : region_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecTPTightF F0 C A ctl uuidTryParse S).withVRegs) :
    DecCalleesTPFPlaced_trap F0 C A ctl S H (fun _ => True) :=
  DecCalleesTPFPlaced.of_region hDealloc (region_ok_restrictPre_true hreg)

theorem withStoresDec_reachVTP_fs_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hid : IdOrDistinctSid uuidTryParse kit st0 Scope x)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre
        x s0 ∗ R)
    (hal : s0.spAligned = true)
    (hfs : DecFsCtxExtPlaced kit ikit (Slots.trTrapExternsPlaced H) s0 s0) :
    reaches_outcome (lsProg_463 (Slots.trTrapExternsPlaced H))
      (withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
      x R s0 s0 :=
  withStoresDec_reachVTP_fs_placed hH hC hQ x R s0 hid hpc hrun hpre hal hfs

theorem withStoresDec_okVTP_fs_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (Slots.trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTP_distinct_fs_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (Slots.trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre
        ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH hC hQ hKitFs

theorem withStoresDec_okVTP_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) wsEntryPCPlaced
      ((withStoresDecPlacedSpecVTP C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
        (IdOrDistinctSid uuidTryParse kit st0 Scope)) :=
  withStoresDec_okVTP_placed hH hC hQ htriv

theorem withStoresDec_okVT_fs_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (Slots.trTrapExternsPlaced H))) :
    subroutine_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) wsEntryPCPlaced
      (withEnvPre (withStoresDecPlacedSpecVT C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_placed hH hscopeIn hC hQ hKitFs

theorem withStoresDec_okVT_placed_trap [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsPPlaced_trap C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hC : DecCalleesTPlaced_trap C A ctl S H Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_463 (Slots.trTrapExternsPlaced H)) wsEntryPCPlaced
      (withStoresDecPlacedSpecVT C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) :=
  withStoresDec_okVT_placed hH hscopeIn hC hQ htriv

/-! ## Placed CLI program (`lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))`) -/

/-- Constructs `DecHypsExtPlaced` from `PublicApiDecHooksPlaced` and the session/identity store-kit bundles. -/
theorem DecHypsExtPlaced.of_hooks [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {ss : SessionStoreSpec A 0#64} {id : IdentityStoreSpec A 0#64}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hhooks : PublicApiDecHooksPlaced A H)
    (hkit : SessionOnlyKitPlacedOkSE ss Scope encRecord H)
    (hikit : IdentityStoreKitPlacedOkI id H)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExtPlaced C A parse S encRecord H ss id st0 Scope where
  hooks := hhooks
  kit := hkit
  ikit := hikit
  scopeInP := hscopeInP
  recOk := hrecOk

/-- Constructs `DecHypsExtPlaced` at `A0` and `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem DecHypsExtPlaced.of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ss : SessionStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {id : IdentityStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {st0 : ss.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hStrClone : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (CryptoVerification.LibsignalPublicApi.stringCloneSpec CryptoVerification.E2E.HooksE.A0))
    (hkit : SessionOnlyKitPlacedOkSE ss Scope encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI id
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      ss.addrOk x.rem.val →
      ss.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S parse x rec = .ok (pt, rec') →
      ss.RecOk rec') :
    DecHypsExtPlaced W.C CryptoVerification.E2E.HooksE.A0 parse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) ss id st0 Scope :=
  let h := Slots.publicApiDecHooksPlaced_cli mmpl gh W hG hStrClone
  DecHypsExtPlaced.of_hooks
    ⟨h.shim, h.alloc, h.dealloc, h.memcpy, h.stringClone, h.handleError, h.expectFailed⟩
    hkit hikit hscopeInP hrecOk

/-- Discharges `KitFsOk` on `lsProg_463` for any pair of `Quiet` store kits. -/
theorem cliQuietKits_placed_fsOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hFs : RunGlue.CliGhostHooksFs gh) {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    (hq : kit.Quiet ∧ ikit.Quiet) :
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  KitFsOk.of_sound hq (RunGlue.traceFsSound_lsProg_cli_ghost mmpl gh W hFs)

/-- Discharges `KitFsOk` for vtable-overridden `cliSessionStoreSpec` and `cliIdentityStoreSpec` on any `TraceFsSound` program. -/
theorem cliFilesKits_placed_fsOk {A : RustAlloc} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 is1 is2 is3 is4 : Nat}
    {ssVt ssIdVt idVt : BitVec 64} {P : Program}
    (hfs : TraceFsSound P) :
    let kit : SessionStoreSpec A 0#64 :=
      { cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer s1 s2 s3 s4 with
        ss_vt := ssVt, id_vt := ssIdVt }
    let ikit : IdentityStoreSpec A 0#64 :=
      { cliIdentityStoreSpec A 0#64 rd F0 pathOk peer is1 is2 is3 is4 with
        id_vt := idVt }
    KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) P :=
  KitFsOk.of_sound
    ⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
      ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩
    hfs

/-- Placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `IdOrDistinctSid`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH (DecCalleesTPFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Variant of `decryptSignalWithStores_placed_okVTP_fs_cli` transferring `DecCalleesTPPlaced_trap` via `TrapsOnly`. -/
theorem decryptSignalWithStores_placed_okVTP_fs_cli_of_trap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap W.C A ctl S
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_fs_placed hH (DecCalleesTPFPlaced.of_trTrap_cli mmpl gh W hC) hQ hKitFs

/-- Placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `DistinctSid`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH
    (DecCalleesTPFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Variant of `decryptSignalWithStores_placed_okVTP_distinct_fs_cli` transferring `DecCalleesTPPlaced_trap` via `TrapsOnly`. -/
theorem decryptSignalWithStores_placed_okVTP_distinct_fs_cli_of_trap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hC : DecCalleesTPPlaced_trap W.C A ctl S
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) Q)
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_fs_placed hH (DecCalleesTPFPlaced.of_trTrap_cli mmpl gh W hC) hQ hKitFs

/-- Placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVT`, `Scope ⊆ RecordInScope`) on `lsProg_463` for arbitrary kits. -/
theorem decryptSignalWithStores_placed_okVT_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecT W.C A ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre (withStoresDecPlacedSpecVT W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVT_fs_placed hH hscopeIn
    (DecCalleesTFPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Concrete file-kit placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `IdOrDistinctSid`) at `A0`. -/
theorem cliDecryptSignalWithStores_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {ctl : BitVec 64} {S : SpqrModel}
    {kit : SessionStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {ikit : IdentityStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hFs : RunGlue.CliGhostHooksFs gh)
    (hStrClone : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (CryptoVerification.LibsignalPublicApi.stringCloneSpec CryptoVerification.E2E.HooksE.A0))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope CryptoVerification.E2E.Record.encodeRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI ikit
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord kit ikit st0 ist0 Scope).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_fs_cli mmpl gh W
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- Concrete file-kit placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `DistinctSid`) at `A0`. -/
theorem cliDecryptSignalWithStores_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {ctl : BitVec 64} {S : SpqrModel}
    {kit : SessionStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {ikit : IdentityStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hFs : RunGlue.CliGhostHooksFs gh)
    (hStrClone : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (CryptoVerification.LibsignalPublicApi.stringCloneSpec CryptoVerification.E2E.HooksE.A0))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope CryptoVerification.E2E.Record.encodeRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI ikit
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withStoresDecPlacedSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
          CryptoVerification.E2E.Record.encodeRecord kit ikit st0 ist0 Scope).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_placed_okVTP_distinct_fs_cli mmpl gh W
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- `withLsFrozen`-guarded placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `IdOrDistinctSid`). -/
theorem decryptSignalWithStores_frozen_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight W.C A ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_frozen_fs_placed hH (DecCalleesTPFFrozenPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- `withLsFrozen`-guarded placed CLI `decrypt_signal` (`withStoresDecPlacedSpecVTP`, `DistinctSid`). -/
theorem decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hH : DecHypsExtPlaced W.C A uuidTryParse S encRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) kit ikit st0 Scope)
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight W.C A ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope)).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  withStoresDec_okVTP_distinct_frozen_fs_placed hH
    (DecCalleesTPFFrozenPlaced.of_region hH.hooks.dealloc hreg) hQ hKitFs

/-- Concrete file-kit `withLsFrozen`-guarded placed CLI `decrypt_signal` (`IdOrDistinctSid`) at `A0`. -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {ctl : BitVec 64} {S : SpqrModel}
    {kit : SessionStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {ikit : IdentityStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hFs : RunGlue.CliGhostHooksFs gh)
    (hStrClone : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (CryptoVerification.LibsignalPublicApi.stringCloneSpec CryptoVerification.E2E.HooksE.A0))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope CryptoVerification.E2E.Record.encodeRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI ikit
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
            CryptoVerification.E2E.Record.encodeRecord kit ikit st0 ist0 Scope)).restrictPre
          (IdOrDistinctSid uuidTryParse kit st0 Scope))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_fs_cli mmpl gh W
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

/-- Concrete file-kit `withLsFrozen`-guarded placed CLI `decrypt_signal` (`DistinctSid`) at `A0`. -/
theorem cliDecryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    {ctl : BitVec 64} {S : SpqrModel}
    {kit : SessionStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {ikit : IdentityStoreSpec CryptoVerification.E2E.HooksE.A0 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    (hG : Slots.CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hFs : RunGlue.CliGhostHooksFs gh)
    (hStrClone : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (CryptoVerification.LibsignalPublicApi.stringCloneSpec CryptoVerification.E2E.HooksE.A0))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope CryptoVerification.E2E.Record.encodeRecord
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hikit : IdentityStoreKitPlacedOkI ikit
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hq : kit.Quiet ∧ ikit.Quiet)
    (hscopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r)
    (hrecOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
      (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
      kit.addrOk x.rem.val →
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord W.C S uuidTryParse x rec = .ok (pt, rec') →
      kit.RecOk rec')
    (hreg : region_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      recEntryPlaced recExitPlaced
      ((withLsFrozen lsmpl (recordDecryptPlacedSpecTPTight W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S)).withVRegs.restrictPre
        (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope (fun pq => pq.length < 2 ^ 32 ∧ Q pq)) :
    subroutine_ok (lsProg_463 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463)
      (withEnvPre
        ((withLsFrozen lsmpl
          (withStoresDecPlacedSpecVTP W.C CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse S
            CryptoVerification.E2E.Record.encodeRecord kit ikit st0 ist0 Scope)).restrictPre
          (fun x => CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid
            uuidTryParse x.loc.name.bytes x.rem.name.bytes))
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  decryptSignalWithStores_frozen_placed_okVTP_distinct_fs_cli mmpl gh W
    (DecHypsExtPlaced.of_cliHooks mmpl gh W hG hStrClone hkit hikit hscopeInP hrecOk)
    hreg hQ (cliQuietKits_placed_fsOk mmpl gh W hFs hq)

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
