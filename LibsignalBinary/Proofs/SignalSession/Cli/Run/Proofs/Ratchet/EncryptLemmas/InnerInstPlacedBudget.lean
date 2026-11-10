/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Inner Contract Transfer and Slot Proof for `encrypt` (Placed)

Budget-pool counterparts of `W1InnerPlacedOk`, cross-block transfer from Block `464`
(`signal_session_ratchet::encrypt`) to caller blocks `i < 619`, and `cliEncrypt_slot_placed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (instIsLsBlockProg_464 lsProg_464)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (RecordPqEmpty encodeRecord)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded SessionStoreSpec TraceFsSound
  extract_withLsCodeRoLoaded ls_subroutine_ok_rocl_of_block
  subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre withLsRoCl
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (CliGhostHooks StoresGhost cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncDef w1EncryptNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn FilesOkPeer encOk₀ scopeIn scopeKit
)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  withStoresEncPlacedSpecV
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SpqrSendBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (encSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget (
  CliEncryptSlotEnv cliEncrypt_slot_of_inner_placed cliEncrypt_slot_of_inner_placed_pe
  w1IdKitPlaced w1SessKitPlaced withStoresEncPlacedSpecVT_cli withStoresEncPlacedSpecVT_cli_F0
)

/-- Budget-threaded Block-`464` inner `withStoresEncPlacedSpecVT_cli` contract over `P : PEParams` and `H : LibsignalHooks`. -/
def W1InnerPlacedOkH [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer)) : Prop :=
  ∀ (F : FsFiles) (peer : AddrGhost),
    FilesOkPeer Scope F peer.val →
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok (lsProg_464 H) (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))

abbrev W1InnerPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer)) : Prop :=
  W1InnerPlacedOkH ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B Scope sendEnv kitEnv ikitEnv

theorem withStoresEncPlacedSpecVT_cli_F0_rocl [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {EnvP : State → Prop} {xs : WithStoresEncGhost × M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli_F0 F0 A lim kit kitEnv st0 ikit ikitEnv ist0
          Scope C ctl uuidParse S sendEnv encRecord)
        EnvP).pre xs s0 ∗ R) :
    LibsignalCodeRoLoaded lsmpl s0.mem := by
  dsimp only [withEnvPre, withStoresEncPlacedSpecVT_cli_F0] at hpre
  have h1 : s0.mem ⊨
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0
        Scope C ctl uuidParse S sendEnv encRecord).pre xs s0 ∗
      (⌜EnvP s0⌝ ∗
        ⌜64 ≤ xs.1.rest.length ∨
          (∀ r, kit.ScopeAt Scope st0 xs.1.rem.val r → RecordPqEmpty r)⌝ ∗
        F0 ∗ R) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  exact (extract_withLsCodeRoLoaded h1).1

theorem withStoresEncPlacedSpecVT_cli_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {EnvP : State → Prop} {xs : WithStoresEncGhost × M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim kit kitEnv st0 ikit ikitEnv ist0
          Scope C ctl uuidParse S sendEnv encRecord)
        EnvP).pre xs s0 ∗ R) :
    LibsignalCodeRoLoaded lsmpl s0.mem :=
  withStoresEncPlacedSpecVT_cli_F0_rocl hpre

/-- Transfers `W1InnerPlacedOkH` from Block `464` (`lsProg_464 H`) to any caller block `i < 619`. -/
theorem w1_inner_placed_at_block_pe [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [hcaller : IsLsBlockProg callerProg i H]
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hInner464 : W1InnerPlacedOkH P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hi : i < 619 := by decide)
    (F : FsFiles) (peer : AddrGhost) (hok : FilesOkPeer Scope F peer.val) :
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok callerProg (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit P.C 0#64 uuidTryParse (pqxdhSpqrModel P) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) := by
  intro kit ikit
  have hsub := hInner464 F peer hok
  have hwrap := subroutine_ok_withLsCodeRoLoaded_of_plain (pl := lsmpl) hsub
  have htr := @ls_subroutine_ok_rocl_of_block _ _ callerProg (lsProg_464 H)
    i 464 H hcaller (instIsLsBlockProg_464 H)
    (lsmpl.base 464) _ hwrap _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono htr (fun xs R s0 hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · have hrocl := withStoresEncPlacedSpecVT_cli_rocl hpre
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hrocl, hpre⟩
  · dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

theorem w1_inner_placed_at_block [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hInner464 : W1InnerPlacedOk mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hi : i < 619 := by decide)
    (F : FsFiles) (peer : AddrGhost) (hok : FilesOkPeer Scope F peer.val) :
    let kit := w1SessKitPlaced A.repAlloc B F peer
    let ikit := w1IdKitPlaced A.repAlloc B F peer
    subroutine_ok callerProg (lsmpl.base 464)
      (withEnvPre
        (withStoresEncPlacedSpecVT_cli A lim
          kit (kitEnv F peer) StoresGhost.opened.sessions
          ikit (ikitEnv F peer) StoresGhost.opened.identity
          scopeKit W.C 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩) sendEnv encodeRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) :=
  w1_inner_placed_at_block_pe ⟨W.C, W.Q⟩ A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))
    B Scope sendEnv kitEnv ikitEnv hInner464 hi F peer hok

/-- Establishes budget-threaded `encSlotSpecPlaced` for `signal_session_ratchet::encrypt` on any caller block `i < 619`. -/
theorem cliEncrypt_slot_placed_pe [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) [IsLsBlockProg callerProg i H]
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hInner464 : W1InnerPlacedOkH P A lim H B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef P Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (encSlotSpecPlaced A lim (CliEncryptSlotEnv P A B sendEnv kitEnv ikitEnv) S stk) :=
  cliEncrypt_slot_of_inner_placed_pe P A lim B S Scope sendEnv kitEnv ikitEnv hfs hinjK hsub hS hok
    (w1_inner_placed_at_block_pe P A lim H B Scope sendEnv kitEnv ikitEnv hInner464 hi)
    stk hstk hstk64

theorem cliEncrypt_slot_placed [LibsignalPlacement] {callerProg : Program} {i : Nat}
    {M : AllocCostModel} (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (sendEnv : SpqrSendBudgetEnv)
    (kitEnv : ∀ F peer, SessionStoreBudgetEnv (w1SessKitPlaced A.repAlloc B F peer))
    (ikitEnv : ∀ F peer, IdentityStoreBudgetEnv (w1IdKitPlaced A.repAlloc B F peer))
    (hfs : TraceFsSound callerProg)
    (hInner464 : W1InnerPlacedOk mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : S.encrypt = w1EncDef ⟨W.C, W.Q⟩ Scope)
    (hok : ∀ F peer me coins, S.filesOk F peer me → S.encOk F peer coins →
      FilesOkPeer Scope F peer ∧ encOk₀ Scope F peer coins)
    (stk : Nat) (hstk : w1EncryptNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 464)
      (encSlotSpecPlaced A lim (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv kitEnv ikitEnv) S stk) :=
  cliEncrypt_slot_of_inner_placed W A lim B S Scope sendEnv kitEnv ikitEnv hfs hinjK hsub hS hok
    (w1_inner_placed_at_block mmpl gh W A lim B Scope sendEnv kitEnv ikitEnv hInner464 hi)
    stk hstk hstk64

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
