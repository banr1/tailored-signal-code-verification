/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.EntryExit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.ModelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Top
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stack

/-!
# Budget-Threaded Outer Slot Reduction for `decrypt_signal` (Placed)

Defines the exact allocation-event envelope `CliDecryptSignalSlotEnv` for
`signal_session_ratchet::decrypt_signal` (Block `463`) and reduces `decSigSlotSpecPlaced` and
`decSigSlotSpecFrozenPlaced` to the budget-threaded inner store-kit contract.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (
  ApiError SessionRecord StoreAnswers StoreCall messageDecryptSignal
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (satisfies_decVtablesAtV_placed)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decVtablesAtV wsStackV)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles FsInv IdentityVtablesPlacedOk LibsignalCodeRoLoaded NoFsEv
  SessionOnlyVtablesPlacedOk SessionStoreSpec TraceFsSound
  withEnvPre withEnvPre_pre_intro withLsCodeRoLoaded
)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiDecResultAt serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SignalMessageGhost coinsOf protocolAddressAt serviceIdParse
  signalMessageAt uuidTryParse
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (
  DirGhost IdGhost KyberGhost StoresGhost files_eq_at_callback
  subroutine_ok_withFsInv withFsInv withFsInv_entry withFsInv_post_elim withFsInv_pre_intro
)
open CryptoVerification.SignalSession.Cli.KitInst (
  cliIdStoreAt cliIdentityStoreSpec cliSessStoreAt cliSessionStoreSpec
)
open CryptoVerification.SignalSession.Cli.MainHops (
  cliIo cliWrOk coinsInstalledPlaced storesAt
)
open CryptoVerification.SignalSession.Cli.RunCompose (
  Bytes DecSigGhost RunSem decResAt idVtPlaced sessVtPlaced slotOut slotTrace
)
open CryptoVerification.SignalSession.Cli.RunProofs (cliAnswers cliFinal)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (
  apiDecResultAt_entails_decResAt cliIdInv_opened_wrOk cliSessInv_opened_wrOk
  cliStep_foldl_eq decDefAux decDefAux_eq_model decIdKit decIdKit_traceOfWith_nil
  decKeyAux decModel_det decNeedAux decSessKit decSessKit_loadRel_eq
  filesOkPeer_mono messageDecryptSignal_panic_iff_of_load_eq
  storesAt_repack_dec storesAt_unpack_dec storesOther5At toDecryptGhost
  wsStackV_le_cliDecryptSignalNeed
)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (
  cliIdentityStoreSpecPlaced cliSessionStoreSpecPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  DistinctSid EncodeInjOn FilesOkPeer coinsAtPlaced_eq_coinsInstalledPlaced
  scopeIn scopeKit scopeKit_of_scopeIn stackAt_split_of_le
)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget (withStoresDecPlacedSpecV)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (
  withStoresDecPlacedSpecVX
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (
  IdentityStoreBudgetEnv retagIdentityStore
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (
  SessionStoreBudgetEnv retagSessionStore
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (
  decSigSlotSpecPlaced slotFramePlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget (
  decIdKitPlaced decSessKitPlaced withStoresDecPlacedSpecVTP
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## Allocator-parametric kit and representation bridges -/

theorem wsStackV_le_cliDecryptSignalNeed_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    wsStackV (decSessKitPlaced A F0 peer B) (decIdKitPlaced A F0 peer B) ≤ decNeedAux B :=
  wsStackV_le_cliDecryptSignalNeed default F0 peer B

private theorem protocolAddressAt_of_live_eq {A₁ A₂ : RustAlloc} (hlive : A₁.live = A₂.live)
    (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt A₁ g a = protocolAddressAt A₂ g a := by
  cases A₁; cases A₂; dsimp only at hlive; subst hlive; rfl

private theorem signalMessageAt_of_live_eq {A₁ A₂ : RustAlloc} (hlive : A₁.live = A₂.live)
    (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A₁ g a m = signalMessageAt A₂ g a m := by
  cases A₁; cases A₂; dsimp only at hlive; subst hlive
  cases m.addresses <;> rfl

private theorem apiDecResultAt_of_live_eq {A₁ A₂ : RustAlloc} (hlive : A₁.live = A₂.live)
    (r : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    apiDecResultAt A₁ r res = apiDecResultAt A₂ r res := by
  cases A₁; cases A₂; dsimp only at hlive; subst hlive
  cases res with
  | ok _ => rfl
  | error e =>
    cases e with
    | protocol pe =>
      cases pe with
      | invalidMessage _ rsn => cases rsn <;> rfl
      | _ => rfl
    | sessionNotFound _ _ => rfl
    | untrustedIdentity _ => rfl
    | store u => cases u; rfl
    | panic => rfl

private theorem retag_decSessKitPlaced_callsRel_iff [LibsignalPlacement] (A A' : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) (st0 : DirGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') (decSessKitPlaced A F0 peer B)).callsRel st0 ans cs ↔
      (decSessKit default F0 peer B).callsRel st0 ans cs := by
  induction cs generalizing st0 with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [SessionStoreSpec.callsRel] <;>
      first | exact ih _ | exact and_congr_right fun _ => ih _

private theorem retag_decIdKitPlaced_idCallsRel_iff [LibsignalPlacement] (A A' : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) (ist0 : IdGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') (decIdKitPlaced A F0 peer B)).idCallsRel ist0 ans cs ↔
      (decIdKit default F0 peer B).idCallsRel ist0 ans cs := by
  induction cs generalizing ist0 with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [IdentityStoreSpec.idCallsRel] <;>
      first | exact ih _ | exact and_congr_right fun _ => ih _

private theorem retag_decSessKitPlaced_storeFinal_eq [LibsignalPlacement] (A A' : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) (st0 : DirGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') (decSessKitPlaced A F0 peer B)).storeFinal st0 ans cs =
      (decSessKit default F0 peer B).storeFinal st0 ans cs := by
  induction cs generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> exact ih _

private theorem retag_decIdKitPlaced_idFinal_eq [LibsignalPlacement] (A A' : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) (ist0 : IdGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') (decIdKitPlaced A F0 peer B)).idFinal ist0 ans cs =
      (decIdKit default F0 peer B).idFinal ist0 ans cs := by
  induction cs generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> exact ih _

private theorem retag_decIdKitPlaced_traceOfWith_nil [LibsignalPlacement] (A A' : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets)
    (encRec : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') (decIdKitPlaced A F0 peer B)).traceOfWith
      (retagSessionStore (A' := A') (decSessKitPlaced A F0 peer B)) encRec ans cs = [] := by
  have h :
      (retagIdentityStore (A' := A') (decIdKitPlaced A F0 peer B)).callEvs
          (retagSessionStore (A' := A') (decSessKitPlaced A F0 peer B)) encRec ans =
        (decIdKit default F0 peer B).callEvs
          (decSessKit default F0 peer B) encRec ans := by
    funext c
    cases c <;> rfl
  unfold IdentityStoreSpec.traceOfWith
  rw [h]
  exact decIdKit_traceOfWith_nil default F0 peer B encRec ans cs

private def dummyCliHooks (P : PEParams) : CliHooks where
  C := P.C
  Q := P.Q
  bcmp := fun a b => if a = b then 0#64 else 1#64
  bcmp_ok := fun a b _ => by
    by_cases h : a = b <;> simp [h]
  utf8Err := fun _ => (0#64, 0#16)

/-! ## Slot allocation envelope -/

/-- Allocation-event envelope for the `decrypt_signal` wrapper slot (`lsProg_463`), instantiating
`WithStoresDecEnv` at `decSessKitPlaced`, `decIdKitPlaced`, and `StoresGhost.opened`. -/
def CliDecryptSignalSlotEnv [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (x : DecSigGhost) (evs : List AllocEvent) : Prop :=
  WithStoresDecEnv
    (decSessKitPlaced A.repAlloc x.F x.peer B) (kitEnv x.F x.peer)
    StoresGhost.opened.sessions
    (decIdKitPlaced A.repAlloc x.F x.peer B) (ikitEnv x.F x.peer)
    StoresGhost.opened.identity
    P.C (pqxdhSpqrModel P) uuidTryParse tdEnv scopeKit (toDecryptGhost x) evs

/-! ## Separation-logic packing and main reduction -/

private theorem unpack_inner_post {α : Type} {p : α → Prop} {body : α → SepProp}
    {tok FR : SepProp} {m : Memory}
    (hm : m ⊨ (tok ∗ (∃∗ a : α, ⌜p a⌝ ∗ body a)) ∗ FR) :
    ∃ a, p a ∧ (m ⊨ (tok ∗ body a) ∗ FR) := by
  have hperm1 :
      (tok ∗ (∃∗ a : α, ⌜p a⌝ ∗ body a)) ∗ FR =
      (∃∗ a : α, ⌜p a⌝ ∗ body a) ∗ (tok ∗ FR) := by
    sep_ac_rfl
  rw [hperm1, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  have hperm2 : (⌜p a⌝ ∗ body a) ∗ (tok ∗ FR) = ⌜p a⌝ ∗ ((tok ∗ body a) ∗ FR) := by
    sep_ac_rfl
  rw [hperm2, satisfies_pure_sepConj] at hm
  exact ⟨a, hm.1, hm.2⟩

private theorem perm_spat_in
    {vt sess id other5 pa1 pa2 coins tok log pool msg ret stkRem stkWs R : SepProp} :
    vt ∗ (((sess ∗ id ∗ other5) ∗ pa1 ∗ pa2 ∗ coins ∗ tok ∗ log ∗ pool ∗ msg ∗ ret ∗
      (stkRem ∗ stkWs)) ∗ R) =
    (tok ∗ (sess ∗ id ∗ msg ∗ pa1 ∗ pa2 ∗ ret ∗ coins ∗ log ∗ vt ∗ stkWs ∗ pool)) ∗
      ((other5 ∗ stkRem) ∗ R) := by
  sep_ac_rfl

private theorem perm_spat_out
    {tok sess id res msg pa1 pa2 coins log vt stkWs pool other5 stkRem R : SepProp} :
    (tok ∗ (sess ∗ id ∗ res ∗ msg ∗ pa1 ∗ pa2 ∗ coins ∗ log ∗ vt ∗ stkWs ∗ pool)) ∗
      ((other5 ∗ stkRem) ∗ R) =
    ((sess ∗ id ∗ other5) ∗ res ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ (stkRem ∗ stkWs) ∗
      (tok ∗ vt ∗ coins)) ∗ R := by
  sep_ac_rfl

set_option maxHeartbeats 1600000 in
/-- Reduces budget-threaded `decSigSlotSpecPlaced` at `lsmpl.base 463` on `callerProg` to `hInner`,
threading `A.pool lim st` and eliminating `allocFailedIn` on panic. -/
theorem cliDecryptSignal_slot_of_inner_placed_pe [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux P Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      FilesOkPeer scopeIn F0 peer.val →
      let kit := decSessKitPlaced A.repAlloc F0 peer B
      let ikit := decIdKitPlaced A.repAlloc F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (withStoresDecPlacedSpecVTP P.C A lim 0#64 uuidTryParse
            (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
            StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced A lim
        (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hal _hcode => ?_
  dsimp only [decSigSlotSpecPlaced, withLsCodeRoLoaded, slotFramePlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
    DecSigGhost.toSlotCtx] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
        s0.readReg64 .x3 = x.stores + 0xf0#64 ∧ s0.readReg64 .x4 = sessVtPlaced ∧
        s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVtPlaced ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        stk ≤ s0.sp.toNat ∧
        FitsEnv M lim st (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv x)⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (((storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R)))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hfl0, hpre_flat⟩ := hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx8, hfiles0, hfok, hstk_sp, hfit⟩, hpre_flat⟩ :=
    hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoins_lt, hspat⟩ := hpre_flat
  obtain ⟨hokPeer, hdist⟩ := hok x.F x.peer.val x.me.val hfok
  have hokIn : FilesOkPeer scopeIn x.F x.peer.val := filesOkPeer_mono hsub hokPeer
  have hsubK : ∀ r, Scope r → scopeKit r := fun r hr => scopeKit_of_scopeIn (hsub r hr)
  have hsess0 := cliSessInv_opened_wrOk hsubK hokPeer
  have hid0 := cliIdInv_opened_wrOk hokPeer
  let kit := decSessKitPlaced A.repAlloc x.F x.peer B
  let ikit := decIdKitPlaced A.repAlloc x.F x.peer B
  let y := toDecryptGhost x
  have hws_le : wsStackV kit ikit ≤ stk :=
    Nat.le_trans (wsStackV_le_cliDecryptSignalNeed_placed A.repAlloc x.F x.peer B) hstk
  have hws_sp : wsStackV kit ikit ≤ s0.sp.toNat := Nat.le_trans hws_le hstk_sp
  let F := storesOther5At A.repAlloc x.stores StoresGhost.opened ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit)
  have hFs0 : FsInv x.F s0.trace s0 := hfiles0 ▸ withFsInv_entry s0
  have hInnerFs := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokIn) x.F s0.trace
  have hvt0 := satisfies_decVtablesAtV_placed
    (kit := kit) (ikit := ikit) (hvt x.F x.peer) (hivt x.F x.peer) hfl0.2 hspat
  have hspat_unpack :
      decVtablesAtV kit ikit ∗
        ((storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R) ⊢
      (tokenInitPlacedAt ∗
        (kit.storeAt (s0.readReg64 .x3) StoresGhost.opened.sessions ∗
          ikit.identityAt (s0.readReg64 .x5) StoresGhost.opened.identity ∗
          signalMessageAt (A.atState lim st s0) y.msgG y.msgA y.msg ∗
          protocolAddressAt (A.atState lim st s0) y.rem y.remA ∗
          protocolAddressAt (A.atState lim st s0) y.loc y.locA ∗
          memRegion y.ret 48 ∗
          cliTapeAt 0#64 y.cur y.rest ∗
          lsLogOff ∗ decVtablesAtV kit ikit ∗
          stackAt s0.sp (wsStackV kit ikit) ∗ A.pool lim st s0)) ∗ (F ∗ R) := by
    rw [stackAt_split_of_le s0.sp hws_le hstk_sp, hx3, hx5,
      signalMessageAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl,
      protocolAddressAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl,
      protocolAddressAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono_left
          (sepConj_mono
            (storesAt_unpack_dec A.repAlloc x.stores StoresGhost.opened x.F scopeKit x.peer hsess0 hid0)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left
                (Entails.of_eq (coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoins_lt).symm)))))))
      ?_
    dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, cliSessionStoreSpecPlaced,
      cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec, y, toDecryptGhost, F]
    exact Entails.of_eq perm_spat_in
  have hspat_in := Satisfies.mono hspat_unpack hvt0
  have hpre_vt :
      s0.mem ⊨
        (withStoresDecPlacedSpecVTP P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv x.F x.peer) ikit (ikitEnv x.F x.peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit).pre
          (y, st) s0 ∗ (F ∗ R) := by
    dsimp only [withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX, withStoresDecPlacedSpecV,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV,
      withLsCodeRoLoaded]
    have hgoal : s0.mem ⊨
        ⌜DistinctSid uuidTryParse y.loc.name.bytes y.rem.name.bytes⌝ ∗
        (⌜FitsEnv M lim st
            (WithStoresDecEnv kit (kitEnv x.F x.peer) StoresGhost.opened.sessions
              ikit (ikitEnv x.F x.peer) StoresGhost.opened.identity
              P.C (pqxdhSpqrModel P) uuidTryParse tdEnv scopeKit y)⌝ ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = y.msgA ∧ s0.readReg64 .x1 = y.remA ∧ s0.readReg64 .x2 = y.locA ∧
          s0.readReg64 .x4 = (retagSessionStore (A' := A.atState lim st s0) kit).ss_vt ∧
          s0.readReg64 .x6 = (retagIdentityStore (A' := A.atState lim st s0) ikit).id_vt ∧
          s0.readReg64 .x8 = y.ret ∧
          wsStackV (retagSessionStore (A' := A.atState lim st s0) kit)
            (retagIdentityStore (A' := A.atState lim st s0) ikit) ≤ s0.sp.toNat ∧
          (retagSessionStore (A' := A.atState lim st s0) kit).addrOk y.rem.val ∧
          (retagIdentityStore (A' := A.atState lim st s0) ikit).addrOk y.rem.val⌝ ∗
        ((tokenInitPlacedAt ∗
          ((retagSessionStore (A' := A.atState lim st s0) kit).storeAt (s0.readReg64 .x3)
              StoresGhost.opened.sessions ∗
            (retagIdentityStore (A' := A.atState lim st s0) ikit).identityAt (s0.readReg64 .x5)
              StoresGhost.opened.identity ∗
            signalMessageAt (A.atState lim st s0) y.msgG y.msgA y.msg ∗
            protocolAddressAt (A.atState lim st s0) y.rem y.remA ∗
            protocolAddressAt (A.atState lim st s0) y.loc y.locA ∗
            memRegion y.ret 48 ∗
            cliTapeAt 0#64 y.cur y.rest ∗
            lsLogOff ∗
            decVtablesAtV (retagSessionStore (A' := A.atState lim st s0) kit)
              (retagIdentityStore (A' := A.atState lim st s0) ikit) ∗
            stackAt s0.sp (wsStackV (retagSessionStore (A' := A.atState lim st s0) kit)
              (retagIdentityStore (A' := A.atState lim st s0) ikit)) ∗
            (A.atState lim st s0).pool)) ∗ (F ∗ R))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hdist, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfit, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl0, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hws_sp, rfl, rfl⟩, hspat_in⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  have hpre_inner :
      s0.mem ⊨
        (withFsInv
          (withEnvPre
            (withStoresDecPlacedSpecVTP P.C A lim 0#64 uuidTryParse
              (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv x.F x.peer)
              ikit (ikitEnv x.F x.peer)
              StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
            fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)
          x.F s0.trace).pre (y, st) s0 ∗ (F ∗ R) :=
    withFsInv_pre_intro hFs0 (withEnvPre_pre_intro ⟨hfiles0, hfiles0⟩ hpre_vt)
  refine hInnerFs.mono_outcome (y, st) (F ∗ R) s0 hpc hrun hpre_inner hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, honp⟩ | ⟨_code, _hex, honex⟩ | ⟨_hoom, honoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hFsSf, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX,
      withStoresDecPlacedSpecV,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV,
      withLsCodeRoLoaded] at hpost
    obtain ⟨evs, hev, hpost1⟩ := unpack_inner_post hpost
    obtain ⟨answers, ⟨hnpan, _, hcalls_r, hidCalls_r, htr⟩, hspat_out⟩ := unpack_inner_post hpost1
    have htr_nil := retag_decIdKitPlaced_traceOfWith_nil A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B encodeRecord answers
      (y.model P.C (pqxdhSpqrModel P) uuidTryParse answers).2
    rw [htr_nil, List.append_nil] at htr
    have hfiles_sf : sf.fs.files = x.F :=
      files_eq_at_callback hFsSf (evs := []) (by simp [htr]) (by simp [NoFsEv])
    have hslotTrace : slotTrace s0 sf :=
      ⟨by simp [htr], hfiles_sf.trans hfiles0.symm, by simp [htr]⟩
    have hcalls0 := (retag_decSessKitPlaced_callsRel_iff A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.sessions answers _).mp hcalls_r
    have hidCalls0 := (retag_decIdKitPlaced_idCallsRel_iff A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.identity answers _).mp hidCalls_r
    obtain ⟨hmod_eq, hnst, hwrOk⟩ := decModel_det (img := default) (dummyCliHooks P) B Scope x.F
      y answers rfl hinjK hsub hokPeer hcalls0 hidCalls0
    let m := y.model P.C (pqxdhSpqrModel P) uuidTryParse answers
    let g' := cliFinal x.F m.2
    have hfold := cliStep_foldl_eq default x.F x.peer B answers m.2 StoresGhost.opened
    have hsf_eq := retag_decSessKitPlaced_storeFinal_eq A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.sessions answers m.2
    have hif_eq := retag_decIdKitPlaced_idFinal_eq A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.identity answers m.2
    have hans_eq : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins =
        match m.1 with
        | .ok pt => some (some (g', pt))
        | .error .panic => none
        | .error _ => some none := by
      rw [hS]
      have hd := decDefAux_eq_model P Scope x.F y
      dsimp only [y, toDecryptGhost, dummyCliHooks] at hd hmod_eq
      rw [hd, ← hmod_eq]
      change (match m with
        | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
        | (.error .panic, _) => none
        | (.error _, _) => some none) = _
      dsimp only [g']
      rcases m with ⟨res, calls⟩
      cases res with
      | ok pt => rfl
      | error err => cases err <;> rfl
    have hslotOut : slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' m.1 s0 sf := by
      refine ⟨hnpan, hnst, ?_⟩
      rw [hans_eq]
      cases hm1 : m.1 with
      | ok pt => exact ⟨rfl, hwrOk pt hm1⟩
      | error err =>
        cases err with
        | panic => exact absurd hm1 hnpan
        | store u => cases u; exact absurd hm1 hnst
        | protocol _ => rfl
        | sessionNotFound _ _ => rfl
        | untrustedIdentity _ => rfl
    have hrepack :
        (tokenInitPlacedAt ∗
          ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeAt
              (s0.readReg64 .x3)
              ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeFinal
                StoresGhost.opened.sessions answers m.2) ∗
            (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).identityAt
              (s0.readReg64 .x5)
              ((retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).idFinal
                StoresGhost.opened.identity answers m.2) ∗
            apiDecResultAt (A.atState lim (M.stepEvents evs st) sf) y.ret m.1 ∗
            signalMessageAt (A.atState lim (M.stepEvents evs st) sf) y.msgG y.msgA y.msg ∗
            protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.rem y.remA ∗
            protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.loc y.locA ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers) ∗
            lsLogOff ∗
            decVtablesAtV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
              (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit) ∗
            stackAt s0.sp
              (wsStackV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit)) ∗
            (A.atState lim (M.stepEvents evs st) sf).pool)) ∗ (F ∗ R) ⊢
        (storesAt A.repAlloc x.stores g' ∗
          decResAt A.repAlloc x.ret m.1 ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗
          anyHeap) ∗ R := by
      have hst_repack := storesAt_repack_dec A.repAlloc x.stores StoresGhost.opened g'
        x.F scopeKit x.peer hfold.2.2.1 (congrArg KyberGhost.oneTime hfold.2.2.2.1)
        (congrArg KyberGhost.lastResort hfold.2.2.2.1) hfold.2.2.2.2.1 hfold.2.2.2.2.2
      have hres_conv := apiDecResultAt_entails_decResAt A.repAlloc x.ret m.1 hnst
      have hperm_out :
          (tokenInitPlacedAt ∗
            ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeAt
                (s0.readReg64 .x3)
                ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeFinal
                  StoresGhost.opened.sessions answers m.2) ∗
              (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).identityAt
                (s0.readReg64 .x5)
                ((retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).idFinal
                  StoresGhost.opened.identity answers m.2) ∗
              apiDecResultAt (A.atState lim (M.stepEvents evs st) sf) y.ret m.1 ∗
              signalMessageAt (A.atState lim (M.stepEvents evs st) sf) y.msgG y.msgA y.msg ∗
              protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.rem y.remA ∗
              protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.loc y.locA ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers) ∗
              lsLogOff ∗
              decVtablesAtV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit) ∗
              stackAt s0.sp
                (wsStackV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                  (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit)) ∗
              (A.atState lim (M.stepEvents evs st) sf).pool)) ∗ (F ∗ R) =
          ((cliSessStoreAt A.repAlloc cliIo.rd x.F cliWrOk scopeKit x.peer
              (x.stores + 0xf0#64) g'.sessions ∗
            cliIdStoreAt A.repAlloc cliIo.rd x.F cliWrOk x.peer x.stores g'.identity ∗
            storesOther5At A.repAlloc x.stores StoresGhost.opened) ∗
            apiDecResultAt A.repAlloc x.ret m.1 ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗
            protocolAddressAt A.repAlloc x.me x.meA ∗
            signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit) ∗
              stackAt s0.sp (wsStackV kit ikit)) ∗
            (tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers))) ∗ R := by
        rw [hx3, hx5, hsf_eq, hif_eq, ← hfold.1, ← hfold.2.1,
          apiDecResultAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          signalMessageAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          protocolAddressAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          protocolAddressAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl]
        dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, retagSessionStore,
          retagIdentityStore, RustCliAllocBudget.atState, cliSessionStoreSpecPlaced,
          cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
          y, toDecryptGhost, F]
        exact perm_spat_out
      rw [hperm_out, ← stackAt_split_of_le s0.sp hws_le hstk_sp]
      exact sepConj_mono_left (sepConj_mono hst_repack (sepConj_mono hres_conv
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))))))))
    have hm_out := Satisfies.mono hrepack hspat_out
    dsimp only [decSigSlotSpecPlaced, withLsCodeRoLoaded]
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨m.1, ?_⟩
    have hgoal_post : sf.mem ⊨
        ⌜CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv x evs ∧
          slotTrace s0 sf ∧
          slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' m.1 s0 sf⌝ ∗
        ((storesAt A.repAlloc x.stores g' ∗
          decResAt A.repAlloc x.ret m.1 ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗
          anyHeap) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hev, hslotTrace, hslotOut⟩, hm_out⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ _) ∗ (F ∗ R) at honp
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨_, honp⟩ := honp
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX,
      decSigSlotSpecPlaced, withLsCodeRoLoaded] at honp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨⟨_, answers, hloadRel, _, hpan_or_false⟩, hm_pan⟩ := honp
    rcases hpan_or_false with hpan_m | hfalse
    · have hloadEq := decSessKit_loadRel_eq (img := default) (B := B) hinjK hsub hokPeer hloadRel
      let ca := cliAnswers Scope x.F x.peer.val
        (decKeyAux P Scope x.F x.peer.val x.me.val x.msg x.coins)
      have hpan_ca := (messageDecryptSignal_panic_iff_of_load_eq P.C
        (pqxdhSpqrModel P).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        answers ca x.msg x.peer.val x.me.val
        (coinsOf x.coins) hloadEq).mp hpan_m
      have hpan_out : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none := by
        rw [hS, decDefAux]
        change (match messageDecryptSignal P.C (pqxdhSpqrModel P).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (coinsOf x.coins) with
          | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = none
        rcases hm_ca : messageDecryptSignal P.C (pqxdhSpqrModel P).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (coinsOf x.coins) with ⟨res_ca, calls_ca⟩
        rw [hm_ca] at hpan_ca
        dsimp only at hpan_ca
        rw [hpan_ca]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      rw [← sepConj_assoc] at hm_pan
      exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
    · exact False.elim hfalse
  ·
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    exact False.elim honex.2.1
  ·
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    exact False.elim honoom.2.1

theorem cliDecryptSignal_slot_of_inner_placed [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel} (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux ⟨W.C, W.Q⟩ Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      FilesOkPeer scopeIn F0 peer.val →
      let kit := decSessKitPlaced A.repAlloc F0 peer B
      let ikit := decIdKitPlaced A.repAlloc F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (withStoresDecPlacedSpecVTP W.C A lim 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
            StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv) S stk) :=
  cliDecryptSignal_slot_of_inner_placed_pe ⟨W.C, W.Q⟩ A lim B S Scope tdEnv kitEnv ikitEnv
    hfs hinjK hsub hS hok hvt hivt hInner stk hstk hstk64

def decSigSlotSpecBasePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  { pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.peerA ∧ s.readReg64 .x2 = x.meA ∧
        s.readReg64 .x3 = x.stores + 0xf0#64 ∧ s.readReg64 .x4 = sessVtPlaced ∧
        s.readReg64 .x5 = x.stores ∧ s.readReg64 .x6 = idVtPlaced ∧
        s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        stk ≤ s.sp.toNat ∧ FitsEnv M lim st (DecSigEnv x)⌝ ∗
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced
        A lim st x.toSlotCtx s ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ stackAt s.sp stk
    post := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent, ∃∗ g' : StoresGhost,
        ∃∗ e : Except (ApiError AddrVal Unit) Bytes,
        ⌜DecSigEnv x evs ∧ slotTrace s0 sf ∧
          slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' e s0 sf⌝ ∗
        storesAt A.repAlloc x.stores g' ∗ decResAt A.repAlloc x.ret e ∗
        protocolAddressAt A.repAlloc x.peer x.peerA ∗
        protocolAddressAt A.repAlloc x.me x.meA ∗
        signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ lsLogOff ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp stk ∗ anyHeap
    onPanic := fun (x, _) _ _ =>
      ⌜S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none⌝ ∗ anyHeap }

def decSigSlotSpecPlacedOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk CodeOk
    (decSigSlotSpecBasePlaced A lim DecSigEnv S stk)

abbrev decSigSlotSpecFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecSigEnv : DecSigGhost → List AllocEvent → Prop) (S : RunSem) (stk : Nat) :
    Spec (DecSigGhost × M.σ) :=
  decSigSlotSpecPlacedOf (CryptoVerification.LibsignalFrozen lsmpl) A lim DecSigEnv S stk

set_option maxHeartbeats 1600000 in
/-- `withLsFrozen`-guarded counterpart of `cliDecryptSignal_slot_of_inner_placed_pe`. -/
theorem cliDecryptSignal_slot_of_inner_frozen_placed_pe [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel} (P : PEParams)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux P Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      FilesOkPeer scopeIn F0 peer.val →
      let kit := decSessKitPlaced A.repAlloc F0 peer B
      let ikit := decIdKitPlaced A.repAlloc F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP
            P.C A lim 0#64 uuidTryParse
            (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
            StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv) S stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hal _hcode => ?_
  dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf,
    CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk,
    decSigSlotSpecBasePlaced, slotFramePlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.slotFramePlaced,
    DecSigGhost.toSlotCtx] at hpre
  have hpre_flat : s0.mem ⊨
      ⌜CryptoVerification.LibsignalFrozen lsmpl s0.mem⌝ ∗
      (⌜s0.readReg64 .x0 = x.msgA ∧ s0.readReg64 .x1 = x.peerA ∧ s0.readReg64 .x2 = x.meA ∧
        s0.readReg64 .x3 = x.stores + 0xf0#64 ∧ s0.readReg64 .x4 = sessVtPlaced ∧
        s0.readReg64 .x5 = x.stores ∧ s0.readReg64 .x6 = idVtPlaced ∧
        s0.readReg64 .x8 = x.ret ∧ s0.fs.files = x.F ∧ S.filesOk x.F x.peer.val x.me.val ∧
        stk ≤ s0.sp.toNat ∧
        FitsEnv M lim st (CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv x)⌝ ∗
      (⌜x.coins.length < 2 ^ 63⌝ ∗
      (((storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R)))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hFroz0, hpre_flat⟩ := hpre_flat
  have hfl0 : LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hFroz0.2, hFroz0.1⟩
  rw [satisfies_pure_sepConj] at hpre_flat
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx8, hfiles0, hfok, hstk_sp, hfit⟩, hpre_flat⟩ :=
    hpre_flat
  rw [satisfies_pure_sepConj] at hpre_flat; obtain ⟨hcoins_lt, hspat⟩ := hpre_flat
  obtain ⟨hokPeer, hdist⟩ := hok x.F x.peer.val x.me.val hfok
  have hokIn : FilesOkPeer scopeIn x.F x.peer.val := filesOkPeer_mono hsub hokPeer
  have hsubK : ∀ r, Scope r → scopeKit r := fun r hr => scopeKit_of_scopeIn (hsub r hr)
  have hsess0 := cliSessInv_opened_wrOk hsubK hokPeer
  have hid0 := cliIdInv_opened_wrOk hokPeer
  let kit := decSessKitPlaced A.repAlloc x.F x.peer B
  let ikit := decIdKitPlaced A.repAlloc x.F x.peer B
  let y := toDecryptGhost x
  have hws_le : wsStackV kit ikit ≤ stk :=
    Nat.le_trans (wsStackV_le_cliDecryptSignalNeed_placed A.repAlloc x.F x.peer B) hstk
  have hws_sp : wsStackV kit ikit ≤ s0.sp.toNat := Nat.le_trans hws_le hstk_sp
  let F := storesOther5At A.repAlloc x.stores StoresGhost.opened ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit)
  have hFs0 : FsInv x.F s0.trace s0 := hfiles0 ▸ withFsInv_entry s0
  have hInnerFs := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokIn) x.F s0.trace
  have hvt0 := satisfies_decVtablesAtV_placed
    (kit := kit) (ikit := ikit) (hvt x.F x.peer) (hivt x.F x.peer) hfl0.2 hspat
  have hspat_unpack :
      decVtablesAtV kit ikit ∗
        ((storesAt A.repAlloc x.stores StoresGhost.opened ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          tokenInitPlacedAt ∗ lsLogOff ∗ A.pool lim st s0 ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R) ⊢
      (tokenInitPlacedAt ∗
        (kit.storeAt (s0.readReg64 .x3) StoresGhost.opened.sessions ∗
          ikit.identityAt (s0.readReg64 .x5) StoresGhost.opened.identity ∗
          signalMessageAt (A.atState lim st s0) y.msgG y.msgA y.msg ∗
          protocolAddressAt (A.atState lim st s0) y.rem y.remA ∗
          protocolAddressAt (A.atState lim st s0) y.loc y.locA ∗
          memRegion y.ret 48 ∗
          cliTapeAt 0#64 y.cur y.rest ∗
          lsLogOff ∗ decVtablesAtV kit ikit ∗
          stackAt s0.sp (wsStackV kit ikit) ∗ A.pool lim st s0)) ∗ (F ∗ R) := by
    rw [stackAt_split_of_le s0.sp hws_le hstk_sp, hx3, hx5,
      signalMessageAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl,
      protocolAddressAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl,
      protocolAddressAt_of_live_eq (A₁ := A.atState lim st s0) (A₂ := A.repAlloc) rfl]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono_left
          (sepConj_mono
            (storesAt_unpack_dec A.repAlloc x.stores StoresGhost.opened x.F scopeKit x.peer hsess0 hid0)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left
                (Entails.of_eq (coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoins_lt).symm)))))))
      ?_
    dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, cliSessionStoreSpecPlaced,
      cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec, y, toDecryptGhost, F]
    exact Entails.of_eq perm_spat_in
  have hspat_in := Satisfies.mono hspat_unpack hvt0
  have hpre_vt :
      s0.mem ⊨
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP
          P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv x.F x.peer) ikit (ikitEnv x.F x.peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit).pre
          (y, st) s0 ∗ (F ∗ R) := by
    dsimp only [LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX, withStoresDecPlacedSpecV,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV,
      withLsCodeRoLoaded]
    have hgoal : s0.mem ⊨
        ⌜CryptoVerification.LibsignalFrozen lsmpl s0.mem⌝ ∗
        (⌜DistinctSid uuidTryParse y.loc.name.bytes y.rem.name.bytes⌝ ∗
        (⌜FitsEnv M lim st
            (WithStoresDecEnv kit (kitEnv x.F x.peer) StoresGhost.opened.sessions
              ikit (ikitEnv x.F x.peer) StoresGhost.opened.identity
              P.C (pqxdhSpqrModel P) uuidTryParse tdEnv scopeKit y)⌝ ∗
        (⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = y.msgA ∧ s0.readReg64 .x1 = y.remA ∧ s0.readReg64 .x2 = y.locA ∧
          s0.readReg64 .x4 = (retagSessionStore (A' := A.atState lim st s0) kit).ss_vt ∧
          s0.readReg64 .x6 = (retagIdentityStore (A' := A.atState lim st s0) ikit).id_vt ∧
          s0.readReg64 .x8 = y.ret ∧
          wsStackV (retagSessionStore (A' := A.atState lim st s0) kit)
            (retagIdentityStore (A' := A.atState lim st s0) ikit) ≤ s0.sp.toNat ∧
          (retagSessionStore (A' := A.atState lim st s0) kit).addrOk y.rem.val ∧
          (retagIdentityStore (A' := A.atState lim st s0) ikit).addrOk y.rem.val⌝ ∗
        ((tokenInitPlacedAt ∗
          ((retagSessionStore (A' := A.atState lim st s0) kit).storeAt (s0.readReg64 .x3)
              StoresGhost.opened.sessions ∗
            (retagIdentityStore (A' := A.atState lim st s0) ikit).identityAt (s0.readReg64 .x5)
              StoresGhost.opened.identity ∗
            signalMessageAt (A.atState lim st s0) y.msgG y.msgA y.msg ∗
            protocolAddressAt (A.atState lim st s0) y.rem y.remA ∗
            protocolAddressAt (A.atState lim st s0) y.loc y.locA ∗
            memRegion y.ret 48 ∗
            cliTapeAt 0#64 y.cur y.rest ∗
            lsLogOff ∗
            decVtablesAtV (retagSessionStore (A' := A.atState lim st s0) kit)
              (retagIdentityStore (A' := A.atState lim st s0) ikit) ∗
            stackAt s0.sp (wsStackV (retagSessionStore (A' := A.atState lim st s0) kit)
              (retagIdentityStore (A' := A.atState lim st s0) ikit)) ∗
            (A.atState lim st s0).pool)) ∗ (F ∗ R)))))) := by
      rw [satisfies_pure_sepConj]; refine ⟨hFroz0, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hdist, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfit, ?_⟩
      rw [satisfies_pure_sepConj]; refine ⟨hfl0, ?_⟩
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hws_sp, rfl, rfl⟩, hspat_in⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hgoal
  have hpre_inner :
      s0.mem ⊨
        (withFsInv
          (withEnvPre
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP P.C A lim 0#64 uuidTryParse
              (pqxdhSpqrModel P) tdEnv encodeRecord kit (kitEnv x.F x.peer)
              ikit (ikitEnv x.F x.peer)
              StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
            fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)
          x.F s0.trace).pre (y, st) s0 ∗ (F ∗ R) :=
    withFsInv_pre_intro hFs0 (withEnvPre_pre_intro ⟨hfiles0, hfiles0⟩ hpre_vt)
  refine hInnerFs.mono_outcome (y, st) (F ∗ R) s0 hpc hrun hpre_inner hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, honp⟩ | ⟨_code, _hex, honex⟩ | ⟨_hoom, honoom⟩
  ·
    refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hFsSf, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX,
      withStoresDecPlacedSpecV,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecV,
      withLsCodeRoLoaded] at hpost
    obtain ⟨evs, hev, hpost1⟩ := unpack_inner_post hpost
    obtain ⟨answers, ⟨hnpan, _, hcalls_r, hidCalls_r, htr⟩, hspat_out⟩ := unpack_inner_post hpost1
    have htr_nil := retag_decIdKitPlaced_traceOfWith_nil A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B encodeRecord answers
      (y.model P.C (pqxdhSpqrModel P) uuidTryParse answers).2
    rw [htr_nil, List.append_nil] at htr
    have hfiles_sf : sf.fs.files = x.F :=
      files_eq_at_callback hFsSf (evs := []) (by simp [htr]) (by simp [NoFsEv])
    have hslotTrace : slotTrace s0 sf :=
      ⟨by simp [htr], hfiles_sf.trans hfiles0.symm, by simp [htr]⟩
    have hcalls0 := (retag_decSessKitPlaced_callsRel_iff A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.sessions answers _).mp hcalls_r
    have hidCalls0 := (retag_decIdKitPlaced_idCallsRel_iff A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.identity answers _).mp hidCalls_r
    obtain ⟨hmod_eq, hnst, hwrOk⟩ := decModel_det (img := default) (dummyCliHooks P) B Scope x.F
      y answers rfl hinjK hsub hokPeer hcalls0 hidCalls0
    let m := y.model P.C (pqxdhSpqrModel P) uuidTryParse answers
    let g' := cliFinal x.F m.2
    have hfold := cliStep_foldl_eq default x.F x.peer B answers m.2 StoresGhost.opened
    have hsf_eq := retag_decSessKitPlaced_storeFinal_eq A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.sessions answers m.2
    have hif_eq := retag_decIdKitPlaced_idFinal_eq A.repAlloc
      (A.atState lim (M.stepEvents evs st) sf) x.F x.peer B
      StoresGhost.opened.identity answers m.2
    have hans_eq : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins =
        match m.1 with
        | .ok pt => some (some (g', pt))
        | .error .panic => none
        | .error _ => some none := by
      rw [hS]
      have hd := decDefAux_eq_model P Scope x.F y
      dsimp only [y, toDecryptGhost, dummyCliHooks] at hd hmod_eq
      rw [hd, ← hmod_eq]
      change (match m with
        | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
        | (.error .panic, _) => none
        | (.error _, _) => some none) = _
      dsimp only [g']
      rcases m with ⟨res, calls⟩
      cases res with
      | ok pt => rfl
      | error err => cases err <;> rfl
    have hslotOut : slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' m.1 s0 sf := by
      refine ⟨hnpan, hnst, ?_⟩
      rw [hans_eq]
      cases hm1 : m.1 with
      | ok pt => exact ⟨rfl, hwrOk pt hm1⟩
      | error err =>
        cases err with
        | panic => exact absurd hm1 hnpan
        | store u => cases u; exact absurd hm1 hnst
        | protocol _ => rfl
        | sessionNotFound _ _ => rfl
        | untrustedIdentity _ => rfl
    have hrepack :
        (tokenInitPlacedAt ∗
          ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeAt
              (s0.readReg64 .x3)
              ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeFinal
                StoresGhost.opened.sessions answers m.2) ∗
            (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).identityAt
              (s0.readReg64 .x5)
              ((retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).idFinal
                StoresGhost.opened.identity answers m.2) ∗
            apiDecResultAt (A.atState lim (M.stepEvents evs st) sf) y.ret m.1 ∗
            signalMessageAt (A.atState lim (M.stepEvents evs st) sf) y.msgG y.msgA y.msg ∗
            protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.rem y.remA ∗
            protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.loc y.locA ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers) ∗
            lsLogOff ∗
            decVtablesAtV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
              (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit) ∗
            stackAt s0.sp
              (wsStackV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit)) ∗
            (A.atState lim (M.stepEvents evs st) sf).pool)) ∗ (F ∗ R) ⊢
        (storesAt A.repAlloc x.stores g' ∗
          decResAt A.repAlloc x.ret m.1 ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗
          anyHeap) ∗ R := by
      have hst_repack := storesAt_repack_dec A.repAlloc x.stores StoresGhost.opened g'
        x.F scopeKit x.peer hfold.2.2.1 (congrArg KyberGhost.oneTime hfold.2.2.2.1)
        (congrArg KyberGhost.lastResort hfold.2.2.2.1) hfold.2.2.2.2.1 hfold.2.2.2.2.2
      have hres_conv := apiDecResultAt_entails_decResAt A.repAlloc x.ret m.1 hnst
      have hperm_out :
          (tokenInitPlacedAt ∗
            ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeAt
                (s0.readReg64 .x3)
                ((retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit).storeFinal
                  StoresGhost.opened.sessions answers m.2) ∗
              (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).identityAt
                (s0.readReg64 .x5)
                ((retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit).idFinal
                  StoresGhost.opened.identity answers m.2) ∗
              apiDecResultAt (A.atState lim (M.stepEvents evs st) sf) y.ret m.1 ∗
              signalMessageAt (A.atState lim (M.stepEvents evs st) sf) y.msgG y.msgA y.msg ∗
              protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.rem y.remA ∗
              protocolAddressAt (A.atState lim (M.stepEvents evs st) sf) y.loc y.locA ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers) ∗
              lsLogOff ∗
              decVtablesAtV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit) ∗
              stackAt s0.sp
                (wsStackV (retagSessionStore (A' := A.atState lim (M.stepEvents evs st) sf) kit)
                  (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sf) ikit)) ∗
              (A.atState lim (M.stepEvents evs st) sf).pool)) ∗ (F ∗ R) =
          ((cliSessStoreAt A.repAlloc cliIo.rd x.F cliWrOk scopeKit x.peer
              (x.stores + 0xf0#64) g'.sessions ∗
            cliIdStoreAt A.repAlloc cliIo.rd x.F cliWrOk x.peer x.stores g'.identity ∗
            storesOther5At A.repAlloc x.stores StoresGhost.opened) ∗
            apiDecResultAt A.repAlloc x.ret m.1 ∗
            protocolAddressAt A.repAlloc x.peer x.peerA ∗
            protocolAddressAt A.repAlloc x.me x.meA ∗
            signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit) ∗
              stackAt s0.sp (wsStackV kit ikit)) ∗
            (tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws P.C answers))) ∗ R := by
        rw [hx3, hx5, hsf_eq, hif_eq, ← hfold.1, ← hfold.2.1,
          apiDecResultAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          signalMessageAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          protocolAddressAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl,
          protocolAddressAt_of_live_eq (A₁ := A.atState lim (M.stepEvents evs st) sf) (A₂ := A.repAlloc) rfl]
        dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, retagSessionStore,
          retagIdentityStore, RustCliAllocBudget.atState, cliSessionStoreSpecPlaced,
          cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
          y, toDecryptGhost, F]
        exact perm_spat_out
      rw [hperm_out, ← stackAt_split_of_le s0.sp hws_le hstk_sp]
      exact sepConj_mono_left (sepConj_mono hst_repack (sepConj_mono hres_conv
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _)))))))))
    have hm_out := Satisfies.mono hrepack hspat_out
    dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf,
      CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk, decSigSlotSpecBasePlaced]
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨evs, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨g', ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨m.1, ?_⟩
    have hgoal_post : sf.mem ⊨
        ⌜CliDecryptSignalSlotEnv P A B tdEnv kitEnv ikitEnv x evs ∧
          slotTrace s0 sf ∧
          slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g' m.1 s0 sf⌝ ∗
        ((storesAt A.repAlloc x.stores g' ∗
          decResAt A.repAlloc x.ret m.1 ∗
          protocolAddressAt A.repAlloc x.peer x.peerA ∗
          protocolAddressAt A.repAlloc x.me x.meA ∗
          signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
          lsLogOff ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk ∗
          anyHeap) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hev, hslotTrace, hslotOut⟩, hm_out⟩
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal_post
  ·
    refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ _) ∗ (F ∗ R) at honp
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨_, honp⟩ := honp
    dsimp only [withEnvPre,
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP,
      CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withStoresDecPlacedSpecVTP, withStoresDecPlacedSpecVX,
      decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf,
      CryptoVerification.SignalSession.Cli.RunCompose.withCodeOk, decSigSlotSpecBasePlaced] at honp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨⟨_, answers, hloadRel, _, hpan_or_false⟩, hm_pan⟩ := honp
    rcases hpan_or_false with hpan_m | hfalse
    · have hloadEq := decSessKit_loadRel_eq (img := default) (B := B) hinjK hsub hokPeer hloadRel
      let ca := cliAnswers Scope x.F x.peer.val
        (decKeyAux P Scope x.F x.peer.val x.me.val x.msg x.coins)
      have hpan_ca := (messageDecryptSignal_panic_iff_of_load_eq P.C
        (pqxdhSpqrModel P).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        answers ca x.msg x.peer.val x.me.val
        (coinsOf x.coins) hloadEq).mp hpan_m
      have hpan_out : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins = none := by
        rw [hS, decDefAux]
        change (match messageDecryptSignal P.C (pqxdhSpqrModel P).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (coinsOf x.coins) with
          | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = none
        rcases hm_ca : messageDecryptSignal P.C (pqxdhSpqrModel P).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (coinsOf x.coins) with ⟨res_ca, calls_ca⟩
        rw [hm_ca] at hpan_ca
        dsimp only at hpan_ca
        rw [hpan_ca]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      rw [← sepConj_assoc] at hm_pan
      exact ⟨hpan_out, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_pan⟩
    · exact False.elim hfalse
  ·
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    exact False.elim honex.2.1
  ·
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    exact False.elim honoom.2.1

theorem cliDecryptSignal_slot_of_inner_frozen_placed [LibsignalPlacement] {callerProg : Program}
    {M : AllocCostModel} (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B))
    (hfs : TraceFsSound callerProg)
    (hinjK : EncodeInjOn scopeKit)
    (hsub : ∀ r, Scope r → scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux ⟨W.C, W.Q⟩ Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      FilesOkPeer Scope F peer ∧ DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced A.repAlloc F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced A.repAlloc F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      FilesOkPeer scopeIn F0 peer.val →
      let kit := decSessKitPlaced A.repAlloc F0 peer B
      let ikit := decIdKitPlaced A.repAlloc F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget.withStoresDecFrozenPlacedSpecVTP
            W.C A lim 0#64 uuidTryParse
            (pqxdhSpqrModel ⟨W.C, W.Q⟩) tdEnv encodeRecord kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
            StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux B ≤ stk) (hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecFrozenPlaced A lim
        (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B tdEnv kitEnv ikitEnv) S stk) :=
  cliDecryptSignal_slot_of_inner_frozen_placed_pe ⟨W.C, W.Q⟩ A lim B S Scope tdEnv kitEnv ikitEnv
    hfs hinjK hsub hS hok hvt hivt hInner stk hstk hstk64

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
