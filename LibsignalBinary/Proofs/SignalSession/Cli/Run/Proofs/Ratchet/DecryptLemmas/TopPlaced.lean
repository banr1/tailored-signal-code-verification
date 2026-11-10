/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.ModelDetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.EntryExit
public import LibsignalBinary.Proofs.SignalSession.Cli.Fs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stack

/-!
# Relocatable Outer Slot Reduction for `decrypt_signal`

Reduces `decSigSlotSpecPlaced` and `decSigSlotSpecFrozenPlaced` at `lsmpl.base 463`
(`signal_session_ratchet::decrypt_signal`) to `hInner` on `callerProg` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification

theorem wsStackV_le_cliDecryptSignalNeed_placed [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    wsStackV (decSessKitPlaced F0 peer B) (decIdKitPlaced F0 peer B) ≤ decNeedAux_placed B := by
  have hk1 : (decSessKitPlaced F0 peer B).loadShimStack = SessKit.loadShimNeed := rfl
  have hk2 : (decSessKitPlaced F0 peer B).loadPollStack = SessKit.loadPollNeed B.readFile := rfl
  have hk3 : (decSessKitPlaced F0 peer B).storeShimStack = SessKit.storeShimNeed := rfl
  have hk4 : (decSessKitPlaced F0 peer B).storePollStack = SessKit.storePollNeedX := rfl
  have hi1 : (decIdKitPlaced F0 peer B).trustShimStack = IdKit.trustShimNeed := rfl
  have hi2 : (decIdKitPlaced F0 peer B).trustPollStack = IdKit.trustPollNeed B.readFile := rfl
  have hi3 : (decIdKitPlaced F0 peer B).saveShimStack = IdKit.saveShimNeed := rfl
  have hi4 : (decIdKitPlaced F0 peer B).savePollStack = IdKit.savePollNeed B.readFile := rfl
  have h1 : CryptoVerification.LibsignalTripleRatchet.doReserveStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.doReserveStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h2 : CryptoVerification.LibsignalTripleRatchet.finishGrowStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.finishGrowStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h3 : CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h4 : Proofs.libsignal.Hooks2.serializeStackX ≤ 262144 := by
    norm_num [Proofs.libsignal.Hooks2.serializeStackX,
      CryptoVerification.LibsignalTripleRatchet.doReserveStackX,
      CryptoVerification.LibsignalTripleRatchet.finishGrowStackX,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h5 : E2E.Record.recDeserializeStack ≤ 262144 := by
    norm_num [E2E.Record.recDeserializeStack,
      CryptoVerification.LibsignalTripleRatchet.smallRootStack,
      CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have h6 : extHookStack ≤ 65536 := by
    norm_num [CryptoVerification.LibsignalTripleRatchet.extHookStack]
  have hpath : RunSkeleton.pathNeed ≤ 66000 := by
    dsimp only [RunSkeleton.pathNeed]
    have hm : max doReserveStackX extHookStack ≤ 65536 := Nat.max_le.mpr ⟨h1, h6⟩
    omega
  have hdget : RunBudgets.dirGetNeed ⟨B.readFile⟩ ≤ 66200 + B.readFile := by
    dsimp only [RunBudgets.dirGetNeed]
    have hm1 : max RunSkeleton.pathNeed B.readFile ≤ 66000 + B.readFile :=
      Nat.max_le.mpr ⟨Nat.le_trans hpath (Nat.le_add_right _ _), Nat.le_add_left _ _⟩
    have hm2 : max (max RunSkeleton.pathNeed B.readFile) extHookStack ≤ 66000 + B.readFile :=
      Nat.max_le.mpr ⟨hm1, Nat.le_trans h6 (by omega)⟩
    omega
  have hdec : SessKit.decNeed ≤ 67000 := by dsimp only [SessKit.decNeed]; omega
  have haddr : SessKit.addrTextNeed ≤ 68000 := by
    dsimp only [SessKit.addrTextNeed]
    have hm : max (max doReserveStackX extHookStack) SessKit.decNeed ≤ 67000 :=
      Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨by omega, by omega⟩, hdec⟩
    omega
  have hgrowS : SessKit.growOneDirNeed ≤ 66000 := by dsimp only [SessKit.growOneDirNeed]; omega
  have hdput : SessKit.dirPutNeed ≤ 67000 := by
    dsimp only [SessKit.dirPutNeed]
    have hm : max SessKit.growOneDirNeed extHookStack ≤ 66000 := Nat.max_le.mpr ⟨hgrowS, by omega⟩
    omega
  have hgrowI : IdKit.growOneDirNeed ≤ 66000 := by dsimp only [IdKit.growOneDirNeed]; omega
  have hdputS : IdKit.dirPutStrNeed ≤ 67000 := by
    dsimp only [IdKit.dirPutStrNeed]
    have hm : max IdKit.growOneDirNeed extHookStack ≤ 66000 := Nat.max_le.mpr ⟨hgrowI, by omega⟩
    omega
  have hls : SessKit.loadShimNeed ≤ 1000000 + B.readFile := by dsimp only [SessKit.loadShimNeed]; omega
  have hlp : SessKit.loadPollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.loadPollNeed]
    have hm1 : max SessKit.addrTextNeed (RunBudgets.dirGetNeed ⟨B.readFile⟩) ≤ 68000 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have hm2 : max E2E.Record.recDeserializeStack extHookStack ≤ 262144 := Nat.max_le.mpr ⟨h5, by omega⟩
    have hm3 : max (max SessKit.addrTextNeed (RunBudgets.dirGetNeed ⟨B.readFile⟩))
        (max E2E.Record.recDeserializeStack extHookStack) ≤ 262144 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  have hss : SessKit.storeShimNeed ≤ 1000000 + B.readFile := by dsimp only [SessKit.storeShimNeed]; omega
  have hsp : SessKit.storePollNeedX ≤ 1000000 + B.readFile := by
    dsimp only [SessKit.storePollNeedX]
    have hm1 : max SessKit.addrTextNeed Proofs.libsignal.Hooks2.serializeStackX ≤ 262144 :=
      Nat.max_le.mpr ⟨by omega, h4⟩
    have hm2 : max SessKit.dirPutNeed extHookStack ≤ 67000 := Nat.max_le.mpr ⟨hdput, by omega⟩
    have hm3 : max (max SessKit.addrTextNeed Proofs.libsignal.Hooks2.serializeStackX)
        (max SessKit.dirPutNeed extHookStack) ≤ 262144 := Nat.max_le.mpr ⟨hm1, by omega⟩
    omega
  have hts : IdKit.trustShimNeed ≤ 1000000 + B.readFile := by dsimp only [IdKit.trustShimNeed]; omega
  have htp : IdKit.trustPollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.trustPollNeed]
    have hm1 : max (RunBudgets.dirGetNeed ⟨B.readFile⟩) 0x60 ≤ 66200 + B.readFile :=
      Nat.max_le.mpr ⟨hdget, by omega⟩
    have hm2 : max 64 extHookStack ≤ 65536 := Nat.max_le.mpr ⟨by omega, h6⟩
    have hm3 : max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) 0x60) (max 64 extHookStack) ≤
        66200 + B.readFile := Nat.max_le.mpr ⟨hm1, by omega⟩
    omega
  have his : IdKit.saveShimNeed ≤ 1000000 + B.readFile := by dsimp only [IdKit.saveShimNeed]; omega
  have hip : IdKit.savePollNeed B.readFile ≤ 1000000 + B.readFile := by
    dsimp only [IdKit.savePollNeed]
    have hm1 : max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed ≤ 67000 + B.readFile :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    have hm2 : max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed) (max 0x60 64) ≤
        67000 + B.readFile := Nat.max_le.mpr ⟨hm1, by omega⟩
    have hm3 : max publicKeySerializeStackX extHookStack ≤ 65536 := Nat.max_le.mpr ⟨h3, h6⟩
    have hm4 : max (max (max (RunBudgets.dirGetNeed ⟨B.readFile⟩) IdKit.dirPutStrNeed) (max 0x60 64))
        (max publicKeySerializeStackX extHookStack) ≤ 67000 + B.readFile :=
      Nat.max_le.mpr ⟨hm2, by omega⟩
    omega
  have hwsc : wsCalleeStack ≤ 1000000 + B.readFile := by
    have he : wsCalleeStack ≤ 524288 := by norm_num [wsCalleeStack, wsStack, wsFrame, entryStack]
    omega
  unfold wsStackV wsCalleeStackV decNeedAux_placed
  rw [hk1, hk2, hk3, hk4, hi1, hi2, hi3, hi4]
  have hmax : max wsCalleeStack
      (max (max (max SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile))
                (max SessKit.storeShimNeed SessKit.storePollNeedX))
           (max (max IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile))
                (max IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)))) ≤ 1000000 + B.readFile :=
    Nat.max_le.mpr ⟨hwsc, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hls, hlp⟩,
      Nat.max_le.mpr ⟨hss, hsp⟩⟩, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hts, htp⟩,
      Nat.max_le.mpr ⟨his, hip⟩⟩⟩⟩
  have hwf : wsFrame = 0xee0 := rfl
  rw [hwf]; omega

def toDecryptGhost_placed (x : DecSigGhost) : DecryptGhost where
  msgG := x.msgG
  msgA := x.msgA
  msg := x.msg
  rem := x.peer
  remA := x.peerA
  loc := x.me
  locA := x.meA
  ret := x.ret
  cur := x.coinsP
  rest := x.coins

private theorem unpack_slot_pre {fl p1 p2 : Prop}
    {s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 R : SepProp} {m : Memory}
    (hm : m ⊨ ((⌜p1⌝ ∗ (⌜p2⌝ ∗ s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ s7) ∗ s8 ∗ s9 ∗ s10) ∗ ⌜fl⌝) ∗ R) :
    fl ∧ p1 ∧ p2 ∧ (m ⊨ (s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ s7 ∗ s8 ∗ s9 ∗ s10) ∗ R) := by
  have hperm :
      ((⌜p1⌝ ∗ (⌜p2⌝ ∗ s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ s7) ∗ s8 ∗ s9 ∗ s10) ∗ ⌜fl⌝) ∗ R =
      ⌜fl⌝ ∗ (⌜p1⌝ ∗ (⌜p2⌝ ∗ ((s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ s7 ∗ s8 ∗ s9 ∗ s10) ∗ R))) := by
    ac_rfl
  rw [hperm, satisfies_pure_sepConj] at hm
  obtain ⟨hfl, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  obtain ⟨hp1, hm⟩ := hm
  rw [satisfies_pure_sepConj] at hm
  exact ⟨hfl, hp1, hm⟩

private theorem pack_inner_pre {dist fl p_in : Prop} {tok body FR : SepProp} {m : Memory}
    (hdist : dist) (hfl : fl) (hp : p_in)
    (hm : m ⊨ (tok ∗ body) ∗ FR) :
    m ⊨ (⌜dist⌝ ∗ tok ∗ ((⌜p_in⌝ ∗ body) ∗ ⌜fl⌝)) ∗ FR := by
  have hperm :
      (⌜dist⌝ ∗ tok ∗ ((⌜p_in⌝ ∗ body) ∗ ⌜fl⌝)) ∗ FR =
      ⌜dist⌝ ∗ (⌜fl⌝ ∗ (⌜p_in⌝ ∗ ((tok ∗ body) ∗ FR))) := by
    ac_rfl
  rw [hperm, satisfies_pure_sepConj]
  refine ⟨hdist, ?_⟩
  rw [satisfies_pure_sepConj]
  refine ⟨hfl, ?_⟩
  rw [satisfies_pure_sepConj]
  exact ⟨hp, hm⟩

private theorem unpack_inner_post {α : Type} {p : α → Prop} {body : α → SepProp}
    {tok FR : SepProp} {m : Memory}
    (hm : m ⊨ (tok ∗ (∃∗ a : α, ⌜p a⌝ ∗ body a)) ∗ FR) :
    ∃ a, p a ∧ (m ⊨ (tok ∗ body a) ∗ FR) := by
  have hperm1 :
      (tok ∗ (∃∗ a : α, ⌜p a⌝ ∗ body a)) ∗ FR =
      (∃∗ a : α, ⌜p a⌝ ∗ body a) ∗ (tok ∗ FR) := by
    ac_rfl
  rw [hperm1, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hm⟩ := hm
  have hperm2 : (⌜p a⌝ ∗ body a) ∗ (tok ∗ FR) = ⌜p a⌝ ∗ ((tok ∗ body a) ∗ FR) := by
    ac_rfl
  rw [hperm2, satisfies_pure_sepConj] at hm
  exact ⟨a, hm.1, hm.2⟩

private theorem pack_slot_post {γ ε : Type} {pq : γ → ε → Prop}
    {stores : γ → SepProp} {res : ε → SepProp}
    {pa1 pa2 msg log pool stk dump R : SepProp} {m : Memory}
    (g' : γ) (e : ε) (hpq : pq g' e)
    (hm : m ⊨ (stores g' ∗ res e ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ stk ∗ dump) ∗ R) :
    m ⊨ (∃∗ g : γ, ∃∗ e' : ε,
      ⌜pq g e'⌝ ∗ stores g ∗ res e' ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ stk ∗ anyHeap) ∗ R := by
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨g', ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨e, ?_⟩
  have hperm2 :
      (⌜pq g' e⌝ ∗ stores g' ∗ res e ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ stk ∗ anyHeap) ∗ R =
      ⌜pq g' e⌝ ∗ ((stores g' ∗ res e ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ stk ∗ anyHeap) ∗ R) := by
    ac_rfl
  rw [hperm2, satisfies_pure_sepConj]
  refine ⟨hpq, Satisfies.mono (sepConj_mono_left ?_) hm⟩
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_anyHeap dump))))))))

private theorem perm_spat_in
    {vt sess id other5 pa1 pa2 coins tok log pool msg ret stkRem stkWs R : SepProp} :
    vt ∗ (((sess ∗ id ∗ other5) ∗ pa1 ∗ pa2 ∗ coins ∗ tok ∗ log ∗ pool ∗ msg ∗ ret ∗
      (stkRem ∗ stkWs)) ∗ R) =
    (tok ∗ (sess ∗ id ∗ msg ∗ pa1 ∗ pa2 ∗ ret ∗ coins ∗ log ∗ vt ∗ stkWs ∗ pool)) ∗
      ((other5 ∗ stkRem) ∗ R) := by
  ac_rfl

private theorem perm_spat_out
    {tok sess id res msg pa1 pa2 coins log vt stkWs pool other5 stkRem R : SepProp} :
    (tok ∗ (sess ∗ id ∗ res ∗ msg ∗ pa1 ∗ pa2 ∗ coins ∗ log ∗ vt ∗ stkWs ∗ pool)) ∗
      ((other5 ∗ stkRem) ∗ R) =
    ((sess ∗ id ∗ other5) ∗ res ∗ pa1 ∗ pa2 ∗ msg ∗ log ∗ pool ∗ (stkRem ∗ stkWs) ∗
      (tok ∗ vt ∗ coins)) ∗ R := by
  ac_rfl

set_option maxHeartbeats 1600000 in
/-- Reduces `decSigSlotSpecPlaced` at `lsmpl.base 463` on `callerProg` to the placed inner store-kit contract. -/
theorem cliDecryptSignal_slot_of_inner_placed [LibsignalPlacement] {callerProg : Program}
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hfs : TraceFsSound callerProg)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux_placed ⟨W.C, W.Q⟩ Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
      let kit := decSessKitPlaced F0 peer B
      let ikit := decIdKitPlaced F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (withStoresDecPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
            (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
            StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux_placed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecPlaced E2E.HooksE.A0 S stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _hcode => ?_
  dsimp only [decSigSlotSpecPlaced, decSigSlotSpecPlacedOf, withCodeOk, slotFramePlaced,
    StoreKit.withLsCodeRoLoaded] at hpre
  obtain ⟨hfl0, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx8, hfiles0, hfok, hstk_sp⟩,
    hcoins_lt, hspat⟩ := unpack_slot_pre hpre
  obtain ⟨hokPeer, hdist⟩ := hok x.F x.peer.val x.me.val hfok
  have hokIn : Slots.FilesOkPeer Slots.scopeIn x.F x.peer.val := filesOkPeer_mono_placed hsub hokPeer
  have hsubK : ∀ r, Scope r → Slots.scopeKit r := fun r hr => Slots.scopeKit_of_scopeIn (hsub r hr)
  have hsess0 := cliSessInv_opened_wrOk_placed hsubK hokPeer
  have hid0 := cliIdInv_opened_wrOk_placed hokPeer
  let kit := decSessKitPlaced x.F x.peer B
  let ikit := decIdKitPlaced x.F x.peer B
  let y := toDecryptGhost_placed x
  have hws_le : wsStackV kit ikit ≤ stk :=
    Nat.le_trans (wsStackV_le_cliDecryptSignalNeed_placed x.F x.peer B) hstk
  have hws_sp : wsStackV kit ikit ≤ s0.sp.toNat := Nat.le_trans hws_le hstk_sp
  let F := storesOther5At E2E.HooksE.A0 x.stores StoresGhost.opened ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit)
  have hFs0 : FsInv x.F s0.trace s0 := hfiles0 ▸ withFsInv_entry s0
  have hInnerFs := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokIn) x.F s0.trace
  have hvt0 := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.satisfies_decVtablesAtV_placed
    (kit := kit) (ikit := ikit) (hvt x.F x.peer) (hivt x.F x.peer) hfl0.2 hspat
  have hspat_unpack :
      decVtablesAtV kit ikit ∗
        ((storesAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R) ⊢
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (kit.storeAt (s0.readReg64 .x3) StoresGhost.opened.sessions ∗
          ikit.identityAt (s0.readReg64 .x5) StoresGhost.opened.identity ∗
          signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
          protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
          protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
          memRegion y.ret 48 ∗
          cliTapeAt 0#64 y.cur y.rest ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
          stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) := by
    rw [Slots.stackAt_split_of_le s0.sp hws_le hstk_sp, hx3, hx5]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono_left
          (sepConj_mono
            (storesAt_unpack_dec E2E.HooksE.A0 x.stores StoresGhost.opened x.F Slots.scopeKit x.peer hsess0 hid0)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (Entails.of_eq (Slots.coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoins_lt).symm)))))))
      ?_
    dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, EncryptLemmas.w1SessKitPlaced,
      EncryptLemmas.w1IdKitPlaced, EncryptLemmas.cliSessionStoreSpecPlaced,
      EncryptLemmas.cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
      y, toDecryptGhost_placed, F]
    exact Entails.of_eq perm_spat_in
  have hspat_in := Satisfies.mono hspat_unpack hvt0
  have hpre_inner :
      s0.mem ⊨
        (withFsInv
          (withEnvPre
            (withStoresDecPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
              (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
              StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
            fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)
          x.F s0.trace).pre y s0 ∗ (F ∗ R) := by
    apply withFsInv_pre_intro hFs0
    apply withEnvPre_pre_intro ⟨hfiles0, hfiles0⟩
    dsimp only [withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded]
    exact pack_inner_pre hdist hfl0 ⟨hx0, hx1, hx2, hx4, hx6, hx8, hws_sp, rfl, rfl⟩ hspat_in
  refine hInnerFs.mono_outcome y (F ∗ R) s0 hpc hrun hpre_inner hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, _hex, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hFsSf, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded] at hpost
    obtain ⟨answers, ⟨hnpan, _, hcalls, hidCalls, htr⟩, hspat_out⟩ := unpack_inner_post hpost
    have htr_nil := decIdKitPlaced_traceOfWith_nil x.F x.peer B E2E.Record.encodeRecord answers
      (y.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2
    rw [htr_nil, List.append_nil] at htr
    have hfiles_sf : sf.fs.files = x.F :=
      files_eq_at_callback hFsSf (evs := []) (by simp [htr]) (by simp [NoFsEv])
    have hslotTrace : slotTrace s0 sf :=
      ⟨by simp [htr], hfiles_sf.trans hfiles0.symm, by simp [htr]⟩
    obtain ⟨hmod_eq, hnst, hwrOk⟩ := decModel_det_placed W B Scope x.F y answers rfl hinjK hsub hokPeer
      hcalls hidCalls
    let m := y.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers
    let g' := cliFinal x.F m.2
    have hfold := cliStep_foldl_placed_eq x.F x.peer B answers m.2 StoresGhost.opened
    have hans_eq : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins =
        match m.1 with
        | .ok pt => some (some (g', pt))
        | .error .panic => none
        | .error _ => some none := by
      rw [hS]
      have hd := decDefAux_eq_model_placed ⟨W.C, W.Q⟩ Scope x.F y
      dsimp only [y, toDecryptGhost_placed] at hd hmod_eq
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
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          (kit.storeAt (s0.readReg64 .x3) (kit.storeFinal StoresGhost.opened.sessions answers m.2) ∗
            ikit.identityAt (s0.readReg64 .x5) (ikit.idFinal StoresGhost.opened.identity answers m.2) ∗
            apiDecResultAt E2E.HooksE.A0 y.ret m.1 ∗
            signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
            protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
            protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers) ∗
            FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
            stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) ⊢
        (storesAt E2E.HooksE.A0 x.stores g' ∗
          decResAt E2E.HooksE.A0 x.ret m.1 ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
          FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ stackAt s0.sp stk ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers))) ∗ R := by
      have hst_repack := storesAt_repack_dec E2E.HooksE.A0 x.stores StoresGhost.opened g'
        x.F Slots.scopeKit x.peer hfold.2.2.1 (congrArg KyberGhost.oneTime hfold.2.2.2.1)
        (congrArg KyberGhost.lastResort hfold.2.2.2.1) hfold.2.2.2.2.1 hfold.2.2.2.2.2
      have hres_conv := apiDecResultAt_entails_decResAt E2E.HooksE.A0 x.ret m.1 hnst
      have hperm_out :
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            (kit.storeAt (s0.readReg64 .x3) (kit.storeFinal StoresGhost.opened.sessions answers m.2) ∗
              ikit.identityAt (s0.readReg64 .x5) (ikit.idFinal StoresGhost.opened.identity answers m.2) ∗
              apiDecResultAt E2E.HooksE.A0 y.ret m.1 ∗
              signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
              protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
              protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers) ∗
              FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
              stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) =
          ((cliSessStoreAt E2E.HooksE.A0 cliIo.rd x.F cliWrOk Slots.scopeKit x.peer
              (x.stores + 0xf0#64) g'.sessions ∗
            cliIdStoreAt E2E.HooksE.A0 cliIo.rd x.F cliWrOk x.peer x.stores g'.identity ∗
            storesOther5At E2E.HooksE.A0 x.stores StoresGhost.opened) ∗
            apiDecResultAt E2E.HooksE.A0 x.ret m.1 ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
            FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit) ∗
              stackAt s0.sp (wsStackV kit ikit)) ∗
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers))) ∗ R := by
        rw [hx3, hx5, ← hfold.1, ← hfold.2.1]
        dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, EncryptLemmas.w1SessKitPlaced,
          EncryptLemmas.w1IdKitPlaced, EncryptLemmas.cliSessionStoreSpecPlaced,
          EncryptLemmas.cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
          y, toDecryptGhost_placed, F]
        exact perm_spat_out
      rw [hperm_out, ← Slots.stackAt_split_of_le s0.sp hws_le hstk_sp]
      exact sepConj_mono_left (sepConj_mono hst_repack (sepConj_mono_left hres_conv))
    dsimp only [decSigSlotSpecPlaced, decSigSlotSpecPlacedOf, withCodeOk, StoreKit.withLsCodeRoLoaded]
    exact pack_slot_post (stores := storesAt E2E.HooksE.A0 x.stores)
      (res := decResAt E2E.HooksE.A0 x.ret)
      (pq := fun g e => slotTrace s0 sf ∧
        slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g e s0 sf)
      g' m.1 (And.intro hslotTrace hslotOut) (Satisfies.mono hrepack hspat_out)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ _) ∗ (F ∗ R) at honp
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨_, honp⟩ := honp
    dsimp only [withEnvPre, withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      decSigSlotSpecPlaced, decSigSlotSpecPlacedOf, withCodeOk,
      StoreKit.withLsCodeRoLoaded] at honp ⊢
    refine satisfies_allowPanicWhen_frame (fun hp => ?_) honp
    rcases hp.2 with halloc | ⟨answers, hloadRel, _, hpan_or_false⟩
    · exact Or.inr halloc
    · rcases hpan_or_false with hpan_m | hfalse
      · refine Or.inl ?_
        have hloadEq := decSessKitPlaced_loadRel_eq hinjK hsub hokPeer hloadRel
        let ca := cliAnswers Scope x.F x.peer.val
          (decKeyAux_placed ⟨W.C, W.Q⟩ Scope x.F x.peer.val x.me.val x.msg x.coins)
        have hload_ca : answers.loadSession = ca.loadSession := hloadEq
        have hpan_ca := (messageDecryptSignal_panic_iff_of_load_eq_placed W.C
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
          (serializeAddrVals (serviceIdParse uuidTryParse))
          answers ca x.msg x.peer.val x.me.val
          (LibsignalTripleRatchetRepr.coinsOf x.coins) hload_ca).mp hpan_m
        rw [hS, decDefAux_placed]
        change (match LibsignalSessionApi.messageDecryptSignal W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (LibsignalTripleRatchetRepr.coinsOf x.coins) with
          | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = none
        rcases hm_ca : LibsignalSessionApi.messageDecryptSignal W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (LibsignalTripleRatchetRepr.coinsOf x.coins) with ⟨res_ca, calls_ca⟩
        rw [hm_ca] at hpan_ca
        dsimp only at hpan_ca
        rw [hpan_ca]
      · exact False.elim hfalse
  · change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    exact False.elim honex.2.1
  · change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    exact False.elim honoom.2.1

set_option maxHeartbeats 1600000 in
/-- `withLsFrozen`-guarded counterpart of `cliDecryptSignal_slot_of_inner_placed`. -/
theorem cliDecryptSignal_slot_of_inner_frozen_placed [LibsignalPlacement] {callerProg : Program}
    (W : CliHooks) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (hfs : TraceFsSound callerProg)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hS : ∀ F peer me msg coins,
      S.decryptSignal F peer me msg coins = decDefAux_placed ⟨W.C, W.Q⟩ Scope F peer me msg coins)
    (hok : ∀ F peer me, S.filesOk F peer me →
      Slots.FilesOkPeer Scope F peer ∧ Slots.DistinctSid uuidTryParse me.name peer.name)
    (hvt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      SessionOnlyVtablesPlacedOk (decSessKitPlaced F0 peer B))
    (hivt : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentityVtablesPlacedOk (decIdKitPlaced F0 peer B))
    (hInner : ∀ (F0 : FsFiles) (peer : AddrGhost),
      Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
      let kit := decSessKitPlaced F0 peer B
      let ikit := decIdKitPlaced F0 peer B
      subroutine_ok callerProg (lsmpl.base 463)
        (withEnvPre
          (withStoresDecFrozenPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
            (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
            StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
          fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files))
    (stk : Nat) (hstk : decNeedAux_placed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    subroutine_ok callerProg (lsmpl.base 463)
      (decSigSlotSpecFrozenPlaced E2E.HooksE.A0 S stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hal _hcode => ?_
  dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk, slotFramePlaced] at hpre
  obtain ⟨hfl0, ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx8, hfiles0, hfok, hstk_sp⟩,
    hcoins_lt, hspat⟩ := unpack_slot_pre hpre
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem :=
    ⟨CryptoVerification.LibsignalCodeLoaded.of_codeLoaded hfl0.2, hfl0.1⟩
  obtain ⟨hokPeer, hdist⟩ := hok x.F x.peer.val x.me.val hfok
  have hokIn : Slots.FilesOkPeer Slots.scopeIn x.F x.peer.val := filesOkPeer_mono_placed hsub hokPeer
  have hsubK : ∀ r, Scope r → Slots.scopeKit r := fun r hr => Slots.scopeKit_of_scopeIn (hsub r hr)
  have hsess0 := cliSessInv_opened_wrOk_placed hsubK hokPeer
  have hid0 := cliIdInv_opened_wrOk_placed hokPeer
  let kit := decSessKitPlaced x.F x.peer B
  let ikit := decIdKitPlaced x.F x.peer B
  let y := toDecryptGhost_placed x
  have hws_le : wsStackV kit ikit ≤ stk :=
    Nat.le_trans (wsStackV_le_cliDecryptSignalNeed_placed x.F x.peer B) hstk
  have hws_sp : wsStackV kit ikit ≤ s0.sp.toNat := Nat.le_trans hws_le hstk_sp
  let F := storesOther5At E2E.HooksE.A0 x.stores StoresGhost.opened ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit)
  have hFs0 : FsInv x.F s0.trace s0 := hfiles0 ▸ withFsInv_entry s0
  have hInnerFs := subroutine_ok_withFsInv hfs (hInner x.F x.peer hokIn) x.F s0.trace
  have hvt0 := CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.satisfies_decVtablesAtV_placed
    (kit := kit) (ikit := ikit) (hvt x.F x.peer) (hivt x.F x.peer) hcrl0.2 hspat
  have hspat_unpack :
      decVtablesAtV kit ikit ∗
        ((storesAt E2E.HooksE.A0 x.stores StoresGhost.opened ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          coinsInstalledPlaced x.coinsP x.coins ∗
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
          signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
          memRegion x.ret 48 ∗ stackAt s0.sp stk) ∗ R) ⊢
      (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
        (kit.storeAt (s0.readReg64 .x3) StoresGhost.opened.sessions ∗
          ikit.identityAt (s0.readReg64 .x5) StoresGhost.opened.identity ∗
          signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
          protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
          protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
          memRegion y.ret 48 ∗
          cliTapeAt 0#64 y.cur y.rest ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
          stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) := by
    rw [Slots.stackAt_split_of_le s0.sp hws_le hstk_sp, hx3, hx5]
    refine Entails.trans
      (sepConj_mono_right
        (sepConj_mono_left
          (sepConj_mono
            (storesAt_unpack_dec E2E.HooksE.A0 x.stores StoresGhost.opened x.F Slots.scopeKit x.peer hsess0 hid0)
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (Entails.of_eq (Slots.coinsAtPlaced_eq_coinsInstalledPlaced x.coinsP x.coins hcoins_lt).symm)))))))
      ?_
    dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, EncryptLemmas.w1SessKitPlaced,
      EncryptLemmas.w1IdKitPlaced, EncryptLemmas.cliSessionStoreSpecPlaced,
      EncryptLemmas.cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
      y, toDecryptGhost_placed, F]
    exact Entails.of_eq perm_spat_in
  have hspat_in := Satisfies.mono hspat_unpack hvt0
  have hpre_inner :
      s0.mem ⊨
        (withFsInv
          (withEnvPre
            (withStoresDecFrozenPlacedSpecVTP W.C E2E.HooksE.A0 0#64 uuidTryParse
              (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) E2E.Record.encodeRecord kit ikit
              StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
            fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)
          x.F s0.trace).pre y s0 ∗ (F ∗ R) := by
    apply withFsInv_pre_intro hFs0
    apply withEnvPre_pre_intro ⟨hfiles0, hfiles0⟩
    dsimp only [withStoresDecFrozenPlacedSpecVTP, withLsFrozen, withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hfl0, pack_inner_pre hdist hcrl0 ⟨hx0, hx1, hx2, hx4, hx6, hx8, hws_sp, rfl, rfl⟩ hspat_in⟩
  refine hInnerFs.mono_outcome y (F ∗ R) s0 hpc hrun hpre_inner hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, _hex, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hFsSf, hpost⟩ := withFsInv_post_elim hpost
    dsimp only [withEnvPre, withStoresDecFrozenPlacedSpecVTP, withLsFrozen, withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded] at hpost
    obtain ⟨answers, ⟨hnpan, _, hcalls, hidCalls, htr⟩, hspat_out⟩ := unpack_inner_post hpost
    have htr_nil := decIdKitPlaced_traceOfWith_nil x.F x.peer B E2E.Record.encodeRecord answers
      (y.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers).2
    rw [htr_nil, List.append_nil] at htr
    have hfiles_sf : sf.fs.files = x.F :=
      files_eq_at_callback hFsSf (evs := []) (by simp [htr]) (by simp [NoFsEv])
    have hslotTrace : slotTrace s0 sf :=
      ⟨by simp [htr], hfiles_sf.trans hfiles0.symm, by simp [htr]⟩
    obtain ⟨hmod_eq, hnst, hwrOk⟩ := decModel_det_placed W B Scope x.F y answers rfl hinjK hsub hokPeer
      hcalls hidCalls
    let m := y.model W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse answers
    let g' := cliFinal x.F m.2
    have hfold := cliStep_foldl_placed_eq x.F x.peer B answers m.2 StoresGhost.opened
    have hans_eq : S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins =
        match m.1 with
        | .ok pt => some (some (g', pt))
        | .error .panic => none
        | .error _ => some none := by
      rw [hS]
      have hd := decDefAux_eq_model_placed ⟨W.C, W.Q⟩ Scope x.F y
      dsimp only [y, toDecryptGhost_placed] at hd hmod_eq
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
        (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
          (kit.storeAt (s0.readReg64 .x3) (kit.storeFinal StoresGhost.opened.sessions answers m.2) ∗
            ikit.identityAt (s0.readReg64 .x5) (ikit.idFinal StoresGhost.opened.identity answers m.2) ∗
            apiDecResultAt E2E.HooksE.A0 y.ret m.1 ∗
            signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
            protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
            protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers) ∗
            FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
            stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) ⊢
        (storesAt E2E.HooksE.A0 x.stores g' ∗
          decResAt E2E.HooksE.A0 x.ret m.1 ∗
          protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
          protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
          signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
          FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗ stackAt s0.sp stk ∗
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
            cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers))) ∗ R := by
      have hst_repack := storesAt_repack_dec E2E.HooksE.A0 x.stores StoresGhost.opened g'
        x.F Slots.scopeKit x.peer hfold.2.2.1 (congrArg KyberGhost.oneTime hfold.2.2.2.1)
        (congrArg KyberGhost.lastResort hfold.2.2.2.1) hfold.2.2.2.2.1 hfold.2.2.2.2.2
      have hres_conv := apiDecResultAt_entails_decResAt E2E.HooksE.A0 x.ret m.1 hnst
      have hperm_out :
          (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
            (kit.storeAt (s0.readReg64 .x3) (kit.storeFinal StoresGhost.opened.sessions answers m.2) ∗
              ikit.identityAt (s0.readReg64 .x5) (ikit.idFinal StoresGhost.opened.identity answers m.2) ∗
              apiDecResultAt E2E.HooksE.A0 y.ret m.1 ∗
              signalMessageAt E2E.HooksE.A0 y.msgG y.msgA y.msg ∗
              protocolAddressAt E2E.HooksE.A0 y.rem y.remA ∗
              protocolAddressAt E2E.HooksE.A0 y.loc y.locA ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers) ∗
              FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗
              stackAt s0.sp (wsStackV kit ikit) ∗ E2E.HooksE.A0.pool)) ∗ (F ∗ R) =
          ((cliSessStoreAt E2E.HooksE.A0 cliIo.rd x.F cliWrOk Slots.scopeKit x.peer
              (x.stores + 0xf0#64) g'.sessions ∗
            cliIdStoreAt E2E.HooksE.A0 cliIo.rd x.F cliWrOk x.peer x.stores g'.identity ∗
            storesOther5At E2E.HooksE.A0 x.stores StoresGhost.opened) ∗
            apiDecResultAt E2E.HooksE.A0 x.ret m.1 ∗
            protocolAddressAt E2E.HooksE.A0 x.peer x.peerA ∗
            protocolAddressAt E2E.HooksE.A0 x.me x.meA ∗
            signalMessageAt E2E.HooksE.A0 x.msgG x.msgA x.msg ∗
            FromRecordCallees.lsLogOff ∗ E2E.HooksE.A0.pool ∗
            (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - wsStackV kit ikit) ∗
              stackAt s0.sp (wsStackV kit ikit)) ∗
            (SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ decVtablesAtV kit ikit ∗
              cliTapeAfter 0#64 y.cur y.rest (y.draws W.C answers))) ∗ R := by
        rw [hx3, hx5, ← hfold.1, ← hfold.2.1]
        dsimp only [kit, ikit, decSessKitPlaced, decIdKitPlaced, EncryptLemmas.w1SessKitPlaced,
          EncryptLemmas.w1IdKitPlaced, EncryptLemmas.cliSessionStoreSpecPlaced,
          EncryptLemmas.cliIdentityStoreSpecPlaced, cliSessionStoreSpec, cliIdentityStoreSpec,
          y, toDecryptGhost_placed, F]
        exact perm_spat_out
      rw [hperm_out, ← Slots.stackAt_split_of_le s0.sp hws_le hstk_sp]
      exact sepConj_mono_left (sepConj_mono hst_repack (sepConj_mono_left hres_conv))
    dsimp only [decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk]
    exact pack_slot_post (stores := storesAt E2E.HooksE.A0 x.stores)
      (res := decResAt E2E.HooksE.A0 x.ret)
      (pq := fun g e => slotTrace s0 sf ∧
        slotOut (S.decryptSignal x.F x.peer.val x.me.val x.msg x.coins) g e s0 sf)
      g' m.1 (And.intro hslotTrace hslotOut) (Satisfies.mono hrepack hspat_out)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ _) ∗ (F ∗ R) at honp
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    obtain ⟨_, honp⟩ := honp
    dsimp only [withEnvPre, withStoresDecFrozenPlacedSpecVTP, withLsFrozen, withStoresDecPlacedSpecVTP,
      CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecPlacedSpecVX,
      decSigSlotSpecFrozenPlaced, decSigSlotSpecPlacedOf, withCodeOk,
      StoreKit.withLsCodeRoLoaded] at honp ⊢
    refine satisfies_allowPanicWhen_frame (fun hp => ?_) honp
    rcases hp.2 with halloc | ⟨answers, hloadRel, _, hpan_or_false⟩
    · exact Or.inr halloc
    · rcases hpan_or_false with hpan_m | hfalse
      · refine Or.inl ?_
        have hloadEq := decSessKitPlaced_loadRel_eq hinjK hsub hokPeer hloadRel
        let ca := cliAnswers Scope x.F x.peer.val
          (decKeyAux_placed ⟨W.C, W.Q⟩ Scope x.F x.peer.val x.me.val x.msg x.coins)
        have hload_ca : answers.loadSession = ca.loadSession := hloadEq
        have hpan_ca := (messageDecryptSignal_panic_iff_of_load_eq_placed W.C
          (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
          (serializeAddrVals (serviceIdParse uuidTryParse))
          answers ca x.msg x.peer.val x.me.val
          (LibsignalTripleRatchetRepr.coinsOf x.coins) hload_ca).mp hpan_m
        rw [hS, decDefAux_placed]
        change (match LibsignalSessionApi.messageDecryptSignal W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (LibsignalTripleRatchetRepr.coinsOf x.coins) with
          | (.ok pt, calls) => some (some (cliFinal x.F calls, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = none
        rcases hm_ca : LibsignalSessionApi.messageDecryptSignal W.C (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩).spqr
            (serializeAddrVals (serviceIdParse uuidTryParse)) ca x.msg x.peer.val x.me.val
            (LibsignalTripleRatchetRepr.coinsOf x.coins) with ⟨res_ca, calls_ca⟩
        rw [hm_ca] at hpan_ca
        dsimp only at hpan_ca
        rw [hpan_ca]
      · exact False.elim hfalse
  · change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    rw [sepConj_assoc, satisfies_pure_sepConj] at honex
    exact False.elim honex.2.1
  · change sf.mem ⊨ (⌜FsInv x.F s0.trace sf⌝ ∗ ⌜False⌝) ∗ (F ∗ R) at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    rw [sepConj_assoc, satisfies_pure_sepConj] at honoom
    exact False.elim honoom.2.1

end CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas
