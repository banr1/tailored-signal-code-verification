/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees

/-!
# Poll Entry Vtable Equalities and Exit/Panic Packaging

Establishes definitional vtable equalities matching `cliPollStoresKitsAt`, packages closure return
paths into `dpPollSpecState.post` (`dpPollPost_of_decResAt` and `dpPollPost_of_decResAt_ext`), and
bridges `PanicOomProp` and `genP3S5PanicProp` to `dpPollSpecState.onPanic`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Vtable Definitional Equalities -/

theorem sessVt_eq_cliPollSessKit (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost) (σ : DpKitStk) :
    sessVt img = (cliPollSessKit A img.base F0 Scope peer σ).ss_vt :=
  rfl

theorem idVt_eq_cliPollIdKit (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    (peer : AddrGhost) (σ : DpKitStk) :
    idVt img = (cliPollIdKit A img.base F0 peer σ).id_vt :=
  rfl

theorem oneTimeVt_eq_cliPollPkKit (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk) :
    oneTimeVt img = (cliPollPkKit A img.base F0 pid σ).pk_vt :=
  rfl

theorem signedVt_eq_cliPollSpkKit (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    (sid : BitVec 32) (σ : DpKitStk) :
    signedVt img = (cliPollSpkKit A img.base F0 sid σ).spk_vt :=
  rfl

theorem kyberVt_eq_cliPollKpkKit (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    (kid ksid : BitVec 32) (kbk : PublicKey) (σ : DpKitStk) :
    kyberVt img = (cliPollKpkKit A img.base F0 kid ksid kbk σ).kpk_vt :=
  rfl

/-! ## 2. Exit Postcondition Packager (`dpPollPost_of_decResAt`) -/

private theorem pure_sepConj_intro {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, emp_sepConj]
  exact h

/-- Packages `decResAt`, `storesAt`, preserved caller borrows, `dpFutDoneAt`, `memRegion cx 32`,
`stackAt s0.sp stk'`, and any leftover heap `Leftover` (vtable read-only cells, `TokenInit`,
`Coins`, etc.) into `dpPollSpecState.post` at `dpSlotPollKState E2E.HooksE.A0 img B S`. -/
theorem dpPollPost_of_decResAt {img : Obj.Image} {W : CliHooks} (B : RunBudgets) (S : RunSem)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState E2E.HooksE.A0 img B S))
    (s0 sf : State)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W))
    (hsteps : Steps (tripleRatchetProgAtExt img.base (cliExterns W)) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt E2E.HooksE.A0 y.out e ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      E2E.HooksE.A0.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      ((dpPollSpecState (dpSlotPollKState E2E.HooksE.A0 img B S) stk').inImage img).post y s0 sf := by
  have hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
    cliSlotTraceFT_of_trace_eq hh hsteps htr
  have hdec := decResAt_entails_dpWords_resHeap E2E.HooksE.A0 y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKState E2E.HooksE.A0 img B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws ∗ dpResHeap E2E.HooksE.A0 ws e) ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ E2E.HooksE.A0.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g s0.fs s0.trace sf.fs sf.trace ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗ dpResHeap E2E.HooksE.A0 ws e) ∗
      storesAt E2E.HooksE.A0 y.g.stores g' ∗
      protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
      protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
      preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ E2E.HooksE.A0.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗
        (storesAt E2E.HooksE.A0 y.g.stores g' ∗ dpResHeap E2E.HooksE.A0 ws e ∗
          protocolAddressAt E2E.HooksE.A0 y.g.peer y.g.peerA ∗
          protocolAddressAt E2E.HooksE.A0 y.g.me y.g.meA ∗
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ E2E.HooksE.A0.pool ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by
    ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws ?_)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  dsimp only [K, dpSlotPollKState]
  exact Entails.sepExists_right g'
    (Entails.sepExists_right e (pure_sepConj_intro ⟨hft, hout⟩ (Entails.refl _)))

/-- Allocator- and extern-polymorphic counterpart of `dpPollPost_of_decResAt`: packages `decResAt A`,
`storesAt A`, preserved caller borrows, `dpFutDoneAt`, `memRegion cx 32`, `stackAt s0.sp stk'`, and
any leftover heap `Leftover` into `dpPollSpecState.post` at `dpSlotPollKState A img B S` from
`TraceFsSound (tripleRatchetProgAtExt img.base ext)`. -/
theorem dpPollPost_of_decResAt_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem)
    (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 sf : State)
    (g' : StoresGhost) (e : Except (ApiError AddrVal Unit) E2E.Bytes)
    (Leftover : SepProp)
    (hfs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hsteps : Steps (tripleRatchetProgAtExt img.base ext) s0 sf)
    (htr : sf.trace = s0.trace)
    (hout : slotOutTr (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
      g' e s0.trace sf.trace) :
    decResAt A y.out e ∗
      storesAt A y.g.stores g' ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗
      A.pool ∗
      Leftover ∗
      dpFutDoneAt y.fut ∗
      memRegion y.cx 32 ∗
      stackAt s0.sp stk' ⊢
      ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf := by
  have hft : slotTraceFT s0.fs s0.trace sf.fs sf.trace :=
    ⟨htr ▸ List.prefix_refl s0.trace,
     hfs.files_eq hsteps (evs := []) (by rw [htr, List.append_nil]) NoFsEv.nil,
     congrArg (ProcessOutcome.traceStreamBytes .stdout) htr⟩
  have hdec := decResAt_entails_dpWords_resHeap A y.out e
  have hany : Leftover ⊢ anyHeap := entails_anyHeap Leftover
  refine Entails.trans (sepConj_mono hdec
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hany)))))))) ?_
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun ws => ?_
  let K := dpSlotPollKState A img B S
  change (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws ∗ dpResHeap A ws e) ∗
      storesAt A y.g.stores g' ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' ⊢
    (∃∗ ws', ⌜ws'.length = 6 ∧ ws'.head? ≠ some pendingTag⌝ ∗
      dpWordsAt y.out ws' ∗ K.res y.g s0.fs s0.trace sf.fs sf.trace ws') ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk'
  have hreord :
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗ dpResHeap A ws e) ∗
      storesAt A y.g.stores g' ∗
      protocolAddressAt A y.g.peer y.g.peerA ∗
      protocolAddressAt A y.g.me y.g.meA ∗
      preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
      logOff img ∗ A.pool ∗ anyHeap ∗
      dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk' =
      (⌜ws.length = 6 ∧ ws.head? ≠ some pendingTag⌝ ∗
        dpWordsAt y.out ws ∗
        (storesAt A y.g.stores g' ∗ dpResHeap A ws e ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗ A.pool ∗ anyHeap)) ∗
      (dpFutDoneAt y.fut ∗ memRegion y.cx 32 ∗ stackAt s0.sp stk') := by
    ac_rfl
  rw [hreord]
  refine sepConj_mono_left (Entails.sepExists_right ws ?_)
  refine sepConj_mono_right (sepConj_mono_right ?_)
  dsimp only [K, dpSlotPollKState]
  exact Entails.sepExists_right g'
    (Entails.sepExists_right e (pure_sepConj_intro ⟨hft, hout⟩ (Entails.refl _)))

/-! ## 3. Panic & OOM Postcondition Packagers -/

/-- Introduces `dpPollSpecState.onPanic` from `s0.trace <+: sf.trace` and
`allocFailedIn s0 sf ∨ K.panics y.g`. -/
theorem dpPollOnPanic_of_or {K : DpPollKState} (stk' : Nat)
    (y : DpPollGhostState K) (s0 sf : State) (P : SepProp)
    (htr : s0.trace <+: sf.trace)
    (hpan : allocFailedIn s0 sf ∨ K.panics y.g) :
    P ⊢ (dpPollSpecState K stk').onPanic y s0 sf := by
  dsimp only [dpPollSpecState]
  exact pure_sepConj_intro ⟨htr, hpan⟩ (entails_anyHeap P)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll

