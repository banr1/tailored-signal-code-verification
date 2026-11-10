/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Handshake `try_decrypt_with_state::<Coins>`

Budget-threaded (`RustCliAllocBudget M` / `BudgetLimits`) relocatable contracts
(`tryDecryptPlacedSpecP`, `tryDecryptPlacedSpecTP`, `tryDecryptPlacedSpecTPTight`,
`tryDecryptPlacedSpecQF_PTight`) and tight-`onPanic` outcome lifts for
`try_decrypt_with_state::<signal_session_handshake::Coins>` (`blkPl_508`), dropping
`allocFailedIn` from `onPanic` under `FitsEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  ChainKey Crypto MessageKeyGenerator Mut RatchetState
  SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508)
open CryptoVerification.LibsignalSpqrV1 (MlKem TokenInit spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32 SpqrModel TryDecryptGhost rootStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptPlacedImg)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model (model_of_recvPanics)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (
  model_spqrDropPanic_eq_of_ne_panic spqrDropPanic
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (SpqrHooksBudget TripleRatchetHooksBudget)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs tryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)

/-! ## 1. Budget-Threaded Relocatable `[LibsignalPlacement]` `tryDecryptPlaced*` Contracts -/

theorem blk507_base_eq [LibsignalPlacement] : (blkPl_508).base = lsmpl.base 508 := rfl

/-- Alias of `OnPanicTightBudget.tryDecryptOnPanicTight` (drops both `S.recvPanics` and
`allocFailedIn`). -/
abbrev tryDecryptPqOnPanicTight := @tryDecryptOnPanicTight

/-- Budget-threaded relocatable `[LibsignalPlacement]` CLI `tryDecryptPlacedSpec` weakened to
`DistinctSid` (`remoteIdentity ≠ some localIdentity ∨ DistinctSid`), reusing
`Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP` via `A.atState` and dropping `allocFailedIn`
from `onPanic`. -/
def tryDecryptPlacedSpecP [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post :=
    (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv).post
  onPanic :=
    (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv).onPanic

/-- Budget-threaded relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecTP` over
`tryDecryptPlacedSpecP` with `TokenInit tryDecryptPlacedImg`. -/
def tryDecryptPlacedSpecTP [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { tryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st) s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit tryDecryptPlacedImg ∗
        (tryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv).pre (x, st) s
    post := fun (x, st) s0 sf =>
      TokenInit tryDecryptPlacedImg ∗
        (tryDecryptPlacedSpecP C A lim ctl uuidParse S tdEnv).post (x, st) s0 sf }

/-- Budget-threaded relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecTP` with tight
`onPanic := tryDecryptOnPanicTight` (dropping both `S.recvPanics` and `allocFailedIn`). -/
def tryDecryptPlacedSpecTPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { tryDecryptPlacedSpecTP C A lim ctl uuidParse S tdEnv with
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S uuidParse x s0 sf }

/-- Budget-threaded `tryDecryptPlacedSpecP` restricted to `Q x.st.pqRatchetState` with frame `F`
and tight `onPanic`. -/
def tryDecryptPlacedSpecQF_PTight [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { tryDecryptPlacedSpecP C A lim ctl parse S tdEnv with
    pre := fun (x, st) s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗
        (tryDecryptPlacedSpecP C A lim ctl parse S tdEnv).pre (x, st) s
    post := fun (x, st) s0 sf =>
      F ∗ (tryDecryptPlacedSpecP C A lim ctl parse S tdEnv).post (x, st) s0 sf
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S parse x s0 sf }

/-! ## 2. Precondition Projections, Tight-`onPanic` Helpers & Outcome Lifts -/

/-- Extract `FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))` from
`(tryDecryptPlacedSpecP C A lim ctl parse S tdEnv).pre (x, st) s0 ∗ R`. -/
theorem fitsEnv_of_pre_P_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (tryDecryptPlacedSpecP C A lim ctl parse S tdEnv).pre (x, st) s0 ∗ R) :
    FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x)) := by
  dsimp only [tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Extract `SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat`
from `(tryDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st) s0 ∗ R`. -/
theorem seedsLen32_of_pre_P_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st) s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  dsimp only [tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact CryptoVerification.LibsignalTripleRatchet.DecryptPq.seedsLen32_of_pre_P_placed hpre.2

theorem restLen_of_pre_P_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptPlacedSpecP C A lim ctl uuidTryParse S tdEnv).pre (x, st) s0 ∗ R) :
    x.rest.length < 2 ^ 63 := by
  dsimp only [tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact CryptoVerification.LibsignalTripleRatchet.DecryptPq.restLen_of_pre_P_placed hpre.2

/-- Absorb frame `F` into `anyHeap` in `OnPanicTightBudget.tryDecryptOnPanicTight`. -/
theorem onPanicTight_drop_frame {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R := by
  dsimp only [tryDecryptOnPanicTight] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

/-- Lift a `consumeMessageKey` `.panic` outcome into `OnPanicTightBudget.tryDecryptOnPanicTight`. -/
theorem onPanicTight_of_cmk_panic {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S parse).1 = .error e)
    (hp : e = .panic ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R := by
  have hcond : (x.model C S parse).1 = .error .panic ∧ s0.trace <+: s'.trace :=
    ⟨hp.1 ▸ hm1, hp.2⟩
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcond, hmem⟩

theorem reaches_outcome_of_panicQF_PTight_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R) :
    reaches_outcome P
      (tryDecryptPlacedSpecQF_PTight Q F C A lim ctl uuidTryParse S tdEnv)
      (x, st) R s0 s :=
  Arm64.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := tryDecryptPlacedSpecQF_PTight Q F C A lim ctl uuidTryParse S tdEnv)
      hpan hq)

theorem tryDecrypt_onPanicTight_of_afterCmk_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator} {R : SepProp}
    {s0 sf : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : sf.mem ⊨
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
        C A lim ctl uuidTryParse S tdEnv).onPanic (x, st) s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  dsimp only [
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htrace⟩, hmem⟩ := h
  refine ⟨⟨?_, htrace⟩, hmem⟩
  rcases hc with hm | hp
  · exact hm
  · exact model_of_recvPanics htr herc hcmk hp

/-- Post-`consumeMessageKey`, any `reaches_outcome` for loose `DefsPlacedBudget.tryDecryptPlacedSpec`
with frame `F ∗ R` lifts directly to `tryDecryptPlacedSpecQF_PTight` with frame `R`. -/
theorem reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Program} {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {R : SepProp} {s0 s : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : reaches_outcome P
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
        C A lim ctl uuidTryParse S tdEnv)
      (x, st) (F ∗ R) s0 s) :
    reaches_outcome P
      (tryDecryptPlacedSpecQF_PTight Q F C A lim ctl uuidTryParse S tdEnv)
      (x, st) R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [tryDecryptPlacedSpecQF_PTight, tryDecryptPlacedSpecP]
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan,
      onPanicTight_drop_frame (tryDecrypt_onPanicTight_of_afterCmk_placed htr herc hcmk hqp)⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

def tryDecryptPlacedTightSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl parse S tdEnv with
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S parse x s0 sf }

/-- Lift a `reaches_outcome` for `tryDecryptPlacedTightSpec` with frame `F ∗ R`
into `tryDecryptPlacedSpecQF_PTight` with frame `R`. -/
theorem reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Program} {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P
      (tryDecryptPlacedTightSpec C A lim ctl uuidTryParse S tdEnv)
      (x, st) (F ∗ R) s0 s) :
    reaches_outcome P
      (tryDecryptPlacedSpecQF_PTight Q F C A lim ctl uuidTryParse S tdEnv)
      (x, st) R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [tryDecryptPlacedSpecQF_PTight, tryDecryptPlacedSpecP,
      tryDecryptPlacedTightSpec] at hpost ⊢
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, onPanicTight_drop_frame hqp⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Whenever `(x.model C S uuidTryParse).1 ≠ .error .panic`, a `reaches_outcome` for
`DefsPlacedBudget.tryDecryptPlacedSpec` under `spqrDropPanic S` lifts to
`tryDecryptPlacedTightSpec` under `S`. -/
theorem reaches_outcome_tight_of_spqrDropPanic_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    (hne : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (h : reaches_outcome P
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
        C A lim ctl uuidTryParse (spqrDropPanic S) tdEnv)
      (x, st) R s0 s) :
    reaches_outcome P
      (tryDecryptPlacedTightSpec C A lim ctl uuidTryParse S tdEnv)
      (x, st) R s0 s := by
  have hmod := model_spqrDropPanic_eq_of_ne_panic hne
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    have hpost_eq :
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
          C A lim ctl uuidTryParse (spqrDropPanic S) tdEnv).post (x, st) s0 s' =
        (tryDecryptPlacedTightSpec C A lim ctl uuidTryParse S tdEnv).post (x, st) s0 s' := by
      dsimp only [tryDecryptPlacedTightSpec,
        LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec]
      rw [hmod]
    rwa [← hpost_eq]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec] at hqp
    rw [hmod] at hqp
    dsimp only [spqrDropPanic] at hqp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hqp
    dsimp only [tryDecryptPlacedTightSpec, tryDecryptOnPanicTight]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    obtain ⟨⟨hc, htr⟩, hmem⟩ := hqp
    refine ⟨⟨?_, htr⟩, hmem⟩
    rcases hc with hm | hp
    · exact hm
    · cases hp
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Budget-threaded relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecT` over
`DefsPlacedBudget.tryDecryptPlacedSpec` with `TokenInit tryDecryptPlacedImg`. -/
def tryDecryptPlacedSpecT [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st) s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit tryDecryptPlacedImg ∗
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
          C A lim ctl uuidParse S tdEnv).pre (x, st) s
    post := fun (x, st) s0 sf =>
      TokenInit tryDecryptPlacedImg ∗
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
          C A lim ctl uuidParse S tdEnv).post (x, st) s0 sf }

/-! ## 3. Budget-Threaded Placed Run Statement Abbreviations & Weakening Bridges -/

/-- Budget-threaded `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmtPlaced`. -/
def TryDecryptPqV1RunStmtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecT C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

/-- Budget-threaded `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmtPPlaced`. -/
def TryDecryptPqV1RunStmtPPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecTP C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

/-- Budget-threaded `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmtPTightPlaced`. -/
def TryDecryptPqV1RunStmtPTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (K : MlKem) (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooksBudget C M A lim (spqrV1 C.F K) abs →
    SpqrHooksBudget C M A lim K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (tryDecryptPlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv))

theorem tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT [LibsignalPlacement]
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {s : State} {R : SepProp}
    (h : s.mem ⊨ (tryDecryptPlacedSpecT C A lim ctl parse S tdEnv).pre (x, st) s ∗ R) :
    s.mem ⊨ (tryDecryptPlacedSpecTP C A lim ctl parse S tdEnv).pre (x, st) s ∗ R := by
  have h0 : s.mem ⊨
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT
        C (A.atState lim st s) ctl parse S).pre x s ∗
      (⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗ R) := by
    dsimp only [tryDecryptPlacedSpecT,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT] at h ⊢
    convert h using 1
    sep_ac_rfl
  have h1 :=
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT h0
  dsimp only [tryDecryptPlacedSpecTP, tryDecryptPlacedSpecP,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP] at h1 ⊢
  convert h1 using 1
  sep_ac_rfl

theorem tryDecryptPlacedOnPanicTight_weaken [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st : M.σ} {s0 sf : State} {R : SepProp}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
        C A lim ctl parse S tdEnv).onPanic (x, st) s0 sf ∗ R := by
  dsimp only [tryDecryptOnPanicTight,
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  exact ⟨⟨Or.inl h.1.1, h.1.2⟩, h.2⟩

theorem tryDecryptPqV1_ok_P_placed_of_PTight [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {K : MlKem} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {abs : String → Option (State → State)}
    (h : TryDecryptPqV1RunStmtPTightPlaced C A lim ctl K tdEnv abs) :
    TryDecryptPqV1RunStmtPPlaced C A lim ctl K tdEnv abs := by
  intro hH hQ
  refine subroutine_ok_mono (h hH hQ)
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => hq)
    (fun ⟨_, st⟩ _ _ _ hp =>
      tryDecryptPlacedOnPanicTight_weaken (A := A) (lim := lim) (ctl := ctl)
        (tdEnv := tdEnv) (st := st) hp)

theorem tryDecryptPqV1_ok_placed_of_P [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {K : MlKem} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {abs : String → Option (State → State)}
    (h : TryDecryptPqV1RunStmtPPlaced C A lim ctl K tdEnv abs) :
    TryDecryptPqV1RunStmtPlaced C A lim ctl K tdEnv abs := by
  intro hH hQ
  refine subroutine_ok_mono (h hH hQ)
    (fun ⟨x, st⟩ R s0 hpre => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc] at hpre ⊢
  exact tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT hpre

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget
