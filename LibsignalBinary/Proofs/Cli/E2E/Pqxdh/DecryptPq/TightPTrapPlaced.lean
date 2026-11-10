/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TryDecryptHsCodeSym
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPModel
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepTightTargets
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKey
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMac
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model

/-!
# Relocatable `[LibsignalPlacement]` Contracts for Handshake `try_decrypt_with_state::<Coins>`

Defines weak-`pre` and tight-`onPanic` relocatable contracts (`tryDecryptPlacedSpecP`,
`tryDecryptPlacedSpecTP`, `tryDecryptPlacedSpecTPTight`, `tryDecryptPlacedSpecQF_PTight`)
and outcome-lifting lemmas for `try_decrypt_with_state::<signal_session_handshake::Coins>`
(`blkPl_508`, calling `signal_session_coins_fill` at `lsmpl.base 618` and `spqr::recv` at
`lsmpl.base 329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.CliHandshake.TryDecPlaced

theorem blk507_base_eq [LibsignalPlacement] : (blkPl_508).base = lsmpl.base 508 := rfl

/-- Relocatable `[LibsignalPlacement]` CLI `tryDecryptPlacedSpec` weakened to `DistinctSid`
(`remoteIdentity ≠ some localIdentity ∨ DistinctSid`). -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
      s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
      (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
        CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
      SeedsLen32 x.st ∧
      x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
    sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
    memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
    stackAt s.sp rootStack ∗ A.pool
  post := (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).post
  onPanic := (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).onPanic

/-- Relocatable `[LibsignalPlacement]` `tryDecryptSpecTP` over `tryDecryptPlacedSpecP` with `TokenInit`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LibsignalSpqrV1.TokenInit tryDecryptPlacedImg ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      LibsignalSpqrV1.TokenInit tryDecryptPlacedImg ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidParse S).post x s0 sf }

/-- Relocatable `[LibsignalPlacement]` `tryDecryptPlacedSpecTP` with tight `onPanic`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTPTight
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP C A ctl uuidParse S with
    onPanic := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S uuidParse }

/-- `tryDecryptPlacedSpecP` restricted to `Q x.st.pqRatchetState` with frame `F` and tight `onPanic`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight
    [LibsignalPlacement] (Q : List (BitVec 8) → Prop) (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl parse S with
    pre := fun x s =>
      ⌜Q x.st.pqRatchetState⌝ ∗ F ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl parse S).pre x s
    post := fun x s0 sf =>
      F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl parse S).post x s0 sf
    onPanic := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S parse }

/-- Extract `SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat`
from `(tryDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗ R`. -/
theorem seedsLen32_of_pre_P_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.2.2.2.2.2.2.2

theorem restLen_of_pre_P_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP C A ctl uuidTryParse S).pre x s0 ∗ R) :
    x.rest.length < 2 ^ 63 := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP] at hpre
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero] at hpre
  have hpre' : s0.mem ⊨ ⌜x.rest.length < 2 ^ 63⌝ ∗
      (⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.ss ∧ s0.readReg64 .x2 = x.remA ∧
        s0.readReg64 .x3 = x.locA ∧ s0.readReg64 .x4 = x.msgA ∧
        (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
          CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes) ∧
        SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat⌝ ∗
       sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
       stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
    convert hpre using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hpre'
  exact hpre'.1

theorem reaches_outcome_of_panicQF_PTight_placed [LibsignalPlacement]
    {P : Program} {Q : List (BitVec 8) → Prop}
    {F : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight Q F C A ctl uuidTryParse S)
      x R s0 s :=
  Arm64.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight Q F C A ctl uuidTryParse S)
      hpan hq)

theorem tryDecrypt_onPanicTight_of_afterCmk_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {x : TryDecryptGhost}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator} {R : SepProp}
    {s0 sf : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : sf.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htrace⟩, hmem⟩ := h
  refine ⟨⟨?_, htrace⟩, hmem⟩
  rcases hc with hm | hp | ha
  · exact Or.inl hm
  · exact Or.inl (CryptoVerification.LibsignalTripleRatchet.Decrypt.Model.model_of_recvPanics htr herc hcmk hp)
  · exact Or.inr ha

/-- Post-`consumeMessageKey`, any `reaches_outcome` for loose `tryDecryptPlacedSpec` with frame `F ∗ R`
lifts directly to `tryDecryptPlacedSpecQF_PTight` with frame `R`. -/
theorem reaches_outcome_tryDecryptSpecQF_PTight_of_afterCmk_placed [LibsignalPlacement]
    {P : Program} {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator} {R : SepProp} {s0 s : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidTryParse S)
      x (F ∗ R) s0 s) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight Q F C A ctl uuidTryParse S)
      x R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP]
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan,
      onPanicTight_drop_frame (tryDecrypt_onPanicTight_of_afterCmk_placed htr herc hcmk hqp)⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

def tryDecryptPlacedTightSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl parse S with
    onPanic := tryDecryptOnPanicTight C S parse }

/-- Lift a `reaches_outcome` for `tryDecryptPlacedTightSpec` with frame `F ∗ R`
into `tryDecryptPlacedSpecQF_PTight` with frame `R`. -/
theorem reaches_outcome_tryDecryptSpecQF_PTight_of_tight_placed [LibsignalPlacement]
    {P : Program} {Q : List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P
      (tryDecryptPlacedTightSpec C A ctl uuidTryParse S)
      x (F ∗ R) s0 s) :
    reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight Q F C A ctl uuidTryParse S)
      x R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPlacedSpecQF_PTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP,
      tryDecryptPlacedTightSpec] at hpost ⊢
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, onPanicTight_drop_frame hqp⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Whenever `(x.model C S uuidTryParse).1 ≠ .error .panic`, a `reaches_outcome` for
`tryDecryptPlacedSpec` under `spqrDropPanic S` lifts to `tryDecryptPlacedTightSpec` under `S`. -/
theorem reaches_outcome_tight_of_spqrDropPanic_placed [LibsignalPlacement]
    {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (hne : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (h : reaches_outcome P
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidTryParse (spqrDropPanic S))
      x R s0 s) :
    reaches_outcome P
      (tryDecryptPlacedTightSpec C A ctl uuidTryParse S)
      x R s0 s := by
  have hmod := model_spqrDropPanic_eq_of_ne_panic hne
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [tryDecryptPlacedTightSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec] at hpost ⊢
    rwa [hmod] at hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec] at hqp
    rw [hmod] at hqp
    dsimp only [spqrDropPanic] at hqp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hqp
    dsimp only [tryDecryptPlacedTightSpec, tryDecryptOnPanicTight]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    obtain ⟨⟨hc, htr⟩, hmem⟩ := hqp
    refine ⟨⟨?_, htr⟩, hmem⟩
    rcases hc with hm | hp | ha
    · exact Or.inl hm
    · cases hp
    · exact Or.inr ha
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Relocatable `[LibsignalPlacement]` `tryDecryptSpecT` over `tryDecryptPlacedSpec` with `TokenInit`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT
    [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LibsignalSpqrV1.TokenInit tryDecryptPlacedImg ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      LibsignalSpqrV1.TokenInit tryDecryptPlacedImg ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl uuidParse S).post x s0 sf }

/-! ## Placed Run Statement Abbreviations -/

/-- `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmt_trap`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPlaced
    [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT C A ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 C.F K)))

/-- `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmtP_trap`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPPlaced
    [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP C A ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 C.F K)))

/-- `[LibsignalPlacement]` twin of `TryDecryptPqV1RunStmtPTight_trap`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPTightPlaced
    [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    subroutine_ok ((blkPC_508).rebase (blkPl_508).base abs)
      (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTPTight C A ctl uuidTryParse
          (LibsignalSpqrV1.spqrV1 C.F K)))

theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT
    [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {x : TryDecryptGhost} {s : State} {R : SepProp}
    (h : s.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT C A ctl parse S).pre x s ∗ R) :
    s.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP C A ctl parse S).pre x s ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecT,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP,
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hq, h⟩
  refine ⟨hq, ?_⟩
  rw [sepConj_assoc, sepConj_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, hne, hseeds, hchains, hstk⟩, hmem⟩ := h
  exact ⟨⟨h0, h1, h2, h3, h4, h5, Or.inl hne, hseeds, hchains, hstk⟩, hmem⟩

theorem tryDecryptPlacedOnPanicTight_weaken [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {parse : UuidParser}
    {x : TryDecryptGhost} {s0 sf : State} {R : SepProp}
    (h : sf.mem ⊨ CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec C A ctl parse S).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
    tryDecryptOnPanicTight,
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  rcases h.1.1 with hm | ha
  · exact Or.inl hm
  · exact Or.inr (Or.inr ha)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_P_placed_of_PTight
    [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {K : LibsignalSpqrV1.MlKem} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPTightPlaced C A ctl K abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPPlaced C A ctl K abs := by
  intro hH hQ x R s0 hpc hrun hpre hsp
  refine (h hH hQ x R s0 hpc hrun hpre hsp).mono_outcome (fun _ hout => ?_)
  rcases hout with h1 | ⟨hpan, hqp⟩ | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptPlacedOnPanicTight_weaken (A := A) (ctl := ctl) hqp⟩)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_placed_of_P
    [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {K : LibsignalSpqrV1.MlKem} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPPlaced C A ctl K abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtPlaced C A ctl K abs := by
  intro hH hQ x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc] at hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K))).pre x s0 ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc]
    exact CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPlacedSpecTP_pre_of_tryDecryptPlacedSpecT hpre
  exact h hH hQ x R s0 hpc hrun hpre' hsp

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
