/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.Decrypt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailExt
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.AesDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ApplyRatchet
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.FindChain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ChainLookup.TightTargets
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.ConsumeMsgKey
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepTightTargets
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTightModel
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.VerifyMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.Cli.TripleRatchet.RunAssembly.DecryptAssembly
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# CLI Ratchet `try_decrypt_with_state::<signal_session_ratchet::Coins>` under `DistinctSid` and Tight `onPanic`

Proves the contract-backed (`Stage2ContractsExt` / `CliExternsOk`) `tryDecryptSpecTPTight` theorems
on `tripleRatchetProgAtExt img.base ext` and specializes to the fixed-table `tripleRatchetProgAt`
kit theorems (`tryDecryptTPTight_run_of_seamW`, `tryDecryptTPTight_prog_run_of_seamW`, and
`CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib CryptoGames CryptoGames.HKDF CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalSpqrV1.M4
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Outcome-Strengthening Bridges for `tryDecryptSpecTPTight` -/

theorem tryDecryptSpecTPTight_pre_iff (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (img : Obj.Image) (x : TryDecryptGhost) (R : SepProp) (s0 : State) :
    (s0.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img).pre x s0 ∗ R) ↔
      x.st.pqRatchetState.length < 2 ^ 32 ∧
        (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗
          (TokenInit img ∗ R)) := by
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP]
  have heq : (⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ TokenInit img ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0) ∗ R =
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        ((CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗
          (TokenInit img ∗ R)) := by ac_rfl
  rw [heq, satisfies_pure_sepConj]

alias tryDecryptSpecTPTight_pre_iff_ext := tryDecryptSpecTPTight_pre_iff

theorem tdp_reaches_outcome_specTPTight_ext {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x (TokenInit img ∗ R) s0 s) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight] at hpost ⊢
    have heq : (TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf) ∗ R =
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗
          (TokenInit img ∗ R) := by ac_rfl
    exact heq ▸ hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      tryDecryptOnPanicTight] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hq2 := hq.2
    rw [← sepConj_assoc] at hq2
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq2
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem tdp_reaches_outcome_weaken_tight_ext {prog : Program}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem tdp_reaches_outcome_of_panic_tight_ext {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps prog s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s :=
  Decrypt.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      hpan hq)

private theorem tdp_reaches_outcome_of_panic {prog : Program}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s sf : State}
    (hsteps : Steps prog s sf) (hpan : sf.status = .Panicked)
    (hq : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
      x R s0 s :=
  Decrypt.reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic
      (spec := CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
      hpan hq)

theorem tdp_onPanicTight_of_cmk_panic_ext {C : Crypto} {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S uuidTryParse).1 = .error e)
    (hp : (e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R := by
  have hcond : ((x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 s') ∧
      s0.trace <+: s'.trace := by
    refine ⟨?_, hp.2⟩
    rcases hp.1 with rfl | halloc
    · exact Or.inl hm1
    · exact Or.inr halloc
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcond, hmem⟩

theorem tdp_reaches_outcome_tight_of_afterCmk_ext {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {tr0 : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator} {R : SepProp}
    {s0 s : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s) :
    reaches_outcome prog
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
        htr herc hcmk hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## 2. Contract-Backed Step Predicates & Parametric Composition -/

/-- Contract-backed `S5 + S6` seam specification on `tripleRatchetProgAtExt img.base ext`. -/
def SpqrRecvDeriveSeamExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    x.st.pqRatchetState.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    mkg.seed.length = 32 →
    tr.pqrState = x.st.pqRatchetState →
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img
      x trG tr st1 mkg draws (TokenInit img ∗ R) s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img
            x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws (TokenInit img ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e : SignalProtocolError :=
          if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
            x trG tr st1 e draws (TokenInit img ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧
            s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)

/-- Contract-backed `S7` step specification on `tripleRatchetProgAtExt img.base ext` with
`tryDecryptSpec.onPanic`. -/
def VerifyMacStepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacState A ctl img
      x trG tr st1 mks newPqrState draws R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img
            x trG tr st1 mks newPqrState draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
            x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))

/-- Contract-backed tight `ErrTail` step specification on `tripleRatchetProgAtExt img.base ext`. -/
def ErrTailTightStepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S uuidTryParse).1 = .error e →
    (x.model C S uuidTryParse).2 = st1 →
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
      x R s0 s

private def ConsumeMsgKeyStepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
      x trG tr st1 ck draws R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG',
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvState A ctl img
              x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((e ≠ .panic ∧ ∃ trG',
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
              x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           ((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

private def AesDecryptStepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptState A ctl img
      x trG tr st1 mks newPqrState draws R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
    | some pt =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img
            x trG tr st1 newPqrState pt draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))
    | none =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
            x trG tr st1 (.invalidMessage x.msgType .badCiphertext) draws R s0 s' ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R)))

private def ApplyRatchetStepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (newPqrState pt : List (BitVec 8))
    (R : SepProp) (s0 s : State),
    (x.model C S uuidTryParse).1 = .ok pt →
    (x.model C S uuidTryParse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetState A ctl img
      x trG tr st1 newPqrState pt (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img)
      x R s0 s

private theorem tdp_reaches_outcome_of_consumeMsgKey_gen
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hs4 : ConsumeMsgKeyStepExt img C A ctl S ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl S ext)
    (hs7 : VerifyMacStepExt img C A ctl S ext)
    (hs8 : AesDecryptStepExt img C A ctl S ext)
    (hs9 : ApplyRatchetStepExt img C A ctl S ext)
    (herr : ErrTailTightStepExt img C A ctl S ext)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
      x trG { tr0 with ratchet := r1 } st1 ck draws (TokenInit img ∗ R) s0 s4)
    (hL4 : (tripleRatchetProgAtExt img.base ext).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
      x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := Model.fromSessionState_ok_inv htr
  have hs4_step := hs4 x trG { tr0 with ratchet := r1 } st1 ck draws
    (TokenInit img ∗ R) s0 s4 hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      apply tdp_reaches_outcome_specTPTight_ext
      have hmodel := Model.model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Decrypt.reaches_outcome_steps hsteps4
          (herr x trG' { tr0 with ratchet := r2 } st1 e
            (TokenInit img ∗ R) s0 s4' hne hm1 hm2 herr_st)
      · exact tdp_reaches_outcome_of_panic_tight_ext hsteps4 hpan
          (tdp_onPanicTight_of_cmk_panic_ext hm1 hp hmem)
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Decrypt.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
        have hs56_step := hSeam x trG5 { tr0 with ratchet := r2 } st1 mkg
          draws R s0 s5 hQ hstk hseed32 hpqr0 hs5_state hL5
        dsimp only at hs56_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := Model.model_of_spqr_error htr herc hcmk hspqr hnp5
            let e : SignalProtocolError :=
              if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            have hne : e ≠ .panic := by subst e; cases sd <;> nofun
            apply tdp_reaches_outcome_specTPTight_ext
            subst hdraws
            exact Decrypt.reaches_outcome_steps hsteps5'
              (herr x trG5 { tr0 with ratchet := r2 } st1 e
                (TokenInit img ∗ R) s0 s5' hne hm1 hm2 herr_st)
          · exact Decrypt.reaches_outcome_steps hsteps5'
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
                hpan
                (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
                  htr herc hcmk hq))
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs56_step
          rcases hs56_step with ⟨s7, hsteps7, ⟨hs7_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · apply tdp_reaches_outcome_specTPTight_ext
            apply tdp_reaches_outcome_tight_of_afterCmk_ext htr herc hcmk
            refine Decrypt.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL5
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (TokenInit img ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := Model.model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 = .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact Decrypt.reaches_outcome_steps hsteps7'
                  (tdp_reaches_outcome_weaken_tight_ext
                    (herr x trG5 { tr0 with ratchet := r2 } st1
                      (.invalidMessage x.msgType .macFailed) (TokenInit img ∗ R) s0 s7' hne hm1 hm2 herr_st))
              · exact tdp_reaches_outcome_of_panic hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (TokenInit img ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps8'
                      (tdp_reaches_outcome_weaken_tight_ext
                        (herr x trG5 { tr0 with ratchet := r2 } st1
                          (.invalidMessage x.msgType .badCiphertext) (TokenInit img ∗ R) s0 s8' hne hm1 hm2 herr_st))
                  · exact tdp_reaches_outcome_of_panic hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := Model.model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps9
                      (hs9 x trG5 { tr0 with ratchet := r2 } st1 newPqrState pt
                        (TokenInit img ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact tdp_reaches_outcome_of_panic hsteps9 hpan hq
              · exact tdp_reaches_outcome_of_panic hsteps8 hpan hq
          · exact Decrypt.reaches_outcome_steps hsteps7
              (reaches_outcome_refl_panic
                (spec := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
                hpan
                (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
                  htr herc hcmk hq))
      · exact tdp_reaches_outcome_specTPTight_ext
          (tdp_reaches_outcome_tight_of_afterCmk_ext htr herc hcmk
            (tdp_reaches_outcome_of_panic hsteps5 hpan hq))

/-! ## 3. Callee Discharges from `Obj.Loads`, `AllocContractsX`, and `black_box` -/

private theorem localIdentityKeyOk_of_loads {img : Obj.Image} (A : RustAlloc)
    (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img) :
    LocalIdentityKeyOkExt img A ext :=
  Getters.local_identity_key_ok_ext img A ext (pkTryFrom_ok_ext img ext hloads)

private theorem remoteIdentityKeyOk_of_loads {img : Obj.Image} (A : RustAlloc)
    (ext : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.LibsignalTripleRatchet.Decrypt.RemoteIdentityKeyOkExt img A ext :=
  Getters.remote_identity_key_ok_ext img A ext (pkTryFrom_ok_ext img ext hloads)

private theorem trApplyOkX_of_allocX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    TrApplyOkX img A ext :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.trApply_ok_ext_x hA

private theorem clearUpkOkX_of_allocX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    ClearUpkOkX img A ext :=
  Glue.clear_unacknowledged_pre_key_message_ok_ext_x hA

theorem tdp_reaches_outcome_of_consumeMsgKey_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (hcmk : CmkOkX img C A ext)
    (hTrApply : TrApplyOkX img A ext)
    (hClearUpk : ClearUpkOkX img A ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl S ext)
    (hs7 : VerifyMacStepExt img C A ctl S ext)
    (herr : ErrTailTightStepExt img C A ctl S ext)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
      x trG { tr0 with ratchet := r1 } st1 ck draws (TokenInit img ∗ R) s0 s4)
    (hL4 : (tripleRatchetProgAtExt img.base ext).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)
      x R s0 s4 :=
  tdp_reaches_outcome_of_consumeMsgKey_gen (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext)
    (consumeMsgKey_ok_ext_x img C _ _ A ctl S ext hloads hC.toStage2ContractsX hcmk)
    hSeam hs7
    (aesDecrypt_ok_ext img C A ctl S ext hloads hC)
    (applyRatchet_ok_ext img C A ctl S ext hloads hC.toStage2ContractsX hTrApply hClearUpk)
    herr hseeds hQ hstk htr herc hdraws hs4_state hL4

/-! ## 4. Full `try_decrypt_with_state` Composition (`S0 → S1 → S2 → S3 → S4..S9 / ErrTail`) -/

private def S0StepExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
    s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img →
    s0.status = .Running →
    s0.spAligned = true →
    (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) →
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segLoadRatchetPC img) s0
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0)

/-- Contract-backed tight `S1` (`loadRatchet`) step specification on `tripleRatchetProgAtExt`. -/
def LoadRatchetStepTightExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetState A ctl img x R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img)
        x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s'

/-- `S1` (`loadRatchet`) tight step from `TrFromOkX img A ext`. -/
theorem loadRatchet_okT_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (htrFrom : TrFromOkX img A ext) :
    LoadRatchetStepTightExt img C A ctl S ext := by
  intro x R s0 s hS1 hcode
  have hcall :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_call_trFrom_reaches_x
      himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret,
      ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ :=
      hcall hcode
    · rw [hres] at hm_ret
      exact Decrypt.reaches_outcome_steps hsteps_ret
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.P3kR1bc.loadRatchet_after_call_error_tight
          himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segFindChainPC img) s
        (fun s' => ∃ trG,
          CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState
            A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _
        ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_after_call_ok
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

/-- Contract-backed `S2` (`findChain`) step specification on `tripleRatchetProgAtExt`. -/
def FindChainStepExt (img : Obj.Image) (A : RustAlloc) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainState A ctl img x trG tr st1 R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
    | .ok (some ck) =>
      reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img x trG tr st1 ck 0 R s0)
    | .ok none =>
      reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segDhStepPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0)
    | .error e =>
      reaches_pc (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.errTailPC img) s
        (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img x trG tr st1 e 0 R s0)

/-- Contract-backed tight `S3` (`dhStep`) step specification on `tripleRatchetProgAtExt`. -/
def DhStepTightExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepState A ctl img x trG tr st1 R s0 s →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
    | (.error e, _) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG' r1',
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailState A ctl img
              x trG' { tr with ratchet := r1' } st1 e
              (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s') ∨
         (s'.status = .Panicked ∧
           s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R))
    | (.ok ck, r1) =>
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        ((∃ trG',
            CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyState A ctl img
              x trG' { tr with ratchet := r1 } st1 ck
              (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s') ∨
         (s'.status = .Panicked ∧
           s'.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 s' ∗ R))

private theorem tdp_try_decrypt_ok_gen
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hs0 : S0StepExt img C A ctl S ext)
    (hs1 : LoadRatchetStepTightExt img C A ctl S ext)
    (hs2 : FindChainStepExt img A ctl ext)
    (hs3 : DhStepTightExt img C A ctl S ext)
    (hs4 : ConsumeMsgKeyStepExt img C A ctl S ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl S ext)
    (hs7 : VerifyMacStepExt img C A ctl S ext)
    (hs8 : AesDecryptStepExt img C A ctl S ext)
    (hs9 : ApplyRatchetStepExt img C A ctl S ext)
    (herr : ErrTailTightStepExt img C A ctl S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have hpre' := (tryDecryptSpecTPTight_pre_iff C A ctl S img x R s0).mp hpre
  rcases hpre' with ⟨hQ, hpre⟩
  obtain ⟨hseeds, hchains, hstk⟩ :=
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.seedsLen32_of_pre_P hpre
  rcases hs0 x (TokenInit img ∗ R) s0 hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Decrypt.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x (TokenInit img ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact tdp_reaches_outcome_specTPTight_ext hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Decrypt.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := hs2 x trG2 tr0 st1 (TokenInit img ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          Model.ensureReceiverChain_of_find_error hf
        have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := Model.findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          Model.decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        apply tdp_reaches_outcome_specTPTight_ext
        exact Decrypt.reaches_outcome_steps hsteps2'
          (herr x trG2 tr0 st1 e (TokenInit img ∗ R) s0 s2' hne hm1 hm2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            Model.ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (Model.decryptDraws_of_find_some x.rest htr hf).symm
          exact tdp_reaches_outcome_of_consumeMsgKey_gen hs4 hSeam hs7 hs8 hs9 herr
            hseeds hQ hstk htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(Model.fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 x trG2 tr0 st1 (TokenInit img ∗ R) s0 s3
            htr hf htr_chains hstk hs3_state hL3
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := Model.model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := Model.dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · apply tdp_reaches_outcome_specTPTight_ext
                exact Decrypt.reaches_outcome_steps hsteps3'
                  (herr x trG3 { tr0 with ratchet := r1' } st1 e
                    (TokenInit img ∗ R) s0 s3' hne hm1 hm2 herr_st)
              · exact tdp_reaches_outcome_specTPTight_ext
                  (tdp_reaches_outcome_of_panic_tight_ext hsteps3' hpan hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [Model.ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact tdp_reaches_outcome_of_consumeMsgKey_gen hs4 hSeam hs7 hs8 hs9 herr
                  hseeds hQ hstk htr herc rfl hs4_state hL4
              · exact tdp_reaches_outcome_specTPTight_ext
                  (tdp_reaches_outcome_of_panic_tight_ext hsteps4 hpan hq)

theorem tdp_try_decrypt_ok_of_seamW_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (h_bb : HookSat ext blackBoxName CliExt.blackBoxSpec)
    (hcmk : CmkOkX img C A ext)
    (hs1 : LoadRatchetStepTightExt img C A ctl S ext)
    (hs2 : FindChainStepExt img A ctl ext)
    (hs3 : DhStepTightExt img C A ctl S ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl S ext)
    (hs7 : VerifyMacStepExt img C A ctl S ext)
    (herr : ErrTailTightStepExt img C A ctl S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  tdp_try_decrypt_ok_gen (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext)
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P_x_ext (C := C) (ctl := ctl) (S := S)
      hloads (localIdentityKeyOk_of_loads A ext hloads)
      (remoteIdentityKeyOk_of_loads A ext hloads)
      (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok_x_ext
        img.base A ext h_bb))
    hs1 hs2 hs3
    (consumeMsgKey_ok_ext_x img C _ _ A ctl S ext hloads hC.toStage2ContractsX hcmk)
    hSeam hs7
    (aesDecrypt_ok_ext img C A ctl S ext hloads hC)
    (applyRatchet_ok_ext img C A ctl S ext hloads hC.toStage2ContractsX
      (trApplyOkX_of_allocX hC.toAllocContractsX)
      (clearUpkOkX_of_allocX hC.toAllocContractsX))
    herr

private theorem tdp_try_decrypt_ok_of_seamW
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hcallees : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpecTight img C A ctl uuidTryParse S abs)
    (hs2 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainSpec img C A ctl abs)
    (hs3 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpecTight img C A ctl uuidTryParse S abs)
    (hs4 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeySpec img C A ctl uuidTryParse S abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs)
    (hs7 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacSpec img C A ctl uuidTryParse S abs)
    (hs8 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptSpec img C A ctl uuidTryParse S abs)
    (hs9 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetSpec img C A ctl uuidTryParse S abs)
    (herr : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecTight img C A ctl uuidTryParse S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  tdp_try_decrypt_ok_gen (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := tripleRatchetExterns C ctl abs)
    (CryptoVerification.Cli.E2E.Pqxdh.WireEntries.s0_ok_P (S := S) hloads hcallees.localIk hcallees.remoteIk)
    (hs1 hloads hcallees.trFrom)
    (hs2 hloads hcallees.findReceiverChainKey)
    (fun x trG tr st1 R s0 s htr hf hlen hstk hst hL => by
      have h := hs3 hloads hhooks hcallees.createChain hcallees.derivePk
        hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
        x trG tr st1 R s0 s htr hf hlen hstk hst hL
      dsimp only at h
      rcases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with ⟨_ | _, _⟩ <;>
        (rw [hdh] at h; exact h))
    (hs4 hloads hhooks hcallees.cmk)
    (fun x trG tr st1 mkg draws R s0 s hQ hstk hseed hpqr hst hL => by
      have h := hSeam hloads hhooks hRecv hGK x trG tr st1 mkg draws R s0 s hQ hstk hseed hpqr hst hL
      rcases hsr : S.recv tr.pqrState x.msg.pqRatchet with _ | ⟨_, _⟩ <;>
        (rw [hsr] at h; exact h))
    (hs7 hloads hhooks hcallees.verifyMac)
    (hs8 hloads hhooks)
    (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk)
    (herr hloads hhooks hcallees.dropChain)

/-! ## 5. Top-Level `fnAddr`, SPQR V1, `CliExternsOk`, and Fixed-Table Corollaries -/

/-- Parametric-`S` tight-`onPanic`, weak-`pre` (`DistinctSid`) `try_decrypt_with_state` theorem
at `tripleRatchetProgAtExt img.base ext` / `fnAddr`. -/
theorem tryDecryptTPTight_run_of_seamW_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (h_bb : HookSat ext blackBoxName CliExt.blackBoxSpec)
    (hTrFrom : TrFromOkX img A ext)
    (hcmk : CmkOkX img C A ext)
    (hs2 : FindChainStepExt img A ctl ext)
    (hs3 : DhStepTightExt img C A ctl S ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl S ext)
    (hs7 : VerifyMacStepExt img C A ctl S ext)
    (herr : ErrTailTightStepExt img C A ctl S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr
    (ext := ext) hloads]
  exact tdp_try_decrypt_ok_of_seamW_ext hloads hC h_bb hcmk
    (loadRatchet_okT_ext_x hloads hTrFrom) hs2 hs3 hSeam hs7 herr

/-- **SPQR V1 (`Stage2ContractsExt`):** `try_decrypt_with_state::<signal_session_ratchet::Coins>`
meets `tryDecryptSpecTPTight` at `S := spqrV1 C.F K` on `tripleRatchetProgAtExt img.base ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsExt img C A ext)
    (h_bb : HookSat ext blackBoxName CliExt.blackBoxSpec)
    (hTrFrom : TrFromOkX img A ext)
    (hcmk : CmkOkX img C A ext)
    (hs2 : FindChainStepExt img A ctl ext)
    (hs3 : DhStepTightExt img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext)
    (hSeam : SpqrRecvDeriveSeamExt img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext)
    (hs7 : VerifyMacStepExt img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext)
    (herr : ErrTailTightStepExt img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  tryDecryptTPTight_run_of_seamW_ext C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext img
    hloads hC h_bb hTrFrom hcmk hs2 hs3 hSeam hs7 herr

/-- **SPQR V1 (`CliExternsOk`):** `tryDecryptV1_ok_PTight_ext` specialized to `cliExternsWith ext`
under `CliExternsOk P A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_cli_ext
    {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hTrFrom : TrFromOkX img A (cliExternsWith ext))
    (hcmk : CmkOkX img P.C A (cliExternsWith ext))
    (hs2 : FindChainStepExt img A ctl (cliExternsWith ext))
    (hs3 : DhStepTightExt img P.C A ctl (E2E.pqxdhSpqrModel P) (cliExternsWith ext))
    (hSeam : SpqrRecvDeriveSeamExt img P.C A ctl (E2E.pqxdhSpqrModel P) (cliExternsWith ext))
    (hs7 : VerifyMacStepExt img P.C A ctl (E2E.pqxdhSpqrModel P) (cliExternsWith ext))
    (herr : ErrTailTightStepExt img P.C A ctl (E2E.pqxdhSpqrModel P) (cliExternsWith ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A ctl uuidTryParse
        (E2E.pqxdhSpqrModel P) img) :=
  CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_ext
    P.C A ctl P.Q.K (cliExternsWith ext) img hloads
    (Stage2ContractsExt.of_externsOk hOk img)
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hookSat_blackBox32_of_externsOk_on
      hOk (CryptoVerification.SignalSession.Cli.Slots.AgreeOnCliHooks.cliExternsWith ext))
    hTrFrom hcmk hs2 hs3 hSeam hs7 herr

/-- Parametric-`S` tight-`onPanic`, weak-`pre` (`DistinctSid`) `try_decrypt_with_state` kit theorem
at `tripleRatchetProgAt` / `fnAddr`. -/
theorem tryDecryptTPTight_run_of_seamW (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr
    (ext := tripleRatchetExterns C ctl abs) himg]
  exact tdp_try_decrypt_ok_of_seamW himg hHooks hRecv hGK
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptAssembly.tryDecryptCallees C A ctl S abs img hHooks himg)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.loadRatchet_okT
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.findChain_ok
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_okT img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.KeyDerive.consumeMsgKey_ok img C A ctl S abs)
    hSeam
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.verifyMac_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.aesDecrypt_ok img C A ctl S abs)
    (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AuthDecrypt.applyRatchet_ok img C A ctl S abs)
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.errTail_okT

/-- `tripleRatchetProg` / `entryOf` corollary of `tryDecryptTPTight_run_of_seamW`. -/
theorem tryDecryptTPTight_prog_run_of_seamW (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRecv : SpqrRecvOkWT img C A ctl S abs)
    (hGK : GenerateKeysOkW img C A ctl abs)
    (hSeam : CryptoVerification.Cli.LibsignalSpqrV1.M4.PqRecvDeriveSpecWT img C A ctl uuidTryParse S abs) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img) := by
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg]
  have hentry := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ChainLookup.tryDecryptEntry_eq_fnAddr
    (ext := tripleRatchetExterns C ctl abs) himg
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry at hentry
  rw [hentry]
  exact tryDecryptTPTight_run_of_seamW C A ctl S abs img hHooks himg hRecv hGK hSeam

/-- SPQR V1 `try_decrypt_with_state::<signal_session_ratchet::Coins>` contract `tryDecryptSpecTPTight`
on `tripleRatchetProgAt img.base C ctl abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  tryDecryptTPTight_run_of_seamW C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (spqrRecvOkWT_of_v1 C A ctl K abs img
      (CryptoVerification.Cli.SpqrV1.Top.Recv.spqr_recv_ok C A ctl K abs img) hH hQ himg)
    (generateKeys_okW C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.pqRecvDerive_okWT img C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs)

end CryptoVerification.Cli.LibsignalSpqrV1.M4
