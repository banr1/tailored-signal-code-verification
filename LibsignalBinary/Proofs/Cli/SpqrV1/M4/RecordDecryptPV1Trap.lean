/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDecryptPV1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordCloneTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordExitTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSegmentsTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1Trap
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Drops
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.LogClosure
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordChainClone.Clone
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetState
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.VecExt
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Ext
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch

/-!
# Trap-at-RNG and CLI `try_decrypt_from_record` Region under `DistinctSid`

Proves the CLI `try_decrypt_from_record` region (`recordRegionEntry` → `recordRegionExit`) against
`recordDecryptSpecTPTight` on `trTrapProgAt img.base C abs` and on
`tripleRatchetProgAtExt img.base (cliExterns W)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalSpqrV1 (TokenInit)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Model & Outcome Bridges for Tight `onPanic` -/

private def rdpTrySpecTrap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).pre x s ∗
        TokenInit img
    post := fun x s0 sf =>
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).post x s0 sf ∗
        TokenInit img
    onPanic := CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidParse }

private theorem rdp_tryDecrypt_onPanic_entails_tight_trap {C : Crypto} {S : SpqrModel}
    {x : RecordDecryptGhost} {G₁ : SessionGhost}
    {s0 s sf : State} {F : SepProp} {sp : BitVec 64}
    (heq : x.st.version.toNat = x.msg.messageVersion.toNat)
    (htr : s.trace = s0.trace) :
    CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidTryParse
        (mkTryDecryptGhost sp x G₁) s sf ∗ F ⊢
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidTryParse x s0 sf := by
  dsimp only [CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight,
    CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hpan, hpref⟩ => ?_
  unfold allocFailedIn at hpan ⊢
  rw [htr] at hpan hpref
  refine Entails.pure_right ⟨?_, hpref⟩ (entails_anyHeap _)
  rcases hpan with hmod | halloc
  · exact Or.inl (model_panic_of_tryDecrypt_panic C S sp x G₁ heq hmod)
  · exact Or.inr halloc

private theorem rdp_grow_onPanic_entails_tight_trap {P1 : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨Or.inr halloc, hpref⟩ (entails_anyHeap _)

private theorem rdp_tryDecryptSpecTPTight_eq_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidParse S img =
      rdpTrySpecTrap C A ctl uuidParse S img := by
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
    rdpTrySpecTrap]
  congr 1
  · funext x s; ac_rfl
  · funext x s0 sf; ac_rfl

private theorem rdp_seg_of_sepWPp_JF_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 sf ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R))) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private def rdpNoPanicTrap (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

private theorem rdp_tryModel_noPanic_or_panic_trap (C : Crypto) (S : SpqrModel)
    (y : TryDecryptGhost) :
    y.model C (rdpNoPanicTrap S) uuidTryParse = y.model C S uuidTryParse ∨
      (y.model C S uuidTryParse).1 = .error .panic := by
  rcases htr : Mut.exec TripleRatchet.fromSessionState y.st with ⟨e | tr, st1⟩
  · left
    rw [(Decrypt.Model.model_of_fromSessionState_error (S := rdpNoPanicTrap S) htr).1,
      (Decrypt.Model.model_of_fromSessionState_error (S := S) htr).1]
  · rcases herc :
        Mut.exec (RatchetState.ensureReceiverChain C y.msg.senderRatchetKey (coinsOf y.rest))
          tr.ratchet with ⟨e | ck, r1⟩
    · left
      rw [Decrypt.Model.model_of_ensureReceiverChain_error (S := rdpNoPanicTrap S) htr herc,
        Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc]
    · rcases hcmk :
          Mut.exec
            (RatchetState.consumeMessageKey C.F y.msg.senderRatchetKey ck y.msg.counter y.msgType)
            r1 with ⟨e | mkg, r2⟩
      · left
        rw [Decrypt.Model.model_of_cmk_error (S := rdpNoPanicTrap S) htr herc hcmk,
          Decrypt.Model.model_of_cmk_error (S := S) htr herc hcmk]
      · have hpq : tr.pqrState = y.st.pqRatchetState :=
          (Decrypt.Model.fromSessionState_ok_inv htr).2.2.1
        cases hp : S.recvPanics y.st.pqRatchetState y.msg.pqRatchet
        · left
          have hnp : S.recvPanics tr.pqrState y.msg.pqRatchet = false := hpq ▸ hp
          have hnp' : (rdpNoPanicTrap S).recvPanics tr.pqrState y.msg.pqRatchet = false := rfl
          rcases hspqr : S.recv tr.pqrState y.msg.pqRatchet with sd | ⟨newPqrState, pqrKey⟩
          · rw [Decrypt.Model.model_of_spqr_error (S := rdpNoPanicTrap S) htr herc hcmk hspqr hnp',
              Decrypt.Model.model_of_spqr_error (S := S) htr herc hcmk hspqr hnp]
          · cases hmac :
                y.msg.verifyMacWithAddresses C.F
                  (serializeAddresses (serviceIdParse uuidTryParse) y.rem y.loc)
                  tr.remoteIdentityKey tr.localIdentityKey
                  (mkg.generateKeys C.F pqrKey).macKey
            · rw [Decrypt.Model.model_of_verifyMac_false (S := rdpNoPanicTrap S)
                  htr herc hcmk hspqr hmac hnp',
                Decrypt.Model.model_of_verifyMac_false (S := S) htr herc hcmk hspqr hmac hnp]
            · cases haes :
                  aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv y.msg.ciphertext
              · rw [Decrypt.Model.model_of_aesDec_none (S := rdpNoPanicTrap S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_none (S := S) htr herc hcmk hspqr hmac haes hnp]
              · rw [Decrypt.Model.model_of_aesDec_some (S := rdpNoPanicTrap S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_some (S := S) htr herc hcmk hspqr hmac haes hnp]
        · right
          exact Decrypt.Model.model_of_recvPanics htr herc hcmk hp

private theorem rdp_model_noPanic_or_panic_trap (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) :
    x.model C (rdpNoPanicTrap S) uuidTryParse = x.model C S uuidTryParse ∨
      (x.model C S uuidTryParse).1 = .error .panic := by
  by_cases heq : x.st.version.toNat = x.msg.messageVersion.toNat
  · rw [model_eq_of_version_eq C (rdpNoPanicTrap S) 0#64 x x.G heq]
    rcases rdp_tryModel_noPanic_or_panic_trap C S (mkTryDecryptGhost 0#64 x x.G) with h | hpan
    · left
      rw [h, ← model_eq_of_version_eq C S 0#64 x x.G heq]
    · right
      exact model_panic_of_tryDecrypt_panic C S 0#64 x x.G heq hpan
  · left
    dsimp [RecordDecryptGhost.model, SessionState.tryDecryptFromRecord, Mut.exec, StateT.run,
      ExceptT.run, ExceptT.mk, pure, Except.pure, Bind.bind, Monad.toBind, ExceptT.bind,
      ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, StateT.lift, throw, throwThe, MonadExceptOf.throw]
    simp [heq]

private theorem rdp_spec_S_exists_trap (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost) :
    ∃ S' : SpqrModel,
      x.model C S' uuidTryParse = x.model C S uuidTryParse ∧
      (∀ (s0 sf : State),
        (x.model C S' uuidTryParse).1 = .error .panic ∨
          (x.st.version.toNat = x.msg.messageVersion.toNat ∧
            S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
          allocFailedIn s0 sf →
        (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) := by
  rcases rdp_model_noPanic_or_panic_trap C S x with hmod_eq | hmod_pan
  · refine ⟨rdpNoPanicTrap S, hmod_eq, fun s0 sf h => ?_⟩
    rcases h with hp | ⟨_, hpan⟩ | halloc
    · exact Or.inl (hmod_eq ▸ hp)
    · exact nomatch hpan
    · exact Or.inr halloc
  · exact ⟨S, rfl, fun _ _ _ => Or.inl hmod_pan⟩

private theorem rdp_JState_eq_of_model_eq_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S' img x R s0 s =
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState]
  rw [hmod]

private theorem rdp_FState_eq_of_model_eq_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S' img x R s0 s =
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState]
  rw [hmod]

private theorem rdp_post_eq_of_model_eq_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S' img).post x s0 sf =
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post x s0 sf := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage]
  rw [hmod]

private theorem rdp_regionOutcome_of_tokenFrame_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse)
    (hpan_imp : ∀ (s0 sf : State),
      (x.model C S' uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
        allocFailedIn s0 sf →
      (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf)
    (hout : regionOutcome
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S' img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      x (TokenInit img ∗ R) s0 sf) :
    regionOutcome
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      x R s0 sf := by
  rcases hout with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hpost⟩
  · left
    refine ⟨hpc, hrun, hvregs, ?_⟩
    rw [rdp_post_eq_of_model_eq_trap hmod] at hpost
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT]
    have heq : (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗
        (TokenInit img ∗ R) =
        (TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post x s0 sf) ∗ R := by
      ac_rfl
    exact heq ▸ hpost
  · right
    refine ⟨hpan, ?_⟩
    dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage] at hpost
    dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight,
      CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight]
    have hent :
        (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
              (x.st.version.toNat = x.msg.messageVersion.toNat ∧
                S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
              allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
            anyHeap) ∗
          (TokenInit img ∗ R) ⊢
        (⌜((x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) ∧
            s0.trace <+: sf.trace⌝ ∗
          anyHeap) ∗ R := by
      have hassoc1 :
          (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
                (x.st.version.toNat = x.msg.messageVersion.toNat ∧
                  S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
                allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
              anyHeap) ∗
            (TokenInit img ∗ R) =
          (⌜((x.model C S' uuidTryParse).1 = .error .panic ∨
                (x.st.version.toNat = x.msg.messageVersion.toNat ∧
                  S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet = true) ∨
                allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
              (anyHeap ∗ TokenInit img)) ∗ R := by
        ac_rfl
      rw [hassoc1]
      refine sepConj_mono_left ?_
      refine Entails.pure_left fun ⟨hp, htr⟩ => ?_
      exact Entails.pure_right ⟨hpan_imp s0 sf hp, htr⟩ (entails_anyHeap _)
    exact Satisfies.mono hent hpost

private theorem rdp_regionOutcome_of_tokenFrame_P_trap {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse)
    (hpan_imp : ∀ (s0 sf : State),
      (x.model C S' uuidTryParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
        allocFailedIn s0 sf →
      (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf)
    (hout : regionOutcome
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S' img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      x (TokenInit img ∗ R) s0 sf) :
    regionOutcome
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      x R s0 sf :=
  rdp_regionOutcome_of_tokenFrame_trap (C := C) (A := A) (ctl := ctl) (S' := S') (S := S) (img := img)
    hmod hpan_imp hout

/-! ## 2. `SegDecrypt` (+1692) Crossing `tryDecryptSpecTPTight` under `AllocContracts` -/

attribute [local arm64_norm ↓, local wp_norm ↓]
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 1200000 in
private theorem rdp_segDecrypt_ok_alloc_TPTight {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (htry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (rdpTrySpecTrap C A ctl uuidTryParse S img))
    (hset : FromRecordCallees.SetSessionStateOkExt img.base A ext)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrow : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclosure : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfrozen, hsym, hvregs⟩,
    ⟨hrem_or_dist, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  have hentry := entryOf_eq_tripleRatchetProgAtExt ext hloads CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC at hpc
  rw [hentry] at hpc
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have htry_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (rdpTrySpecTrap C A ctl uuidTryParse S img) := by
    have h1 : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName =
        num% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact htry
  dsimp only [rdpTrySpecTrap, CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP] at htry_rel
  have hmemcpy_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
        sessionMemcpyRegionSpec :=
    hA.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
      (num% (ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal"))
      (by simp only [hfn, memcpyName, arm64_norm])
  have hset_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (setSessionStateSpec A) := by
    have h1 : libsignalSessionCode.fnOff setSessionStateName =
        num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr setSessionStateName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hset
  have hdrop_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (dropSessionStructureLocal2Spec A) := by
    have h1 : libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name =
        num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") :=
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hdrop
  have hclosure_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        ((logClosureSpec img).inImage img) := by
    have h1 : libsignalSessionCode.fnOff
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName =
        num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") :=
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.logClosureName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hclosure
  have hgrow_rel :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
          bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
            (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
        (growOneSpeSpec A) := by
    have h1 : libsignalSessionCode.fnOff growOneSpeName =
        num% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") :=
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")
    have h2 : (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName +
        bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")) =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn, h1]
      bv_omega
    rw [h2]
    exact hgrow
  have hFPC : CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 2128#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recFPC
    rw [hentry]
  have hJPC : CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC img =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 7820#64 := by
    unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recJPC
    rw [hentry]
  have hlog1732 : logOff img =
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) -
          page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1732))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.logOff_eq_at_1732
      hloads (by rw [Program.fnAddr_rebase, hfn])
  have hlog1732' :
      (((((libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1732#64 &&&
        bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 -
          page% (ls_off% "libsignal_cli_ratchet::decrypt_signal" + 1732))) ↦₆₄ 0#64) : SepProp) ⊢
        logOff img := by
    rw [hlog1732]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 1692 64
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 1984 36
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 5948 156
  segDecrypt_rec_fetches_cli img.base (Rust.withPanics ext) hfn 7812 8
  change s.pc = (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 1692#64 at hpc
  clear hentry hfn htry hset hdrop hgrow hclosure hloads
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry
  examples_hide_fetches
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFrame at hmem
  simp only [← sepConj_assoc] at hmem
  have hF0 : FrozenInv img s := ⟨hfrozen, hsym⟩
  apply rdp_seg_of_sepWPp_JF_trap hmem hL
    (target := decryptTarget entry ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_frozen hF0
    (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
      (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) (entry + bv% (1720)) |>.setPC
      (entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") -
        (ls_off% "libsignal_cli_ratchet::decrypt_signal")))).sp.toNat := hsp_bound
  segDecrypt_wpp_call_frozen_cli htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (rdp_tryDecrypt_onPanic_entails_tight_trap heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_frozen hF_sf
        (mid := entry + bv% (2 ^ 64 + (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_ratchet::Coins>::{closure#0}") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen_cli hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_frozen hF_sf_1
        (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_frozen_cli hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (rdp_grow_onPanic_entails_tight_trap (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
          C img.base s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4 hmf
      right
      refine ⟨by rw [hFPC]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4.1, hF4.2,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_frozen hF_sf
        (mid := entry + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") -
          (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_frozen_cli hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_frozen hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
          C img.base s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3.1, hF3.2,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFrame
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_frozen hF_sf
      (mid := entry + bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp, hlog1732]
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_frozen_cli hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_frozen hF_sf_1
      (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") -
        (ls_off% "libsignal_cli_ratchet::decrypt_signal")))
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_frozen_cli hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_frozen hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre hlog1732' (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.tapeAfter_tryDecrypt_entails
        C img.base s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by rw [hJPC]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4.1, hF4.2,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFrame
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

/-! ## 3. Record Callees & Region Assembly on `trTrapProgAt` -/

private theorem rdp_region_reachesTPTight_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img →
      s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).pre x s0 ∗ R) →
      region_reaches (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s0 := by
  have hA : AllocContracts img.base A (trTrapExterns C abs) :=
    AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hHooks.alloc
  have hchainClone :=
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.chain_clone_ok_ext hA
  have hsenderClone :=
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.senderChain_clone_ok_ext hA
  have hdropLocal2 :=
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_ok_ext hA
      (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_ext hA)
  have hsetState :=
    FromRecordCallees.set_session_state_ok_ext hA
      (FromRecordCallees.drop_session_structure_local1_ok_ext hA
        (Getters.drop_vec_message_key_ok_ext hA)
        (Getters.drop_vec_chain_ok_ext hA))
  have hgrowSpe := FromRecordCallees.grow_one_spe_ok_ext (finish_grow_ok_ext hA)
  have hclosure :=
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.log_closure_ok_ext
      (ext := trTrapExterns C abs) himg
  have htd := hTry
  rw [rdp_tryDecryptSpecTPTight_eq_trap] at htd
  intro x R s0 hpc hst hpre hL
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists_trap C S x
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S' img).pre x s0 ∗
      (TokenInit img ∗ R) := by
    change s0.mem ⊨
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗
      (TokenInit img ∗ R)
    have heq :
        (TokenInit img ∗
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0) ∗ R =
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗
          (TokenInit img ∗ R) := by ac_rfl
    exact heq ▸ hpre
  have hstk := CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPre_P hpre'
  have hJ : ∀ s,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s →
      region_reaches (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    rw [← rdp_JState_eq_of_model_eq_trap hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_ok_alloc (C := C) (ctl := ctl) (S := S') himg hA x (TokenInit img ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_trap hmod hpan_imp hout⟩
  have hF : ∀ s,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s →
      region_reaches (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    rw [← rdp_FState_eq_of_model_eq_trap hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_ok_alloc (C := C) (ctl := ctl) (S := S') himg hA hdropLocal2
        x (TokenInit img ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · rw [rdp_JState_eq_of_model_eq_trap hmod] at hj
      exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_trap hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    segClone_ok_alloc_P (C := C) (ctl := ctl) (S := S')
      himg hA hchainClone hsenderClone x (TokenInit img ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ :=
      rdp_segDecrypt_ok_alloc_TPTight himg hA htd
        hsetState hdropLocal2 hgrowSpe hclosure x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ :=
      segMismatch_ok_alloc (C := C) (ctl := ctl) (S := S') himg
        hgrowSpe hclosure x G₁ (TokenInit img ∗ R) s0 s' hm (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · rw [rdp_FState_eq_of_model_eq_trap hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame_trap hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_P_trap hmod hpan_imp hout⟩

/-! ## 4. Top `_trap` and `_cli` Theorems -/

/-- Parametric-`S` `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`trTrapProgAt img.base C abs`. -/
theorem recordDecrypt_region_okTPTight_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  Record.region_ok_of_reaches (rdp_region_reachesTPTight_trap C A ctl S abs img hHooks himg hTry)

/-- `recordDecrypt_region_okTPTight_trap` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem recordDecrypt_region_vregs_okTPTight_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reachesTPTight_trap C A ctl S abs img hHooks himg hTry x R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- SPQR V1 `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`trTrapProgAt img.base C abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  recordDecrypt_region_okTPTight_trap C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_trap C A ctl K abs img hH hQ himg)

/-- `recordDecryptV1_region_ok_PTight_trap` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img).withVRegs :=
  recordDecrypt_region_vregs_okTPTight_trap C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight_trap C A ctl K abs img hH hQ himg)

/-- CLI corollary of `recordDecryptV1_region_ok_PTight_trap` over arbitrary `RustAlloc` / `MlKem`
hooks on `cliExterns W`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_cli_of_hooks
    (W : CryptoVerification.SignalSession.CliHooks) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (img : Obj.Image)
    (hH : TripleRatchetHooks W.C A (LibsignalSpqrV1.spqrV1 W.C.F K)
      (CryptoVerification.SignalSession.cliExterns W))
    (hQ : LibsignalSpqrV1.SpqrHooks W.C A K
      (CryptoVerification.SignalSession.cliExterns W))
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight W.C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F K) img) :=
  CryptoVerification.LibsignalTripleRatchet.region_ok_of_trapsOnly
    (CryptoVerification.SignalSession.Cli.Slots.trapsOnly_trTrap_cli img.base W)
    (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_trap
      W.C A ctl K (CryptoVerification.SignalSession.cliExterns W) img hH hQ himg)

/-- CLI corollary of `recordDecryptV1_region_ok_PTight_trap` discharged with
`cliExterns_tripleRatchetHooks` and `cliExterns_spqrHooks`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img) :=
  CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_cli_of_hooks
    W CryptoVerification.E2E.HooksE.A0 ctl W.Q.K img
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_tripleRatchetHooks W
      (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_spqrHooks W)
    himg

/-- CLI corollary of `recordDecryptV1_region_vregs_ok_PTight_trap` over arbitrary `RustAlloc` / `MlKem`
hooks on `cliExterns W`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_cli_of_hooks
    (W : CryptoVerification.SignalSession.CliHooks) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (img : Obj.Image)
    (hH : TripleRatchetHooks W.C A (LibsignalSpqrV1.spqrV1 W.C.F K)
      (CryptoVerification.SignalSession.cliExterns W))
    (hQ : LibsignalSpqrV1.SpqrHooks W.C A K
      (CryptoVerification.SignalSession.cliExterns W))
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight W.C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F K) img).withVRegs :=
  CryptoVerification.LibsignalTripleRatchet.region_ok_of_trapsOnly
    (CryptoVerification.SignalSession.Cli.Slots.trapsOnly_trTrap_cli img.base W)
    (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_trap
      W.C A ctl K (CryptoVerification.SignalSession.cliExterns W) img hH hQ himg)

/-- CLI corollary of `recordDecryptV1_region_vregs_ok_PTight_trap` discharged with
`cliExterns_tripleRatchetHooks` and `cliExterns_spqrHooks`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_cli
    (W : CryptoVerification.SignalSession.CliHooks) (ctl : BitVec 64) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAtExt img.base (CryptoVerification.SignalSession.cliExterns W))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight W.C
        CryptoVerification.E2E.HooksE.A0 ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) img).withVRegs :=
  CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_cli_of_hooks
    W CryptoVerification.E2E.HooksE.A0 ctl W.Q.K img
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_tripleRatchetHooks W
      (LibsignalSpqrV1.spqrV1 W.C.F W.Q.K))
    (CryptoVerification.SignalSession.Cli.Slots.cliExterns_spqrHooks W)
    himg

end CryptoVerification.Cli.LibsignalSpqrV1.M4
