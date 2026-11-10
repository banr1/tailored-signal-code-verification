/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DefsP
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ChainClone4KExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordCloneExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropChainExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordDropVecExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordExitTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSegDecryptExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSegmentsTrap
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordSetStateExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.TryDecryptPV1
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.LogClosure
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel

/-!
# CLI `try_decrypt_from_record` Region under `DistinctSid` and Tight `onPanic`

Proves the CLI `try_decrypt_from_record` region (`recordRegionEntry` → `recordRegionExit`)
against `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight` (weak `remote ≠ local ∨ DistinctSid`
precondition and tight `recordDecryptOnPanicTight` panic condition):
- `CryptoVerification.Cli.LibsignalSpqrV1.M4.recordDecrypt_region_okTPTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.M4.recordDecrypt_region_vregs_okTPTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight`
- `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.SignalSession (CliExternsOk cliExternsWith)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Tight `onPanic` Record Spec & Weakening Helpers -/

/-- Tight panic condition for `try_decrypt_from_record`: the model panics or an allocation failed,
and the trace only grew (dropping the `(version check ∧ S.recvPanics …)` disjunct). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight
    (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : RecordDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜((x.model C S uuidParse).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
    anyHeap

/-- `recordDecryptSpecT` with `recordDecryptSpecP`'s weak `pre` (`remote ≠ local ∨ DistinctSid`)
and the tight panic condition `recordDecryptOnPanicTight`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec RecordDecryptGhost :=
  { CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidParse S img).pre x s
    onPanic := CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S uuidParse }

/-- `recordDecryptOnPanicTight` implies `(recordDecryptSpecT ...).onPanic`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight_weaken
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost}
    {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT C A ctl parse S img).onPanic x s0 sf ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT,
    CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inr ha)

/-! ## 2. Model & Outcome Bridges for Tight `onPanic` -/

private def rdpTrySpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
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

private theorem rdp_tryDecrypt_onPanic_entails_tight {C : Crypto} {S : SpqrModel}
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

private theorem rdp_grow_onPanic_entails_tight {P1 : Prop} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜(P1 ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨Or.inr halloc, hpref⟩ (entails_anyHeap _)

private theorem rdp_tryDecryptSpecTPTight_eq (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidParse S img =
      rdpTrySpec C A ctl uuidParse S img := by
  dsimp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight,
    rdpTrySpec]
  congr 1
  · funext x s; ac_rfl
  · funext x s0 sf; ac_rfl

private def rdpNoPanic (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

private theorem rdp_tryModel_noPanic_or_panic (C : Crypto) (S : SpqrModel)
    (y : TryDecryptGhost) :
    y.model C (rdpNoPanic S) uuidTryParse = y.model C S uuidTryParse ∨
      (y.model C S uuidTryParse).1 = .error .panic := by
  rcases htr : Mut.exec TripleRatchet.fromSessionState y.st with ⟨e | tr, st1⟩
  · left
    rw [(Decrypt.Model.model_of_fromSessionState_error (S := rdpNoPanic S) htr).1,
      (Decrypt.Model.model_of_fromSessionState_error (S := S) htr).1]
  · rcases herc :
        Mut.exec (RatchetState.ensureReceiverChain C y.msg.senderRatchetKey (coinsOf y.rest))
          tr.ratchet with ⟨e | ck, r1⟩
    · left
      rw [Decrypt.Model.model_of_ensureReceiverChain_error (S := rdpNoPanic S) htr herc,
        Decrypt.Model.model_of_ensureReceiverChain_error (S := S) htr herc]
    · rcases hcmk :
          Mut.exec
            (RatchetState.consumeMessageKey C.F y.msg.senderRatchetKey ck y.msg.counter y.msgType)
            r1 with ⟨e | mkg, r2⟩
      · left
        rw [Decrypt.Model.model_of_cmk_error (S := rdpNoPanic S) htr herc hcmk,
          Decrypt.Model.model_of_cmk_error (S := S) htr herc hcmk]
      · have hpq : tr.pqrState = y.st.pqRatchetState :=
          (Decrypt.Model.fromSessionState_ok_inv htr).2.2.1
        cases hp : S.recvPanics y.st.pqRatchetState y.msg.pqRatchet
        · left
          have hnp : S.recvPanics tr.pqrState y.msg.pqRatchet = false := hpq ▸ hp
          have hnp' : (rdpNoPanic S).recvPanics tr.pqrState y.msg.pqRatchet = false := rfl
          rcases hspqr : S.recv tr.pqrState y.msg.pqRatchet with sd | ⟨newPqrState, pqrKey⟩
          · rw [Decrypt.Model.model_of_spqr_error (S := rdpNoPanic S) htr herc hcmk hspqr hnp',
              Decrypt.Model.model_of_spqr_error (S := S) htr herc hcmk hspqr hnp]
          · cases hmac :
                y.msg.verifyMacWithAddresses C.F
                  (serializeAddresses (serviceIdParse uuidTryParse) y.rem y.loc)
                  tr.remoteIdentityKey tr.localIdentityKey
                  (mkg.generateKeys C.F pqrKey).macKey
            · rw [Decrypt.Model.model_of_verifyMac_false (S := rdpNoPanic S)
                  htr herc hcmk hspqr hmac hnp',
                Decrypt.Model.model_of_verifyMac_false (S := S) htr herc hcmk hspqr hmac hnp]
            · cases haes :
                  aesCbcDecrypt C.D (mkg.generateKeys C.F pqrKey).cipherKey
                    (mkg.generateKeys C.F pqrKey).iv y.msg.ciphertext
              · rw [Decrypt.Model.model_of_aesDec_none (S := rdpNoPanic S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_none (S := S) htr herc hcmk hspqr hmac haes hnp]
              · rw [Decrypt.Model.model_of_aesDec_some (S := rdpNoPanic S)
                    htr herc hcmk hspqr hmac haes hnp',
                  Decrypt.Model.model_of_aesDec_some (S := S) htr herc hcmk hspqr hmac haes hnp]
        · right
          exact Decrypt.Model.model_of_recvPanics htr herc hcmk hp

private theorem rdp_model_noPanic_or_panic (C : Crypto) (S : SpqrModel)
    (x : RecordDecryptGhost) :
    x.model C (rdpNoPanic S) uuidTryParse = x.model C S uuidTryParse ∨
      (x.model C S uuidTryParse).1 = .error .panic := by
  by_cases heq : x.st.version.toNat = x.msg.messageVersion.toNat
  · rw [model_eq_of_version_eq C (rdpNoPanic S) 0#64 x x.G heq]
    rcases rdp_tryModel_noPanic_or_panic C S (mkTryDecryptGhost 0#64 x x.G) with h | hpan
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

private theorem rdp_spec_S_exists (C : Crypto) (S : SpqrModel) (x : RecordDecryptGhost) :
    ∃ S' : SpqrModel,
      x.model C S' uuidTryParse = x.model C S uuidTryParse ∧
      (∀ (s0 sf : State),
        (x.model C S' uuidTryParse).1 = .error .panic ∨
          (x.st.version.toNat = x.msg.messageVersion.toNat ∧
            S'.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∨
          allocFailedIn s0 sf →
        (x.model C S uuidTryParse).1 = .error .panic ∨ allocFailedIn s0 sf) := by
  rcases rdp_model_noPanic_or_panic C S x with hmod_eq | hmod_pan
  · refine ⟨rdpNoPanic S, hmod_eq, fun s0 sf h => ?_⟩
    rcases h with hp | ⟨_, hpan⟩ | halloc
    · exact Or.inl (hmod_eq ▸ hp)
    · exact nomatch hpan
    · exact Or.inr halloc
  · exact ⟨S, rfl, fun _ _ _ => Or.inl hmod_pan⟩

private theorem rdp_JState_eq_of_model_eq {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S' img x R s0 s =
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x R s0 s := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState]
  rw [hmod]

private theorem rdp_FState_eq_of_model_eq {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S' img x R s0 s =
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x R s0 s := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState]
  rw [hmod]

private theorem rdp_post_eq_of_model_eq {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S' S : SpqrModel} {img : Obj.Image} {x : RecordDecryptGhost} {s0 sf : State}
    (hmod : x.model C S' uuidTryParse = x.model C S uuidTryParse) :
    (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S' img).post x s0 sf =
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).post x s0 sf := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec, Spec.inImage]
  rw [hmod]

private theorem rdp_regionOutcome_of_tokenFrame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
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
    rw [rdp_post_eq_of_model_eq hmod] at hpost
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

private theorem rdp_regionOutcome_of_tokenFrame_P {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
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
  rdp_regionOutcome_of_tokenFrame (C := C) (A := A) (ctl := ctl) (S' := S') (S := S) (img := img)
    hmod hpan_imp hout

/-! ## 3. `SegDecrypt` (+1692) Crossing `tryDecryptSpecTPTight` (`ext`-Generic) -/

private theorem rdp_segDecrypt_ok_ext_TPTight {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (htry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (rdpTrySpec C A ctl uuidTryParse S img))
    (hset : FromRecordCallees.SetSessionStateOkExt img.base A ext)
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrow : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclosure : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.LogClosureOkExt img ext)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
        regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
          (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') :=
  rdp_segDecrypt_ok_4k
    (tok := TokenInit img)
    (tryOnPanic := CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidTryParse)
    (recSpec := CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
    hloads
    (subroutine_ok_withStack_of_subroutine_ok hhooks.session_memcpy_region allocHookStack)
    htry hset hdrop hgrow hclosure x G₁ R s0 s hQ
    (fun _ _ _ _ heq htr => rdp_tryDecrypt_onPanic_entails_tight heq htr)
    (fun _ _ _ htr => rdp_grow_onPanic_entails_tight htr)
    hV hsp_bound hL

/-! ## 4. Contract-Backed Record Region Assembly on `tripleRatchetProgAtExt` -/

/-- Entry-to-branch (`SegClone`, `recordRegionEntry → recVPC / recMPC / panic`) contract on
`tripleRatchetProgAtExt img.base ext` under `recordDecryptSpecP`. -/
abbrev SegCloneOkPExt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) : Prop :=
  ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
    s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img →
    s0.status = .Running →
    (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R) →
    (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem →
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
      ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ R s0 s') ∨
       (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
       regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img)
         (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')

/-- Region assembly for `try_decrypt_from_record` under `recordDecryptSpecTPTight` on
`tripleRatchetProgAtExt img.base ext` from 4K allocator/callee contracts. -/
theorem rdp_region_reachesTPTight_of_callees_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName) (rustAllocSpec A))
    (hdropLocal2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrowSpe : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclone : ∀ S' : SpqrModel, SegCloneOkPExt img C A ctl S' ext)
    (hsegDecrypt : ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
            (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')) :
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img →
      s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).pre x s0 ∗ R) →
      region_reaches (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s0 := by
  have hclosure :=
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.log_closure_ok_ext
      (ext := ext) himg
  intro x R s0 hpc hst hpre hL
  obtain ⟨S', hmod, hpan_imp⟩ := rdp_spec_S_exists C S x
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
      region_reaches (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    rw [← rdp_JState_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hout⟩ :=
      segExit_ok_dealloc (C := C) (ctl := ctl) (S := S') himg hdealloc_fn x (TokenInit img ∗ R) s0 s hs hLs
    exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame hmod hpan_imp hout⟩
  have hF : ∀ s,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s →
      region_reaches (tripleRatchetProgAtExt img.base ext)
        (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
        (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s := by
    intro s hs hLs
    rw [← rdp_FState_eq_of_model_eq hmod] at hs
    obtain ⟨s', hst', hnext⟩ :=
      segTail_ok_alloc_shim (C := C) (ctl := ctl) (S := S') himg hshim_fn halloc_fn hdropLocal2
        x (TokenInit img ∗ R) s0 s hs hLs
    rcases hnext with hj | hout
    · rw [rdp_JState_eq_of_model_eq hmod] at hj
      exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame hmod hpan_imp hout⟩
  obtain ⟨s', hst', hnext⟩ :=
    hclone S' x (TokenInit img ∗ R) s0 hpc hst hpre' hL
  rcases hnext with ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout
  · obtain ⟨s'', hst'', hnext'⟩ :=
      hsegDecrypt x G₁ R s0 s' hQ hv hstk (hst'.codeLoaded hL)
    rcases hnext' with hj | hf | hout
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hnext'⟩ :=
      segMismatch_ok_alloc (C := C) (ctl := ctl) (S := S') himg
        hgrowSpe hclosure x G₁ (TokenInit img ∗ R) s0 s' hm (hst'.codeLoaded hL)
    rcases hnext' with hf | hout
    · rw [rdp_FState_eq_of_model_eq hmod] at hf
      exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', rdp_regionOutcome_of_tokenFrame hmod hpan_imp hout⟩
  · exact ⟨s', hst', rdp_regionOutcome_of_tokenFrame_P hmod hpan_imp hout⟩

/-- `region_ok` wrapper around `rdp_region_reachesTPTight_of_callees_ext`. -/
theorem recordDecrypt_region_okTPTight_of_callees_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName) (rustAllocSpec A))
    (hdropLocal2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrowSpe : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclone : ∀ S' : SpqrModel, SegCloneOkPExt img C A ctl S' ext)
    (hsegDecrypt : ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
            (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  Record.region_ok_of_reaches
    (rdp_region_reachesTPTight_of_callees_ext C A ctl S ext img himg
      hdealloc_fn hshim_fn halloc_fn hdropLocal2 hgrowSpe hclone hsegDecrypt)

/-- `Spec.withVRegs` wrapper around `rdp_region_reachesTPTight_of_callees_ext`. -/
theorem recordDecrypt_region_vregs_okTPTight_of_callees_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName) (rustAllocSpec A))
    (hdropLocal2 : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A ext)
    (hgrowSpe : FromRecordCallees.GrowOneSpeOkExt img.base A ext)
    (hclone : ∀ S' : SpqrModel, SegCloneOkPExt img C A ctl S' ext)
    (hsegDecrypt : ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
            (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s')) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    rdp_region_reachesTPTight_of_callees_ext C A ctl S ext img himg
      hdealloc_fn hshim_fn halloc_fn hdropLocal2 hgrowSpe hclone hsegDecrypt
      x R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## 5. 4K Callee Instantiations & Generalized Top Region Theorems -/

/-- Discharge `DropSessionStructureLocal2OkExt b A ext` from `AllocContracts4K b A ext`
(using only `hA.dealloc`). -/
theorem drop_session_structure_local2_ok_4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      b A ext :=
  drop_session_structure_local2_ok_dealloc hA.dealloc
    (drop_proto_chain_ok_dealloc hA.dealloc)
    (drop_chain_ok_dealloc hA.dealloc)

/-- Discharge `DropSessionStructureLocal2OkExt b A (cliExternsWith ext)` directly from
`CliExternsOk P A ext`. -/
theorem drop_session_structure_local2_cli_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
      b A (cliExternsWith ext) :=
  drop_session_structure_local2_ok_4k (AllocContracts4K.of_externsOk hOk b)

/-- Discharge `SetSessionStateOkExt b A ext` from `AllocContracts4K b A ext`. -/
theorem set_session_state_ok_alloc4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    FromRecordCallees.SetSessionStateOkExt b A ext :=
  set_session_state_ok_4k
    (hA.session_memcpy_region allocHookStack (by decide) (by decide))
    (drop_session_structure_local1_ok_dealloc hA.dealloc
      (drop_vec_message_key_ok_dealloc hA.dealloc)
      (drop_vec_chain_ok_dealloc hA.dealloc))

/-- Discharge `GrowOneSpeOkExt b A ext` from `AllocContracts4K b A ext`. -/
theorem grow_one_spe_ok_alloc4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    FromRecordCallees.GrowOneSpeOkExt b A ext :=
  grow_one_spe_ok_4k hA.shim hA.alloc hA.realloc

/-- `SegDecrypt` (+1692) instantiated at `TokenInit img` and `recordDecryptSpecTPTight`
from `AllocContracts4K img.base A ext` and `tryDecryptSpecTPTight`. -/
theorem rdp_segDecrypt_ok_4k_TPTight {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    ∀ (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      x.st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ (TokenInit img ∗ R) s0 s →
      rootStack ≤ s0.sp.toNat →
      (tripleRatchetProgAtExt img.base ext).CodeLoaded s.mem →
      ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s s' ∧
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.JState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.FState C A ctl uuidTryParse S img x (TokenInit img ∗ R) s0 s' ∨
          regionOutcome (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img)
            (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  have hTry' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (rdpTrySpecParam C A ctl uuidTryParse S img (TokenInit img)
        (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight C S uuidTryParse)) := by
    change subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (rdpTrySpec C A ctl uuidTryParse S img)
    rwa [← rdp_tryDecryptSpecTPTight_eq]
  intro x G₁ R s0 s hQ hV hstk hL
  exact rdp_segDecrypt_ok_4k himg
    (hA.session_memcpy_region allocHookStack (by decide) (by decide))
    hTry'
    (set_session_state_ok_alloc4k hA)
    (drop_session_structure_local2_ok_4k hA)
    (grow_one_spe_ok_alloc4k hA)
    (CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.log_closure_ok_ext (ext := ext) himg)
    x G₁ R s0 s hQ
    (fun _ _ _ _ heq htr => rdp_tryDecrypt_onPanic_entails_tight heq htr)
    (fun _ _ _ htr => rdp_grow_onPanic_entails_tight htr)
    hV hstk hL

/-- Discharge `SegCloneOkPExt img C A ctl S ext` unconditionally from `AllocContracts4K img.base A ext`
via `segClone_ok_4k_P`, `chain_clone_ok_4k_ext`, and `senderChain_clone_ok_4k_ext`. -/
theorem segClone_ok_alloc4k {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts4K img.base A ext) :
    SegCloneOkPExt img C A ctl S ext :=
  segClone_ok_4k_P himg hA.shim hA.alloc
    (hA.session_memcpy_region allocHookStack (by decide) (by decide))
    (chain_clone_ok_4k_ext hA)
    (senderChain_clone_ok_4k_ext hA)

/-- Parametric-`S` `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`tripleRatchetProgAtExt img.base ext` from `AllocContracts4K` and `tryDecryptSpecTPTight`. -/
theorem recordDecrypt_region_okTPTight_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts4K img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  recordDecrypt_region_okTPTight_of_callees_ext C A ctl S ext img himg
    hA.dealloc hA.shim hA.alloc
    (drop_session_structure_local2_ok_4k hA)
    (grow_one_spe_ok_alloc4k hA)
    (fun _ => segClone_ok_alloc4k himg hA)
    (rdp_segDecrypt_ok_4k_TPTight himg hA hTry)

/-- `recordDecrypt_region_okTPTight_ext` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem recordDecrypt_region_vregs_okTPTight_ext (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts4K img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs :=
  recordDecrypt_region_vregs_okTPTight_of_callees_ext C A ctl S ext img himg
    hA.dealloc hA.shim hA.alloc
    (drop_session_structure_local2_ok_4k hA)
    (grow_one_spe_ok_alloc4k hA)
    (fun _ => segClone_ok_alloc4k himg hA)
    (rdp_segDecrypt_ok_4k_TPTight himg hA hTry)

/-- SPQR V1 `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`tripleRatchetProgAtExt img.base ext` under `AllocContracts4K`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts4K img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  recordDecrypt_region_okTPTight_ext C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext img
    hA himg hTry

/-- Specialization of `recordDecryptV1_region_ok_PTight_ext` to `cliExternsWith ext` under
`CliExternsOk P A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_cli_ext
    {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A ctl uuidTryParse
        (E2E.pqxdhSpqrModel P) img)) :
    region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A ctl uuidTryParse
        (E2E.pqxdhSpqrModel P) img) :=
  CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight_ext
    P.C A ctl P.Q.K (cliExternsWith ext) img
    (AllocContracts4K.of_externsOk hOk img.base) himg hTry

/-- `recordDecryptV1_region_ok_PTight_ext` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hA : AllocContracts4K img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img)) :
    region_ok (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img).withVRegs :=
  recordDecrypt_region_vregs_okTPTight_ext C A ctl (LibsignalSpqrV1.spqrV1 C.F K) ext img
    hA himg hTry

/-- Specialization of `recordDecryptV1_region_vregs_ok_PTight_ext` to `cliExternsWith ext` under
`CliExternsOk P A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_cli_ext
    {img : Obj.Image} {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A ctl uuidTryParse
        (E2E.pqxdhSpqrModel P) img)) :
    region_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight P.C A ctl uuidTryParse
        (E2E.pqxdhSpqrModel P) img).withVRegs :=
  CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight_ext
    P.C A ctl P.Q.K (cliExternsWith ext) img
    (AllocContracts4K.of_externsOk hOk img.base) himg hTry

/-! ## 6. Fixed-Table `tripleRatchetProgAt` Corollaries -/

/-- Parametric-`S` `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`tripleRatchetProgAt`. -/
theorem recordDecrypt_region_okTPTight (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img) :=
  recordDecrypt_region_okTPTight_ext C A ctl S (tripleRatchetExterns C ctl abs) img
    (AllocContracts4K.of_AllocContracts
      (Stage2Contracts.of_tripleRatchetProgAt' (b := img.base) (ctl := ctl) hHooks).toAllocContracts)
    himg hTry

/-- `recordDecrypt_region_okTPTight` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem recordDecrypt_region_vregs_okTPTight (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTry : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl uuidTryParse S img)) :
    region_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse S img).withVRegs :=
  recordDecrypt_region_vregs_okTPTight_ext C A ctl S (tripleRatchetExterns C ctl abs) img
    (AllocContracts4K.of_AllocContracts
      (Stage2Contracts.of_tripleRatchetProgAt' (b := img.base) (ctl := ctl) hHooks).toAllocContracts)
    himg hTry

/-- SPQR V1 `try_decrypt_from_record` region contract `recordDecryptSpecTPTight` on
`tripleRatchetProgAt` from `TripleRatchetHooks` and `SpqrHooks`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_ok_PTight
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img) :=
  recordDecrypt_region_okTPTight C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight C A ctl K abs img hH hQ himg)

/-- `recordDecryptV1_region_ok_PTight` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptV1_region_vregs_ok_PTight
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hH : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hQ : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    region_ok (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
      (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecTPTight C A ctl uuidTryParse
        (LibsignalSpqrV1.spqrV1 C.F K) img).withVRegs :=
  recordDecrypt_region_vregs_okTPTight C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img hH himg
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptV1_ok_PTight C A ctl K abs img hH hQ himg)

end CryptoVerification.Cli.LibsignalSpqrV1.M4
