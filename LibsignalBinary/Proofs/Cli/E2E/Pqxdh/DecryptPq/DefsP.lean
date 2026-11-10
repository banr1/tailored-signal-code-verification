/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `DistinctSid` and Tight-Panic `try_decrypt_with_state` Specifications

Variants of `tryDecryptSpec` and `tryDecryptSpecT` relaxing `x.st.remoteIdentity ≠ some x.st.localIdentity`
to `DistinctSid` and refining `onPanic` to `tryDecryptPqOnPanicTight`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalSession

set_option linter.unusedVariables false in
/-- Variant of `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec` relaxing identity inequality to `DistinctSid`. -/
def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧
          s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
          (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
          (x.st.remoteIdentity ≠ some x.st.localIdentity ∨
            CryptoVerification.E2E.Pqxdh.WireEntries.DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧
          SeedsLen32 x.st ∧
          x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗
        sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
        memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
        A.pool
      post := (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img).post
      onPanic := (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img).onPanic
      onOom := (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img).onOom }
    img

def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl uuidParse S img).post x s0 sf }

abbrev _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight

def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl uuidParse S img with
    onPanic := CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S uuidParse }

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S0SpecP (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  LocalIdentityKeyOk img C A ctl abs →
  RemoteIdentityKeyOk img C A ctl abs →
  IsSameAccountOk img.base C ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl parse S img).pre x s0 ∗ R) →
      reaches_pc (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS1PC img) s0
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1State A ctl img x R s0)

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.TryDecryptPqV1RunStmtP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img)

/-- `tryDecryptPqOnPanicTight` implies `(tryDecryptSpecTP ...).onPanic`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight_weaken
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl parse S img).onPanic x s0 sf ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptPqOnPanicTight, tryDecryptOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inr ha)

/-- `tryDecryptSpec.pre` implies `tryDecryptSpecP.pre`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP_pre_of_tryDecryptSpec
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {p : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s : State}
    (h : s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl p S img).pre x s ∗ R) :
    s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl p S img).pre x s ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  obtain ⟨himg, h⟩ := h
  refine ⟨himg, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  obtain ⟨hp, hrest⟩ := h
  refine ⟨⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    Or.inl hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2⟩, hrest⟩

/-- `tryDecryptSpecT.pre` implies `tryDecryptSpecTP.pre`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP_pre_of_tryDecryptSpecT
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {p : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s : State}
    (h : s.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl p S img).pre x s ∗ R) :
    s.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl p S img).pre x s ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT,
    CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  obtain ⟨hpq, h⟩ := h
  refine ⟨hpq, ?_⟩
  rw [sepConj_assoc] at h ⊢
  rw [sepConj_comm] at h ⊢
  rw [sepConj_assoc] at h ⊢
  exact CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP_pre_of_tryDecryptSpec h

section Smoke
variable (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (p : UuidParser) (S : SpqrModel) (img : Obj.Image)

example : (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl p S img).pre =
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl p S img).pre := rfl

example : (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight C A ctl p S img).post =
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl p S img).post := rfl

example : (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl p S img).post =
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl p S img).post := rfl

example : (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpecP C A ctl p S img).onPanic =
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl p S img).onPanic := rfl

example : (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTP C A ctl p S img).onPanic =
    (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl p S img).onPanic := rfl
end Smoke

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
