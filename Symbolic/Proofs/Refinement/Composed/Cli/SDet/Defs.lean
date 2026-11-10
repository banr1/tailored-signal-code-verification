/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Party-State and Session Equivalence for CLI Model Determinism

Defines `PqSessionEquiv` and `PqPartyEquiv` characterizing `PqParty` states with identical
`filesOf (encodeDir P st)` directory snapshots, together with `InputsEquiv` equivalence lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli.SDet.Draft

open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (PreKeyBundleFields PreKeyMessageFields UnreachedPqxdhPrimitives PEParams initiateTapeLen wireWhisper
  wirePrekey)
open CryptoVerification.SignalSession (PqParty pqInitInputs pqSendInputs pqRecvInputs
  pqxdhExpectedOutcome pqInitModel pqSendModel pqRecvWhisperModel pqRecvPrekeyModel PqSessionMatches PqxdhPartyInSpecDomain
  Inputs Outcome filesOf)

def InputsEquiv (i i' : Inputs) : Prop :=
  i.argv = i'.argv ∧ i.dirs = i'.dirs ∧ i.stdin = i'.stdin ∧
    ∀ p, filesOf i.files p = filesOf i'.files p

def PqCall (X : UnreachedPqxdhPrimitives) (W : PEParams) (st : PqParty) (i₀ : Inputs) (o₀ : Outcome) : Prop :=
  (∃ (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen), st.session = none ∧
    i₀ = pqInitInputs W st b t ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqInitModel X W st b t)) ∨
  (∃ (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64), m.length < 2 ^ 32 ∧
    i₀ = pqSendInputs W st m r ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqSendModel W st m r.toList)) ∨
  (∃ (c : List (BitVec 8)) (rc : BitVec 256), c.length < 2 ^ 32 ∧
    i₀ = pqRecvInputs W st (wireWhisper :: c) rc ∧ o₀ = pqxdhExpectedOutcome W i₀ (pqRecvWhisperModel W st c rc)) ∨
  (∃ (m : PreKeyMessageFields) (rc : BitVec 256), m.inner.length + 2048 < 2 ^ 32 ∧
    (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) ∧
    i₀ = pqRecvInputs W st (wirePrekey :: m.bytes) rc ∧
    o₀ = pqxdhExpectedOutcome W i₀ (pqRecvPrekeyModel X W st m rc))

def PqModelRel (Xof : ExternInterpretation → UnreachedPqxdhPrimitives) (Wof : ExternInterpretation → PEParams)
    (interp : ExternInterpretation) (i : Inputs) (o : Outcome) : Prop :=
  ∃ st i₀, PqxdhPartyInSpecDomain (Wof interp) st ∧ InputsEquiv i i₀ ∧ PqCall (Xof interp) (Wof interp) st i₀ o

end DY.Libsignal.Composed.Refinement.Cli.SDet.Draft

namespace DY.Libsignal.Composed.Refinement.Cli

theorem InputsEquiv.refl (i : CryptoVerification.SignalSession.Inputs) : InputsEquiv i i :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem InputsEquiv.symm {i i' : CryptoVerification.SignalSession.Inputs}
    (h : InputsEquiv i i') : InputsEquiv i' i :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun p => (h.2.2.2 p).symm⟩

theorem InputsEquiv.trans {i₁ i₂ i₃ : CryptoVerification.SignalSession.Inputs}
    (h₁₂ : InputsEquiv i₁ i₂) (h₂₃ : InputsEquiv i₂ i₃) : InputsEquiv i₁ i₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1, h₁₂.2.2.1.trans h₂₃.2.2.1,
    fun p => (h₁₂.2.2.2 p).trans (h₂₃.2.2.2 p)⟩

namespace SDet

open DY.Libsignal (HwBytes)
open CryptoGames.LibsignalSession (GhostState)
open CryptoVerification.E2E (PEParams RecordExtras encodeRecordUnderExtras encStateUnderExtras)
open CryptoVerification.SignalSession

/-- Equivalence on stored `(RecordExtras, GhostState HwBytes)` pairs up to `encodeRecordUnderExtras`:
all fields written by `encodeRecordUnderExtras` agree (in particular `x = x'` whenever `pendingPreKey = true`). -/
structure PqSessionEquiv (x : RecordExtras) (g : GhostState HwBytes)
    (x' : RecordExtras) (g' : GhostState HwBytes) : Prop where
  party_eq : g.party = g'.party
  session_eq : g.session = g'.session
  remoteReg_eq : x.remoteRegistrationId = x'.remoteRegistrationId
  localReg_eq : x.localRegistrationId = x'.localRegistrationId
  aliceBase_eq : x.aliceBaseKey = x'.aliceBaseKey
  pending_eq : g.session.pendingPreKey = true → x = x'

theorem PqSessionEquiv.refl (x : RecordExtras) (g : GhostState HwBytes) :
    PqSessionEquiv x g x g :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem encodeRecordX_eq_of_pqSessionEquiv {x x' : RecordExtras} {g g' : GhostState HwBytes}
    (h : PqSessionEquiv x g x' g') :
    encodeRecordUnderExtras (fun _ => x) g = encodeRecordUnderExtras (fun _ => x') g' := by
  unfold encodeRecordUnderExtras encStateUnderExtras
  cases hppk : g.session.pendingPreKey
  · have hppk' : g'.session.pendingPreKey = false := h.session_eq ▸ hppk
    simp [h.session_eq, hppk', h.remoteReg_eq, h.localReg_eq, h.aliceBase_eq]
  · have hppk' : g'.session.pendingPreKey = true := h.session_eq ▸ hppk
    have hx := h.pending_eq hppk
    simp [hx, h.session_eq, hppk']

/-- Equivalence on `PqParty` induced by `filesOf` on `encodeDir` under `PqxdhPartyInSpecDomain`. -/
structure PqPartyEquiv (st st' : PqParty) : Prop where
  party_eq : st.party = st'.party
  me_eq : st.me = st'.me
  peerId_eq : st.peerId = st'.peerId
  session_rel : Option.Rel (fun p p' => PqSessionEquiv p.1 p.2 p'.1 p'.2) st.session st'.session
  signed_lookup : ∀ id, st.signed.lookup id = st'.signed.lookup id
  oneTime_lookup : ∀ id, st.oneTime.lookup id = st'.oneTime.lookup id
  kyberOneTime_lookup : ∀ id, st.kyberOneTime.lookup id = st'.kyberOneTime.lookup id
  kyberLastResort_lookup : ∀ id, st.kyberLastResort.lookup id = st'.kyberLastResort.lookup id
  signed_nodup : (st.signed.map (·.1)).Nodup ∧ (st'.signed.map (·.1)).Nodup
  oneTime_nodup : (st.oneTime.map (·.1)).Nodup ∧ (st'.oneTime.map (·.1)).Nodup
  kyberOneTime_nodup : (st.kyberOneTime.map (·.1)).Nodup ∧ (st'.kyberOneTime.map (·.1)).Nodup
  kyberLastResort_nodup : (st.kyberLastResort.map (·.1)).Nodup ∧ (st'.kyberLastResort.map (·.1)).Nodup

end SDet

end DY.Libsignal.Composed.Refinement.Cli
