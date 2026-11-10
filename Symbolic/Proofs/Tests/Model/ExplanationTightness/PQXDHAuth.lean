/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces

/-!
# Tightness of Composed PQXDH Authentication

Single-clause strengthenings of `Composed.Security.Authentication` (`PQXDH.AuthenticationQuery`),
each refuted by a reachable trace of the composed protocol. Omitting any of the three compromise
disjuncts in `HandshakeAuthWasCompromised` (`CompromisedIK`, `CompromisedSPK`, or `BrokenDH`),
requiring strict intended-peer agreement `b' = b` in `ResponderSessionAgreement`, or replacing
`SameDHKey`/`SameOPK` with byte equality on X25519 prekeys makes `Authentication` false.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHAuth

open Symbolic.Proofs.Tests.Shared.Composed.Adversary (trAlias trAlias_bobDone trAlias_keys
  trAlias_no_aliceDone_bob trAlias_out trAlias_reach trBrokenDHB_bobDone trBrokenDHB_reach
  trIKA_bobDone trIKA_reach trSPKB_bobDone trSPKB_reach)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB opkB pqskB spkB)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.PQXDHAuthTraces (Thm8Case
  handshakeAuthWasCompromised_iff_exists_thm8Case r3aTrace
  r3aTrace_aliceDone_spk_eq r3aTrace_bobDone r3aTrace_no_thm8Excuse r3aTrace_reach r3a_keys
  r3a_out r3bTrace r3bTrace_aliceDone_opk_eq r3bTrace_bobDone r3bTrace_no_thm8Excuse
  r3bTrace_reach r3b_keys r3b_out trAlias_no_thm8Excuse trBrokenDHB_no_thm8Agreement
  trBrokenDHB_not_other_thm8Case trIKA_no_thm8Agreement trIKA_not_other_thm8Case
  trSPKB_no_thm8Agreement trSPKB_not_other_thm8Case x25519Variant1_ne_dhPk)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman DY.PQKem
open DY.Libsignal.PQXDH
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security

/-! ## Parameterized authentication predicates -/

/-- `ResponderSessionAgreement` parameterized by the signed-prekey and one-time-prekey relations. -/
def Thm8AgreementWith
    (spkRel : Bytes → Bytes → Prop)
    (opkRel : Option Bytes → Option Bytes → Prop)
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ b' ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j < i ∧
    spkRel spk spk' ∧
    opkRel opk opk'

def AuthenticationQueryWith
    (Agreement : Participant → Participant → Bytes → Bytes → Option Bytes → Nat → ExecTrace → Prop)
    (Excuse : Participant → Participant → Bytes → Bytes → Nat → ExecTrace → Prop)
    (tr : ExecTrace) : Prop :=
  ∀ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i →
    Agreement b a spk pqpk opk i tr ∨
    Excuse b a ikA spk i tr

def AuthenticationWith
    (Agreement : Participant → Participant → Bytes → Bytes → Option Bytes → Nat → ExecTrace → Prop)
    (Excuse : Participant → Participant → Bytes → Bytes → Nat → ExecTrace → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    AuthenticationQueryWith Agreement Excuse tr

theorem thm8AgreementWith_real
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) :
    Thm8AgreementWith PQXDH.SameDHKey PQXDH.SameOPK a spk pqpk opk i tr ↔
      PQXDH.ResponderSessionAgreement a spk pqpk opk i tr :=
  Iff.rfl

theorem authenticationQueryWith_real (tr : ExecTrace) :
    AuthenticationQueryWith (fun _ => PQXDH.ResponderSessionAgreement) PQXDH.HandshakeAuthWasCompromised tr ↔
      PQXDH.AuthenticationQuery tr :=
  Iff.rfl

theorem authenticationWith_real :
    AuthenticationWith (fun _ => PQXDH.ResponderSessionAgreement) PQXDH.HandshakeAuthWasCompromised ↔
      Authentication :=
  Iff.rfl

theorem authenticationWith_exists_thm8Case_iff :
    AuthenticationWith (fun _ => PQXDH.ResponderSessionAgreement)
      (fun b a ikA spk i tr => ∃ k : Fin 3, Thm8Case b a ikA spk i tr k) ↔
      Authentication := by
  constructor
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv).imp id
      (handshakeAuthWasCompromised_iff_exists_thm8Case b a ikA spk i tr).mpr
  · intro h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv
    exact (h tr hR b a ikB ikA spk pqpk opk ek ct keys i hEv).imp id
      (handshakeAuthWasCompromised_iff_exists_thm8Case b a ikA spk i tr).mp

/-! ## Compromise-disjunct omissions -/

/-- `HandshakeAuthWasCompromised` omitting branch `omitted` of `Thm8Case`. -/
def Thm8ExcuseWithout
    (omitted : Fin 3) (b a : Participant) (ikA spk : Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ k : Fin 3, k ≠ omitted ∧ Thm8Case b a ikA spk i tr k

def Authentication_withoutCase (omitted : Fin 3) : Prop :=
  AuthenticationWith (fun _ => PQXDH.ResponderSessionAgreement) (Thm8ExcuseWithout omitted)

theorem not_Authentication_withoutCase_of_witness
    {omitted : Fin 3} {tr : ExecTrace}
    {b a : Participant} {ikB ikA spk pqpk : Bytes} {opk : Option Bytes}
    {ek ct : Bytes} {keys : HandshakeKeys} {i : Nat}
    (hReach : tr.Reachable reachability)
    (hBob : tr.EventLoggedAt (PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i)
    (hNoAgree : ¬ PQXDH.ResponderSessionAgreement a spk pqpk opk i tr)
    (hNoOther : ∀ k : Fin 3, k ≠ omitted → ¬ Thm8Case b a ikA spk i tr k) :
    ¬ Authentication_withoutCase omitted := by
  intro hAuth
  rcases hAuth tr hReach b a ikB ikA spk pqpk opk ek ct keys i hBob with
    hAgree | ⟨k, hkNe, hkCase⟩
  · exact hNoAgree hAgree
  · exact hNoOther k hkNe hkCase

/-- Omitting `CompromisedIK a ikA` (`Thm8Case 0`) falsifies `Authentication` (`trIKA`). -/
theorem not_Authentication_withoutCase0 : ¬ Authentication_withoutCase 0 :=
  not_Authentication_withoutCase_of_witness trIKA_reach trIKA_bobDone
    (trIKA_no_thm8Agreement _ _ _ _ _) trIKA_not_other_thm8Case

/-- Omitting `CompromisedSPK b spk` (`Thm8Case 1`) falsifies `Authentication` (`trSPKB`). -/
theorem not_Authentication_withoutCase1 : ¬ Authentication_withoutCase 1 :=
  not_Authentication_withoutCase_of_witness trSPKB_reach trSPKB_bobDone
    (trSPKB_no_thm8Agreement _ _ _ _ _) trSPKB_not_other_thm8Case

/-- Omitting `BrokenDH` (`Thm8Case 2`) falsifies `Authentication` (`trBrokenDHB`). -/
theorem not_Authentication_withoutCase2 : ¬ Authentication_withoutCase 2 :=
  not_Authentication_withoutCase_of_witness trBrokenDHB_reach trBrokenDHB_bobDone
    (trBrokenDHB_no_thm8Agreement _ _ _ _ _) trBrokenDHB_not_other_thm8Case

/-! ## Strict intended-peer agreement -/

/-- `ResponderSessionAgreement` strengthened to require Alice's intended peer `b'` to equal `b`. -/
def Thm8Agreement_strictPeer
    (b a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j < i ∧
    PQXDH.SameDHKey spk spk' ∧
    PQXDH.SameOPK opk opk'

def Authentication_strictPeer : Prop :=
  AuthenticationWith Thm8Agreement_strictPeer PQXDH.HandshakeAuthWasCompromised

/-- Requiring strict intended-peer agreement `b' = b` falsifies `Authentication` via identity-key
re-registration (`trAlias`). -/
theorem not_Authentication_strictPeer : ¬ Authentication_strictPeer := by
  intro hAuth
  rcases hAuth trAlias trAlias_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none trAlias_out.ek trAlias_out.ct trAlias_keys 44 trAlias_bobDone with
    ⟨ikA', ikB', spk', opk', ek', ct', keys', j, hEv, _⟩ | hExc
  · exact trAlias_no_aliceDone_bob ikA' ikB' spk' (kemPk pqskB) opk' ek' ct' keys' ⟨j, hEv⟩
  · exact trAlias_no_thm8Excuse hExc

/-! ## Exact byte equality on prekeys -/

/-- `ResponderSessionAgreement` with `SameDHKey spk spk'` strengthened to `spk' = spk`. -/
def Thm8Agreement_exactSPK
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ b' ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j < i ∧
    spk' = spk ∧
    PQXDH.SameOPK opk opk'

theorem thm8Agreement_exactSPK_iff
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) :
    Thm8Agreement_exactSPK a spk pqpk opk i tr ↔
      Thm8AgreementWith (fun s s' => s' = s) PQXDH.SameOPK a spk pqpk opk i tr :=
  Iff.rfl

def Authentication_exactSPK : Prop :=
  AuthenticationWith (fun _ => Thm8Agreement_exactSPK) PQXDH.HandshakeAuthWasCompromised

/-- Requiring `spk' = spk` instead of `SameDHKey spk spk'` falsifies `Authentication` under
X25519 torsion re-encoding (`r3aTrace`). -/
theorem not_Authentication_exactSPK : ¬ Authentication_exactSPK := by
  intro hAuth
  rcases hAuth r3aTrace r3aTrace_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none r3a_out.ek r3a_out.ct r3a_keys 44 r3aTrace_bobDone with
    ⟨b', ikA', ikB', spk', opk', ek', ct', keys', j, hEv, _, hSpk, _⟩ | hExc
  · have hEq := r3aTrace_aliceDone_spk_eq hEv
    rw [hEq] at hSpk
    exact x25519Variant1_ne_dhPk spkB hSpk
  · exact r3aTrace_no_thm8Excuse hExc

/-- `ResponderSessionAgreement` with `SameOPK opk opk'` strengthened to `opk' = opk`. -/
def Thm8Agreement_exactOPK
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) : Prop :=
  ∃ b' ikA' ikB' spk' opk' ek' ct' keys' j,
    tr.EventLoggedAt (PQXDHEvent.AliceDone a b' ikA' ikB' spk' pqpk opk' ek' ct' keys') j ∧
    j < i ∧
    PQXDH.SameDHKey spk spk' ∧
    opk' = opk

theorem thm8Agreement_exactOPK_iff
    (a : Participant) (spk pqpk : Bytes) (opk : Option Bytes)
    (i : Nat) (tr : ExecTrace) :
    Thm8Agreement_exactOPK a spk pqpk opk i tr ↔
      Thm8AgreementWith PQXDH.SameDHKey (fun o o' => o' = o) a spk pqpk opk i tr :=
  Iff.rfl

def Authentication_exactOPK : Prop :=
  AuthenticationWith (fun _ => Thm8Agreement_exactOPK) PQXDH.HandshakeAuthWasCompromised

/-- Requiring `opk' = opk` instead of `SameOPK opk opk'` falsifies `Authentication` under
server-side X25519 torsion re-encoding (`r3bTrace`). -/
theorem not_Authentication_exactOPK : ¬ Authentication_exactOPK := by
  intro hAuth
  rcases hAuth r3bTrace r3bTrace_reach "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) (some (dhPk opkB)) r3b_out.ek r3b_out.ct r3b_keys 46 r3bTrace_bobDone with
    ⟨b', ikA', ikB', spk', opk', ek', ct', keys', j, hEv, _, _, hOpk⟩ | hExc
  · have hEq := r3bTrace_aliceDone_opk_eq hEv
    rw [hEq] at hOpk
    injection hOpk with hVar
    exact x25519Variant1_ne_dhPk opkB hVar
  · exact r3bTrace_no_thm8Excuse hExc

end Symbolic.Proofs.Tests.Model.ExplanationTightness.PQXDHAuth
