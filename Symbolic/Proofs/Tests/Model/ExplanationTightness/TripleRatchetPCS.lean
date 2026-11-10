/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRPCSTraces

@[expose] public section

set_option autoImplicit false

open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (TestTracePredicates mkTestTracePredicates FSQueryP PCSQueryP fsQuery_iff_test pcsQuery_iff_test)

/-!
# Tightness of Triple Ratchet Post-Compromise Security

Single-point mutant refutations for `PCSQuery`, `RootDescends`, `DerivesChain`, and
`DerivesMsgKey` in the composed `PostCompromiseSecurity` property. Dropping any compromise
disjunct or healing-share alternative, or restricting root descent or symmetric-ratchet steps, is
refuted on reachable traces of the composed protocol. Because `bobStart` ratchets before storing
state and never logs `HonestDH` for `spkSk`, the first PCS heal in an honest session is Bob's
sending half-step in `bobStart` (`ownSk = dhsB1`, `peerSk = dhsA`).
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetPCS

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (dhsA dhsA2 dhsB1 dhsB2 stA0 stA4 stB1
  stB5)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (createChain_comm rnd_inj)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (
  eq_of_derivesMsgKey_createChain_zero isChainRoot_createChain_snd kdfCk_snd_inj saltDepth
  saltDepth_createChain_fst saltDepth_createChain_snd saltDepth_kdfCk_snd saltDepth_keys1_rk
  saltDepth_le_of_rootDescends saltDepth_lt_of_derivesChain saltDepth_lt_of_derivesMsgKey
  saltDepth_lt_of_rootDescends_ne saltDepth_rnd saltDepth_stA0_rk saltDepth_stA4_rk
  saltDepth_stB1_rk saltDepth_stB2_cks)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRPCSTraces (mkA4_0 mkA4_1 mkB0 mkB1 mkB5_0
  rootDescends_stA0_rk saltDepth_mkA4_0 saltDepth_mkA4_1 saltDepth_mkB0 saltDepth_mkB1
  saltDepth_mkB5_0 saltDepth_of_rootDescends_stA0_rk stA4_cks_eq stA4_rk_eq stB1_cks_eq stB1_rk_eq
  stB2_cks_eq stB5_cks_eq trCK trCK2 trCK2_compromised trCK2_honestDH_dhsA trCK2_honestDH_dhsB1
  trCK2_knows trCK2_messageKey trCK2_reach trCK_compromised trCK_honestDH_dhsA trCK_honestDH_dhsB1
  trCK_knows trCK_messageKey trCK_reach trDC trDC_compromised_saltDepth trDC_honestDH_dhsA2
  trDC_honestDH_dhsB1 trDC_knows trDC_messageKey trDC_reach trMK trMK_compromised
  trMK_honestDH_dhsA trMK_honestDH_dhsB1 trMK_knows trMK_messageKey trMK_reach trRKP2
  trRKP2_compromised_saltDepth trRKP2_honestDH_dhsA trRKP2_honestDH_dhsB1 trRKP2_knows
  trRKP2_messageKey trRKP2_not_ck trRKP2_reach trRKPost trRKPost_compromised_saltDepth
  trRKPost_honestDH_dhsA trRKPost_honestDH_dhsB1 trRKPost_knows trRKPost_messageKey trRKPost_reach
  trRKPre trRKPre_compromised trRKPre_compromised_saltDepth trRKPre_honestDH_dhsA
  trRKPre_honestDH_dhsB1 trRKPre_knows trRKPre_messageKey trRKPre_reach trRP
  trRP_compromised_saltDepth trRP_honestDH_dhsA trRP_honestDH_dhsB1 trRP_knows trRP_messageKey
  trRP_reach)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.DiffieHellman
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet (createChain kdfCk chainKeyAt DerivesMsgKey RootDescends
  DerivesChain)
open DY.Libsignal.TripleRatchet.Cheval

/-- `PostCompromiseSecurity` parameterized by the trace query `Q`. -/
def PostCompromiseSecurityWith (Q : TestTracePredicates → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    Q (mkTestTracePredicates tr)

theorem postCompromiseSecurityWith_real :
    PostCompromiseSecurityWith PCSQueryP ↔ PostCompromiseSecurity :=
  forall₂_congr fun tr _ => (pcsQuery_iff_test tr _).symm

theorem PostCompromiseSecurityWith.mono {Q Q' : TestTracePredicates → Prop}
    (h : ∀ P, Q P → Q' P) (hQ : PostCompromiseSecurityWith Q) :
    PostCompromiseSecurityWith Q' :=
  fun tr hR => h _ (hQ tr hR)

/-! ## Disjunct-drop and boundary mutants -/

section DisjunctAndBoundaryMutants

def PCSQuery_mkWith (D1 : TestTracePredicates → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    D1 P mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_mkWith_real (P : TestTracePredicates) :
    PCSQuery_mkWith (fun P mk => P.Compromised mk) P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_withoutMK (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_withoutMK_iff (P : TestTracePredicates) :
    PCSQuery_withoutMK P ↔ PCSQuery_mkWith (fun _ _ => False) P := by
  simp [PCSQuery_withoutMK, PCSQuery_mkWith]

def PostCompromiseSecurity_withoutMK : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutMK

def PCSQuery_ckWith (D2 : TestTracePredicates → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    D2 P mk ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_ckWith_real (P : TestTracePredicates) :
    PCSQuery_ckWith (fun P mk => ∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) P ↔ PCSQueryP P :=
  Iff.rfl

def PCSQuery_withoutCK (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_withoutCK_iff (P : TestTracePredicates) :
    PCSQuery_withoutCK P ↔ PCSQuery_ckWith (fun _ _ => False) P := by
  simp [PCSQuery_withoutCK, PCSQuery_ckWith]

def PostCompromiseSecurity_withoutCK : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutCK

def PCSQuery_rkPostWith (D3 : TestTracePredicates → Bytes → Bytes → Prop) (P : TestTracePredicates) :
    Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    D3 P rk_heal mk ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostWith_real (P : TestTracePredicates) :
    PCSQuery_rkPostWith
      (fun P rk_heal mk =>
        ∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
          P.Compromised rk) P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_withoutRKPost (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_withoutRKPost_iff (P : TestTracePredicates) :
    PCSQuery_withoutRKPost P ↔ PCSQuery_rkPostWith (fun _ _ _ => False) P := by
  simp [PCSQuery_withoutRKPost, PCSQuery_rkPostWith]

def PCSQuery_rkPostDescWith (R : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, R rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostDescWith_real (P : TestTracePredicates) :
    PCSQuery_rkPostDescWith RootDescends P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_rkPostStrict (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, (RootDescends rk_heal rk ∧ rk ≠ rk_heal) ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostStrict_def (P : TestTracePredicates) :
    PCSQuery_rkPostStrict P ↔
      PCSQuery_rkPostDescWith (fun rk_heal rk => RootDescends rk_heal rk ∧ rk ≠ rk_heal) P :=
  Iff.rfl

def PostCompromiseSecurity_withoutRKPost : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutRKPost

def PostCompromiseSecurity_rkPostStrict : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPostStrict

def PCSQuery_rkPreShareWith (S : TestTracePredicates → Bytes → Bytes → Prop) (P : TestTracePredicates) :
    Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧ S P ownSk peerSk)

theorem pcsQuery_rkPreShareWith_real (P : TestTracePredicates) :
    PCSQuery_rkPreShareWith (fun P ownSk peerSk => P.Compromised ownSk ∨ P.Compromised peerSk) P ↔
      PCSQueryP P := Iff.rfl

def PCSQuery_withoutRKPreOwn (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      P.Compromised peerSk)

theorem pcsQuery_withoutRKPreOwn_def (P : TestTracePredicates) :
    PCSQuery_withoutRKPreOwn P ↔
      PCSQuery_rkPreShareWith (fun P _ peerSk => P.Compromised peerSk) P := Iff.rfl

def PCSQuery_withoutRKPrePeer (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      P.Compromised ownSk)

theorem pcsQuery_withoutRKPrePeer_def (P : TestTracePredicates) :
    PCSQuery_withoutRKPrePeer P ↔
      PCSQuery_rkPreShareWith (fun P ownSk _ => P.Compromised ownSk) P := Iff.rfl

def PCSQuery_rkPreWith (D4 : TestTracePredicates → Bytes → Bytes → Bytes → Prop)
    (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    D4 P rk_prev ownSk peerSk

theorem pcsQuery_rkPreWith_real (P : TestTracePredicates) :
    PCSQuery_rkPreWith
      (fun P rk_prev ownSk peerSk =>
        (∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
          (P.Compromised ownSk ∨ P.Compromised peerSk)) P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_withoutRKPre (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk)

theorem pcsQuery_withoutRKPre_iff (P : TestTracePredicates) :
    PCSQuery_withoutRKPre P ↔ PCSQuery_rkPreWith (fun _ _ _ _ => False) P := by
  simp [PCSQuery_withoutRKPre, PCSQuery_rkPreWith]

def PCSQuery_rkPreDescWith (R : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, R rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPreDescWith_real (P : TestTracePredicates) :
    PCSQuery_rkPreDescWith RootDescends P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_rkPreStrict (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, (RootDescends rk rk_prev ∧ rk ≠ rk_prev) ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPreStrict_def (P : TestTracePredicates) :
    PCSQuery_rkPreStrict P ↔
      PCSQuery_rkPreDescWith (fun rk rk_prev => RootDescends rk rk_prev ∧ rk ≠ rk_prev) P :=
  Iff.rfl

def PostCompromiseSecurity_withoutRKPreOwn : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutRKPreOwn

def PostCompromiseSecurity_withoutRKPrePeer : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutRKPrePeer

def PostCompromiseSecurity_withoutRKPre : Prop :=
  PostCompromiseSecurityWith PCSQuery_withoutRKPre

def PostCompromiseSecurity_rkPreStrict : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPreStrict

/-- Dropping `P.Compromised mk` from `PCSQuery` is refuted on `trMK`, where only the skipped
post-heal message key `mkB0` is exposed. -/
theorem not_PostCompromiseSecurity_withoutMK : ¬ PostCompromiseSecurity_withoutMK := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB0 :=
    .inl ⟨0, by rw [← stB1_cks_eq]; rfl⟩
  rcases hPCS trMK trMK_reach mkB0 stA0.rk dhsB1 dhsA trMK_messageKey trMK_knows
      trMK_honestDH_dhsB1 trMK_honestDH_dhsA hHeal with
    ⟨ck, hDM, hComp⟩ | ⟨rk, ck, _, hDC, hDM, hComp⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h1 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trMK_compromised hComp] at h1; omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trMK_compromised hComp] at h1; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    rw [trMK_compromised hComp, saltDepth_mkB0, saltDepth_stA0_rk] at h1; omega

/-- Dropping the chain-key disjunct from `PCSQuery` is refuted on `trCK`, where exposing Bob's
post-heal sending chain key `stB2.cks` reveals `mkB0`. -/
theorem not_PostCompromiseSecurity_withoutCK : ¬ PostCompromiseSecurity_withoutCK := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB0 :=
    .inl ⟨0, by rw [← stB1_cks_eq]; rfl⟩
  rcases hPCS trCK trCK_reach mkB0 stA0.rk dhsB1 dhsA trCK_messageKey trCK_knows
      trCK_honestDH_dhsB1 trCK_honestDH_dhsA hHeal with
    hComp | ⟨rk, ck, _, hDC, hDM, hComp⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have heq := congrArg saltDepth (trCK_compromised hComp)
    rw [saltDepth_mkB0, saltDepth_stB2_cks] at heq; omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trCK_compromised hComp, saltDepth_stB2_cks] at h1
    rw [saltDepth_mkB0] at h2; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    rw [trCK_compromised hComp, saltDepth_stB2_cks, saltDepth_stA0_rk] at h1; omega

/-- Excluding `rk = rk_heal` from the post-heal root-key disjunct is refuted on `trRKPost`,
where exposing `stB1.rk = rk_heal` and `dhsB1` reveals `mkA4_0` on `stA4.cks`. -/
theorem not_PostCompromiseSecurity_rkPostStrict : ¬ PostCompromiseSecurity_rkPostStrict := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkA4_0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkA4_0 :=
    .inr ⟨stA4.cks, ⟨stB1.rk, dhPk dhsB1, dhsA2, stB1_rk_eq ▸ .refl, stA4_cks_eq⟩, ⟨0, rfl⟩⟩
  rcases hPCS trRKPost trRKPost_reach mkA4_0 stA0.rk dhsB1 dhsA trRKPost_messageKey trRKPost_knows
      trRKPost_honestDH_dhsB1 trRKPost_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, _, ⟨hDesc, hne⟩, _, _, hComp⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h0 := trRKPost_compromised_saltDepth hComp
    rw [saltDepth_mkA4_0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stB1.rk (dhPk dhsB1) dhsA2).2).2 := by
      rw [← stA4_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPost_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stB1_rk] at h0; omega
  · have h1 := saltDepth_lt_of_rootDescends_ne hDesc hne
    change saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 + 2 ≤ saltDepth rk at h1
    rw [saltDepth_createChain_fst, saltDepth_stA0_rk] at h1
    have h0 := trRKPost_compromised_saltDepth hComp; omega
  · have h1 := saltDepth_of_rootDescends_stA0_rk hDesc
    have h0 := trRKPost_compromised_saltDepth hComp; omega

theorem not_PostCompromiseSecurity_withoutRKPost : ¬ PostCompromiseSecurity_withoutRKPost := by
  intro hMut
  apply not_PostCompromiseSecurity_rkPostStrict
  intro tr hR mk rk_prev ownSk peerSk hMk hK hO hP hHeal
  rcases hMut tr hR mk rk_prev ownSk peerSk hMk hK hO hP hHeal with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

/-- Dropping `P.Compromised peerSk` from the pre-heal disjunct is refuted on `trRKPre`, where
exposing `stA0.rk` and `dhsA` reveals `mkB0` while `ownSk = dhsB1` remains uncompromised. -/
theorem not_PostCompromiseSecurity_withoutRKPrePeer : ¬ PostCompromiseSecurity_withoutRKPrePeer := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB0 :=
    .inl ⟨0, by rw [← stB1_cks_eq]; rfl⟩
  rcases hPCS trRKPre trRKPre_reach mkB0 stA0.rk dhsB1 dhsA trRKPre_messageKey trRKPre_knows
      trRKPre_honestDH_dhsB1 trRKPre_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, _, hDesc, _, _, hComp⟩ | ⟨_, hCompOwn⟩
  · have h0 := trRKPre_compromised_saltDepth hComp
    rw [saltDepth_mkB0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA0.rk (dhPk dhsA) dhsB1).2).2 := by
      rw [← stB2_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPre_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stA0_rk] at h0; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    change saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 ≤ saltDepth rk at h1
    rw [saltDepth_createChain_fst, saltDepth_stA0_rk] at h1
    have h0 := trRKPre_compromised_saltDepth hComp; omega
  · rcases trRKPre_compromised hCompOwn with heq | heq
    · have h0 := congrArg saltDepth heq
      rw [saltDepth_rnd, saltDepth_stA0_rk] at h0; omega
    · have := rnd_inj heq; omega

/-- By symmetry of `ownSk` and `peerSk` under `createChain_comm`, dropping `P.Compromised ownSk`
is equivalent to dropping `P.Compromised peerSk`. -/
theorem pcsQuery_withoutRKPreOwn_iff_withoutRKPrePeer (P : TestTracePredicates) :
    PCSQuery_withoutRKPreOwn P ↔ PCSQuery_withoutRKPrePeer P := by
  constructor
  · intro h mk rk_prev ownSk peerSk hMk hK hO hP hHeal
    have h' := h mk rk_prev peerSk ownSk hMk hK hP hO
    rw [createChain_comm rk_prev ownSk peerSk] at h'
    exact h' hHeal
  · intro h mk rk_prev ownSk peerSk hMk hK hO hP hHeal
    have h' := h mk rk_prev peerSk ownSk hMk hK hP hO
    rw [createChain_comm rk_prev ownSk peerSk] at h'
    exact h' hHeal

theorem not_PostCompromiseSecurity_withoutRKPreOwn : ¬ PostCompromiseSecurity_withoutRKPreOwn :=
  fun h => not_PostCompromiseSecurity_withoutRKPrePeer fun tr hR =>
    (pcsQuery_withoutRKPreOwn_iff_withoutRKPrePeer _).mp (h tr hR)

theorem not_PostCompromiseSecurity_withoutRKPre : ¬ PostCompromiseSecurity_withoutRKPre := by
  intro hMut
  apply not_PostCompromiseSecurity_withoutRKPrePeer
  intro tr hR mk rk_prev ownSk peerSk hMk hK hO hP hHeal
  rcases hMut tr hR mk rk_prev ownSk peerSk hMk hK hO hP hHeal with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

/-- Excluding `rk = rk_prev` from the pre-heal root-key disjunct is refuted on `trRKPre`, where
`stA0.rk = rk_prev` is compromised while `keys1.rk` is not. -/
theorem not_PostCompromiseSecurity_rkPreStrict : ¬ PostCompromiseSecurity_rkPreStrict := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB0 :=
    .inl ⟨0, by rw [← stB1_cks_eq]; rfl⟩
  rcases hPCS trRKPre trRKPre_reach mkB0 stA0.rk dhsB1 dhsA trRKPre_messageKey trRKPre_knows
      trRKPre_honestDH_dhsB1 trRKPre_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, _, hDesc, _, _, hComp⟩ | ⟨⟨rk, ⟨hDesc, hne⟩, hComp⟩, _⟩
  · have h0 := trRKPre_compromised_saltDepth hComp
    rw [saltDepth_mkB0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA0.rk (dhPk dhsA) dhsB1).2).2 := by
      rw [← stB2_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPre_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stA0_rk] at h0; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    change saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 ≤ saltDepth rk at h1
    rw [saltDepth_createChain_fst, saltDepth_stA0_rk] at h1
    have h0 := trRKPre_compromised_saltDepth hComp; omega
  · rcases rootDescends_stA0_rk hDesc with rfl | rfl
    · exact hne rfl
    · have h0 := trRKPre_compromised_saltDepth hComp
      rw [saltDepth_keys1_rk] at h0; omega

end DisjunctAndBoundaryMutants

/-! ## Root-descent and chain-derivation mutants -/

section DescentMutants

def PCSQuery_rkPreDirect (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
      P.Compromised rk) ∨
    (P.Compromised rk_prev ∧ (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPreDirect_iff (P : TestTracePredicates) :
    PCSQuery_rkPreDirect P ↔ PCSQuery_rkPreDescWith Eq P := by
  simp [PCSQuery_rkPreDirect, PCSQuery_rkPreDescWith]

def PostCompromiseSecurity_rkPreDirect : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPreDirect

/-- Restricting pre-heal root descent to `rk = rk_prev` is refuted on `trDC`, where `stA0.rk`
(parent of `rk_prev = stB1.rk`), `dhsA`, and `dhsA2` are exposed without exposing `stB1.rk`. -/
theorem not_PostCompromiseSecurity_rkPreDirect : ¬ PostCompromiseSecurity_rkPreDirect := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stB1.rk (dhPk dhsB1) dhsA2).2 mkA4_0 ∨
      ∃ ck, DerivesChain (createChain stB1.rk (dhPk dhsB1) dhsA2).1 ck ∧ DerivesMsgKey ck mkA4_0 :=
    .inl ⟨0, by rw [← stA4_cks_eq]; rfl⟩
  rcases hPCS trDC trDC_reach mkA4_0 stB1.rk dhsA2 dhsB1 trDC_messageKey trDC_knows
      trDC_honestDH_dhsA2 trDC_honestDH_dhsB1 hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, _, hDesc, _, _, hComp⟩ | ⟨hComp, _⟩
  · have h0 := trDC_compromised_saltDepth hComp
    rw [saltDepth_mkA4_0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stB1.rk (dhPk dhsB1) dhsA2).2).2 := by
      rw [← stA4_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trDC_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stB1_rk] at h0; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    change saltDepth (createChain stB1.rk (dhPk dhsB1) dhsA2).1 ≤ saltDepth rk at h1
    rw [saltDepth_createChain_fst, saltDepth_stB1_rk] at h1
    have h0 := trDC_compromised_saltDepth hComp; omega
  · have h0 := trDC_compromised_saltDepth hComp
    rw [saltDepth_stB1_rk] at h0; omega

def PCSQuery_rkPostDirect (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, rk = rk_heal ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostDirect_def (P : TestTracePredicates) :
    PCSQuery_rkPostDirect P ↔ PCSQuery_rkPostDescWith (fun rk_heal rk => rk = rk_heal) P :=
  Iff.rfl

def PostCompromiseSecurity_rkPostDirect : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPostDirect

/-- Restricting post-heal root descent to `rk = rk_heal` is refuted on `trRP`, where exposing
`stA4.rk` (one step after `rk_heal = stB1.rk`) and `dhsA2` reveals `mkB5_0`. -/
theorem not_PostCompromiseSecurity_rkPostDirect : ¬ PostCompromiseSecurity_rkPostDirect := by
  intro hPCS
  have hDescHeal : RootDescends (createChain stA0.rk (dhPk dhsA) dhsB1).1 stA4.rk := by
    rw [← stB1_rk_eq, stA4_rk_eq]
    exact .step .refl
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB5_0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB5_0 :=
    .inr ⟨stB5.cks, ⟨stA4.rk, dhPk dhsA2, dhsB2, hDescHeal, stB5_cks_eq⟩, ⟨0, rfl⟩⟩
  rcases hPCS trRP trRP_reach mkB5_0 stA0.rk dhsB1 dhsA trRP_messageKey trRP_knows
      trRP_honestDH_dhsB1 trRP_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, _, hrk, _, _, hComp⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h0 := trRP_compromised_saltDepth hComp
    rw [saltDepth_mkB5_0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA4.rk (dhPk dhsA2) dhsB2).2).2 := by
      rw [← stB5_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRP_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stA4_rk] at h0; omega
  · have h0 := trRP_compromised_saltDepth hComp
    rw [hrk] at h0
    change saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 = 8 ∨
      saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 = 0 at h0
    rw [saltDepth_createChain_fst, saltDepth_stA0_rk] at h0; omega
  · have h1 := saltDepth_of_rootDescends_stA0_rk hDesc
    have h0 := trRP_compromised_saltDepth hComp; omega

def DerivesChainWith (R : Bytes → Bytes → Prop) (rk ck : Bytes) : Prop :=
  ∃ rk' theirPk ourSk, R rk rk' ∧ ck = (createChain rk' theirPk ourSk).2

theorem derivesChainWith_real (rk ck : Bytes) :
    DerivesChainWith RootDescends rk ck ↔ DerivesChain rk ck := Iff.rfl

/-- Chain derivation from a strict descendant `rk' ≠ rk` of `rk`, omitting `RootDescends.refl`. -/
def DerivesChainStrict (rk ck : Bytes) : Prop :=
  ∃ rk' theirPk ourSk, (RootDescends rk rk' ∧ rk' ≠ rk) ∧ ck = (createChain rk' theirPk ourSk).2

theorem derivesChainStrict_def (rk ck : Bytes) :
    DerivesChainStrict rk ck ↔
      DerivesChainWith (fun rk rk' => RootDescends rk rk' ∧ rk' ≠ rk) rk ck := Iff.rfl

def PCSQuery_rkPostChainWith (DC : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DC rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostChainWith_real (P : TestTracePredicates) :
    PCSQuery_rkPostChainWith DerivesChain P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_rkPostChainStrict (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChainStrict rk ck ∧ DerivesMsgKey ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostChainStrict_def (P : TestTracePredicates) :
    PCSQuery_rkPostChainStrict P ↔ PCSQuery_rkPostChainWith DerivesChainStrict P := Iff.rfl

def PostCompromiseSecurity_rkPostChainStrict : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPostChainStrict

/-- Omitting `RootDescends.refl` from `DerivesChain` in the post-heal disjunct is refuted on
`trRKPost`, where `rk_heal = stB1.rk` is the direct parent of `stA4.cks`. -/
theorem not_PostCompromiseSecurity_rkPostChainStrict :
    ¬ PostCompromiseSecurity_rkPostChainStrict := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkA4_0 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkA4_0 :=
    .inr ⟨stA4.cks, ⟨stB1.rk, dhPk dhsB1, dhsA2, stB1_rk_eq ▸ .refl, stA4_cks_eq⟩, ⟨0, rfl⟩⟩
  rcases hPCS trRKPost trRKPost_reach mkA4_0 stA0.rk dhsB1 dhsA trRKPost_messageKey trRKPost_knows
      trRKPost_honestDH_dhsB1 trRKPost_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, hDesc, ⟨rk', _, _, ⟨hDesc', hne⟩, hck⟩, hDM, _⟩ |
    ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h0 := trRKPost_compromised_saltDepth hComp
    rw [saltDepth_mkA4_0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stB1.rk (dhPk dhsB1) dhsA2).2).2 := by
      rw [← stA4_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPost_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stB1_rk] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stB1.rk (dhPk dhsB1) dhsA2).2).2 := by
      rw [← stA4_cks_eq]; exact hDM
    have h1 := congrArg saltDepth ((eq_of_derivesMsgKey_createChain_zero hDM').symm.trans hck)
    simp only [saltDepth_createChain_snd, saltDepth_stB1_rk] at h1
    have h2 := saltDepth_lt_of_rootDescends_ne hDesc' hne
    have h3 := saltDepth_le_of_rootDescends hDesc
    change saltDepth (createChain stA0.rk (dhPk dhsA) dhsB1).1 ≤ saltDepth rk at h3
    rw [saltDepth_createChain_fst, saltDepth_stA0_rk] at h3
    omega
  · have h1 := saltDepth_of_rootDescends_stA0_rk hDesc
    have h0 := trRKPost_compromised_saltDepth hComp; omega

end DescentMutants

/-! ## Symmetric-ratchet step mutants -/

section MsgKeyStepMutants

/-- Message-key derivation restricted to the initial step (`steps = 0`). -/
def DerivesMsgKey0 (ck mk : Bytes) : Prop :=
  mk = (kdfCk ck).2

theorem derivesMsgKey_zero_iff (ck mk : Bytes) :
    (∃ steps : Nat, steps = 0 ∧ mk = (kdfCk (chainKeyAt ck steps)).2) ↔ DerivesMsgKey0 ck mk := by
  simp [DerivesMsgKey0, chainKeyAt]

def PCSQuery_ckStepsWith (DM : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DM ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_ckStepsWith_real (P : TestTracePredicates) :
    PCSQuery_ckStepsWith DerivesMsgKey P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_ckSteps0 (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey0 ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_ckSteps0_def (P : TestTracePredicates) :
    PCSQuery_ckSteps0 P ↔ PCSQuery_ckStepsWith DerivesMsgKey0 P := Iff.rfl

def PCSQuery_rkPostStepsWith (DM : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DM ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostStepsWith_real (P : TestTracePredicates) :
    PCSQuery_rkPostStepsWith DerivesMsgKey P ↔ PCSQueryP P := Iff.rfl

def PCSQuery_rkPostSteps0 (P : TestTracePredicates) : Prop :=
  ∀ mk rk_prev ownSk peerSk,
    P.MessageKey mk → P.AttackerKnows mk → P.HonestDH ownSk → P.HonestDH peerSk →
    let (rk_heal, ck_heal) := createChain rk_prev (DiffieHellman.dhPk peerSk) ownSk
    (DerivesMsgKey ck_heal mk ∨ ∃ ck, DerivesChain rk_heal ck ∧ DerivesMsgKey ck mk) →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, RootDescends rk_heal rk ∧ DerivesChain rk ck ∧ DerivesMsgKey0 ck mk ∧
      P.Compromised rk) ∨
    ((∃ rk, RootDescends rk rk_prev ∧ P.Compromised rk) ∧
      (P.Compromised ownSk ∨ P.Compromised peerSk))

theorem pcsQuery_rkPostSteps0_def (P : TestTracePredicates) :
    PCSQuery_rkPostSteps0 P ↔ PCSQuery_rkPostStepsWith DerivesMsgKey0 P := Iff.rfl

def PostCompromiseSecurity_ckSteps0 : Prop :=
  PostCompromiseSecurityWith PCSQuery_ckSteps0

def PostCompromiseSecurity_rkPostSteps0 : Prop :=
  PostCompromiseSecurityWith PCSQuery_rkPostSteps0

/-- Restricting `DerivesMsgKey` to `steps = 0` in the chain-key disjunct is refuted on `trCK2`,
where exposing `stB2.cks` reveals Bob's second message key `mkB1` (`steps = 1`). -/
theorem not_PostCompromiseSecurity_ckSteps0 : ¬ PostCompromiseSecurity_ckSteps0 := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkB1 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkB1 :=
    .inl ⟨1, by rw [← stB1_cks_eq]; rfl⟩
  rcases hPCS trCK2 trCK2_reach mkB1 stA0.rk dhsB1 dhsA trCK2_messageKey trCK2_knows
      trCK2_honestDH_dhsB1 trCK2_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, _, hDC, hDM, hComp⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h0 := congrArg saltDepth (trCK2_compromised hComp)
    rw [saltDepth_mkB1, saltDepth_stB2_cks] at h0; omega
  · have h0 := congrArg saltDepth (show mkB1 = (kdfCk ck).2 from hDM)
    rw [trCK2_compromised hComp, saltDepth_mkB1, saltDepth_kdfCk_snd, saltDepth_stB2_cks] at h0
    omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trCK2_compromised hComp, saltDepth_stB2_cks] at h1
    rw [saltDepth_mkB1] at h2; omega
  · have h1 := saltDepth_le_of_rootDescends hDesc
    rw [trCK2_compromised hComp, saltDepth_stB2_cks, saltDepth_stA0_rk] at h1; omega

/-- Restricting `DerivesMsgKey` to `steps = 0` in the post-heal root-key disjunct is refuted on
`trRKP2`, where exposing `stB1.rk` and `dhsB1` reveals `mkA4_1` (`steps = 1`) on `stA4.cks`. -/
theorem not_PostCompromiseSecurity_rkPostSteps0 : ¬ PostCompromiseSecurity_rkPostSteps0 := by
  intro hPCS
  have hHeal : DerivesMsgKey (createChain stA0.rk (dhPk dhsA) dhsB1).2 mkA4_1 ∨
      ∃ ck, DerivesChain (createChain stA0.rk (dhPk dhsA) dhsB1).1 ck ∧ DerivesMsgKey ck mkA4_1 :=
    .inr ⟨stA4.cks, ⟨stB1.rk, dhPk dhsB1, dhsA2, stB1_rk_eq ▸ .refl, stA4_cks_eq⟩, ⟨1, rfl⟩⟩
  rcases hPCS trRKP2 trRKP2_reach mkA4_1 stA0.rk dhsB1 dhsA trRKP2_messageKey trRKP2_knows
      trRKP2_honestDH_dhsB1 trRKP2_honestDH_dhsA hHeal with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, _, ⟨_, _, _, _, rfl⟩, hDM, _⟩ | ⟨⟨rk, hDesc, hComp⟩, _⟩
  · have h0 := trRKP2_compromised_saltDepth hComp
    rw [saltDepth_mkA4_1] at h0; omega
  · exact trRKP2_not_ck hDM hComp
  · exact isChainRoot_createChain_snd _ _ _ _ (kdfCk_snd_inj hDM).symm
  · have h1 := saltDepth_of_rootDescends_stA0_rk hDesc
    have h0 := trRKP2_compromised_saltDepth hComp; omega

end MsgKeyStepMutants

end Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetPCS
