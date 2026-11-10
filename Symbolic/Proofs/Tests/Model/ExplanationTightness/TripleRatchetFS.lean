/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
public import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon
import Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRTraces

@[expose] public section

set_option autoImplicit false

/-!
# Tightness of the Triple Ratchet Forward-Secrecy Query

Mutant refutations for the composed `ForwardSecrecy` property (`FSQuery`). Dropping any of the
three compromise disjuncts (message key, chain key, or root key) or restricting `DerivesChain` or
`DerivesMsgKey` to a proper subrelation is refuted by a reachable trace of the composed model.
-/

namespace Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetFS

open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (dhsA dhsB1 stA0 stA4 stB2)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRCommon (FSQueryP TestTracePredicates
  createChain_snd_inj eq_of_derivesMsgKey_createChain_zero eq_of_rootDescends_keys1_rk
  eq_or_rootDescends_of_createChain_fst fsQuery_iff_test isChainRoot_createChain_snd
  kdfCk_snd_inj mkTestTracePredicates not_chainKeyAt_eq_of_root saltDepth
  saltDepth_createChain_snd saltDepth_kdfCk_snd saltDepth_lt_of_derivesChain
  saltDepth_lt_of_derivesMsgKey saltDepth_stA0_cks saltDepth_stA0_rk saltDepth_stA4_cks
  saltDepth_stB2_cks)
open Symbolic.Proofs.Tests.Shared.ExplanationTightness.TRTraces (isChainRoot_stB2_cks mkA0 mkA1
  mkB0 mkB1 mkDC saltDepth_mkA0 saltDepth_mkA1 saltDepth_mkB0 saltDepth_mkB1 saltDepth_mkDC
  stB2_cks_eq trCK trCK2 trCK2_compromised trCK2_knows trCK2_messageKey trCK2_reach
  trCK_compromised trCK_knows trCK_messageKey trCK_reach trDC trDC_compromised_saltDepth
  trDC_knows trDC_messageKey trDC_reach trMK trMK_compromised trMK_knows trMK_messageKey
  trMK_reach trRKP2 trRKP2_compromised_saltDepth trRKP2_knows trRKP2_messageKey trRKP2_reach
  trRKPost trRKPost_compromised trRKPost_compromised_saltDepth trRKPost_knows trRKPost_messageKey
  trRKPost_reach)
open DY DY.Libsignal DY.Libsignal.Composed

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Concat DY.Literal
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval

/-! ## Parameterized `ForwardSecrecy` and `FSQuery` -/

/-- `Security.ForwardSecrecy` parameterized by the trace query `Q`. -/
def ForwardSecrecyWith (Q : TestTracePredicates → Prop) : Prop :=
  ∀ tr : ExecTrace, tr.Reachable reachability →
    Q (mkTestTracePredicates tr)

theorem forwardSecrecyWith_real :
    ForwardSecrecyWith FSQueryP ↔ Security.ForwardSecrecy := by
  simp only [ForwardSecrecyWith, Security.ForwardSecrecy, fsQuery_iff_test]

theorem ForwardSecrecyWith.mono {Q Q' : TestTracePredicates → Prop}
    (h : ∀ P, Q P → Q' P) (hFS : ForwardSecrecyWith Q) : ForwardSecrecyWith Q' :=
  fun tr hR => h _ (hFS tr hR)

/-- `FSQueryP` parameterized by the chain-derivation relation `DC` and the message-key derivation
relations `DM_ck` and `DM_rk` in the chain-key and root-key disjuncts. -/
def FSQueryGen (DC DM_ck DM_rk : Bytes → Bytes → Prop) (P : TestTracePredicates) : Prop :=
  ∀ mk, P.MessageKey mk → P.AttackerKnows mk →
    P.Compromised mk ∨
    (∃ ck, DM_ck ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, DC rk ck ∧ DM_rk ck mk ∧ P.Compromised rk)

theorem fsQueryGen_real :
    FSQueryGen DerivesChain DerivesMsgKey DerivesMsgKey = FSQueryP :=
  rfl

/-! ## Mutated `FSQuery` predicates -/

def FSQuery_withoutMK (P : TestTracePredicates) : Prop :=
  ∀ mk, P.MessageKey mk → P.AttackerKnows mk →
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck) ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk)

def FSQuery_withoutCK (P : TestTracePredicates) : Prop :=
  ∀ mk, P.MessageKey mk → P.AttackerKnows mk →
    P.Compromised mk ∨
    (∃ rk ck, DerivesChain rk ck ∧ DerivesMsgKey ck mk ∧ P.Compromised rk)

def FSQuery_withoutRK (P : TestTracePredicates) : Prop :=
  ∀ mk, P.MessageKey mk → P.AttackerKnows mk →
    P.Compromised mk ∨
    (∃ ck, DerivesMsgKey ck mk ∧ P.Compromised ck)

/-- Direct chain creation from `rk`, omitting `RootDescends.step`. -/
def DerivesChainDirect (rk ck : Bytes) : Prop :=
  ∃ theirPk ourSk, ck = (createChain rk theirPk ourSk).2

/-- Chain derivation from a strict descendant `rk' ≠ rk` of `rk`, omitting `RootDescends.refl`. -/
def DerivesChainStrict (rk ck : Bytes) : Prop :=
  ∃ rk' theirPk ourSk, (RootDescends rk rk' ∧ rk' ≠ rk) ∧ ck = (createChain rk' theirPk ourSk).2

/-- Message-key derivation restricted to the initial step (`steps = 0`). -/
def DerivesMsgKey0 (ck mk : Bytes) : Prop :=
  mk = (kdfCk ck).2

abbrev FSQuery_chainDirect : TestTracePredicates → Prop :=
  FSQueryGen DerivesChainDirect DerivesMsgKey DerivesMsgKey

abbrev FSQuery_chainStrict : TestTracePredicates → Prop :=
  FSQueryGen DerivesChainStrict DerivesMsgKey DerivesMsgKey

abbrev FSQuery_ckSteps0 : TestTracePredicates → Prop :=
  FSQueryGen DerivesChain DerivesMsgKey0 DerivesMsgKey

abbrev FSQuery_rkSteps0 : TestTracePredicates → Prop :=
  FSQueryGen DerivesChain DerivesMsgKey DerivesMsgKey0

abbrev ForwardSecrecy_withoutMK : Prop := ForwardSecrecyWith FSQuery_withoutMK

abbrev ForwardSecrecy_withoutCK : Prop := ForwardSecrecyWith FSQuery_withoutCK

abbrev ForwardSecrecy_withoutRK : Prop := ForwardSecrecyWith FSQuery_withoutRK

abbrev ForwardSecrecy_chainDirect : Prop := ForwardSecrecyWith FSQuery_chainDirect

abbrev ForwardSecrecy_chainStrict : Prop := ForwardSecrecyWith FSQuery_chainStrict

abbrev ForwardSecrecy_ckSteps0 : Prop := ForwardSecrecyWith FSQuery_ckSteps0

abbrev ForwardSecrecy_rkSteps0 : Prop := ForwardSecrecyWith FSQuery_rkSteps0

/-! ## Mutant refutations -/

/-- Dropping `P.Compromised mk` from `FSQuery` is refuted on `trMK`, where only the skipped message
key `mkA1` is exposed. -/
theorem not_ForwardSecrecy_withoutMK : ¬ ForwardSecrecy_withoutMK := by
  intro hFS
  rcases hFS trMK trMK_reach mkA1 trMK_messageKey trMK_knows with
    ⟨ck, hDM, hComp⟩ | ⟨rk, ck, hDC, hDM, hComp⟩
  · have h1 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trMK_compromised hComp] at h1; omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trMK_compromised hComp] at h1; omega

/-- Dropping the chain-key disjunct from `FSQuery` is refuted on `trCK`, where exposing `stA0.cks`
reveals `mkA0` without exposing `mkA0` or any root key. -/
theorem not_ForwardSecrecy_withoutCK : ¬ ForwardSecrecy_withoutCK := by
  intro hFS
  rcases hFS trCK trCK_reach mkA0 trCK_messageKey trCK_knows with
    hComp | ⟨rk, ck, hDC, hDM, hComp⟩
  · have heq := congrArg saltDepth (trCK_compromised hComp)
    simp only [saltDepth_mkA0, saltDepth_stA0_cks] at heq; omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trCK_compromised hComp, saltDepth_stA0_cks] at h1
    rw [saltDepth_mkA0] at h2; omega

/-- Dropping the root-key disjunct from `FSQuery` is refuted on `trRKPost`, where exposing `stA0.rk`
and `dhsA` reveals `mkB0` on `stB2.cks` without exposing `mkB0` or `stB2.cks`. -/
theorem not_ForwardSecrecy_withoutRK : ¬ ForwardSecrecy_withoutRK := by
  intro hFS
  rcases hFS trRKPost trRKPost_reach mkB0 trRKPost_messageKey trRKPost_knows with
    hComp | ⟨ck, hDM, hComp⟩
  · have h0 := trRKPost_compromised_saltDepth hComp
    rw [saltDepth_mkB0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA0.rk (dhPk dhsA) dhsB1).2).2 := by
      rw [← stB2_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPost_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stA0_rk] at h0; omega

/-- Omitting `RootDescends.step` from `DerivesChain` in `FSQuery` is refuted on `trDC`, where
`mkDC` on `stA4.cks` is derived from the grandparent root `stA0.rk` via `dhsA` and `dhsB1`. -/
theorem not_ForwardSecrecy_chainDirect : ¬ ForwardSecrecy_chainDirect := by
  intro hFS
  rcases hFS trDC trDC_reach mkDC trDC_messageKey trDC_knows with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, ⟨pk, sk, hck⟩, hDM, hComp⟩
  · have h0 := trDC_compromised_saltDepth hComp
    rw [saltDepth_mkDC] at h0; omega
  · have hck : ck = stA4.cks := eq_of_derivesMsgKey_createChain_zero hDM
    have h0 := trDC_compromised_saltDepth hComp
    rw [hck, saltDepth_stA4_cks] at h0; omega
  · have hck' : ck = stA4.cks := eq_of_derivesMsgKey_createChain_zero hDM
    have h1 := congrArg saltDepth (hck'.symm.trans hck)
    have h0 := trDC_compromised_saltDepth hComp
    rw [saltDepth_stA4_cks, saltDepth_createChain_snd] at h1; omega

/-- Omitting `RootDescends.refl` from `DerivesChain` in `FSQuery` is refuted on `trRKPost`, where
the exposed root `stA0.rk` is the direct parent of `stB2.cks` and its ancestor `keys1.rk` is
uncompromised. -/
theorem not_ForwardSecrecy_chainStrict : ¬ ForwardSecrecy_chainStrict := by
  intro hFS
  rcases hFS trRKPost trRKPost_reach mkB0 trRKPost_messageKey trRKPost_knows with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, ⟨rk', pk, sk, ⟨hDesc, hne⟩, hck⟩, hDM, hComp⟩
  · have h0 := trRKPost_compromised_saltDepth hComp
    rw [saltDepth_mkB0] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA0.rk (dhPk dhsA) dhsB1).2).2 := by
      rw [← stB2_cks_eq]; exact hDM
    have hck := eq_of_derivesMsgKey_createChain_zero hDM'
    have h0 := trRKPost_compromised_saltDepth hComp
    rw [hck, saltDepth_createChain_snd, saltDepth_stA0_rk] at h0; omega
  · have hDM' : DerivesMsgKey ck (kdfCk (createChain stA0.rk (dhPk dhsA) dhsB1).2).2 := by
      rw [← stB2_cks_eq]; exact hDM
    have hck' := eq_of_derivesMsgKey_createChain_zero hDM'
    have hrk' : stA0.rk = rk' := createChain_snd_inj (hck'.symm.trans hck)
    subst hrk'
    rcases eq_or_rootDescends_of_createChain_fst hDesc with rfl | hDesc0
    · exact hne rfl
    · have hrk := eq_of_rootDescends_keys1_rk hDesc0
      subst hrk
      rcases trRKPost_compromised hComp with heq | heq
      · have h0 := congrArg saltDepth heq; simp at h0
      · have h0 := congrArg saltDepth heq; simp at h0

/-- Restricting `DerivesMsgKey` to `steps = 0` in the chain-key disjunct is refuted on `trCK2`,
where exposing `stA0.cks` reveals the second message key `mkA1` (`steps = 1`). -/
theorem not_ForwardSecrecy_ckSteps0 : ¬ ForwardSecrecy_ckSteps0 := by
  intro hFS
  rcases hFS trCK2 trCK2_reach mkA1 trCK2_messageKey trCK2_knows with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, hDC, hDM, hComp⟩
  · have h0 := congrArg saltDepth (trCK2_compromised hComp)
    simp only [saltDepth_mkA1, saltDepth_stA0_cks] at h0; omega
  · have h0 : saltDepth mkA1 = saltDepth (kdfCk ck).2 := congrArg saltDepth hDM
    rw [trCK2_compromised hComp, saltDepth_mkA1, saltDepth_kdfCk_snd, saltDepth_stA0_cks] at h0
    omega
  · have h1 := saltDepth_lt_of_derivesChain hDC
    have h2 := saltDepth_lt_of_derivesMsgKey hDM
    rw [trCK2_compromised hComp, saltDepth_stA0_cks] at h1
    rw [saltDepth_mkA1] at h2; omega

/-- Restricting `DerivesMsgKey` to `steps = 0` in the root-key disjunct is refuted on `trRKP2`,
where exposing `stA0.rk` and `dhsA` reveals Bob's second message key `mkB1` (`steps = 1`) on
`stB2.cks`. -/
theorem not_ForwardSecrecy_rkSteps0 : ¬ ForwardSecrecy_rkSteps0 := by
  intro hFS
  rcases hFS trRKP2 trRKP2_reach mkB1 trRKP2_messageKey trRKP2_knows with
    hComp | ⟨ck, hDM, hComp⟩ | ⟨rk, ck, ⟨rk', pk, sk, _, rfl⟩, hDM, _⟩
  · have h0 := trRKP2_compromised_saltDepth hComp
    rw [saltDepth_mkB1] at h0; omega
  · rcases hDM with ⟨steps, hmk⟩
    have h' : chainKeyAt stB2.cks 1 = chainKeyAt ck steps := kdfCk_snd_inj hmk
    have h0 := trRKP2_compromised_saltDepth hComp
    exact not_chainKeyAt_eq_of_root isChainRoot_stB2_cks
      (by rw [saltDepth_stB2_cks]; omega) h'
  · exact isChainRoot_createChain_snd rk' pk sk _ (kdfCk_snd_inj hDM).symm

end Symbolic.Proofs.Tests.Model.ExplanationTightness.TripleRatchetFS
