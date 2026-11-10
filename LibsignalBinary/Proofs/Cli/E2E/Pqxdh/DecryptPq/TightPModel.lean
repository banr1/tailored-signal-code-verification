/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel

/-!
# Pure Model & Tight-`onPanic` Helpers (`spqrDropPanic`)

Defines `spqrDropPanic` (clearing `S.recvPanics` to `false`) and proves
`model_spqrDropPanic_eq_of_ne_panic` when `(x.model C S uuidTryParse).1 ≠ .error .panic`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

/-- Copy of `S` with `recvPanics` cleared to `false`. Used to tighten non-panicking / alloc-only
seams where `(x.model C S uuidTryParse).1 ≠ .error .panic`. -/
def spqrDropPanic (S : SpqrModel) : SpqrModel :=
  { S with recvPanics := fun _ _ => false }

/-- Whenever `(x.model C S uuidTryParse).1 ≠ .error .panic`, `x.model` evaluates identically under
`spqrDropPanic S` and `S` (if execution reaches `spqr::recv`, `S.recvPanics` must have been `false`,
otherwise `model_of_recvPanics` would give `.error .panic`). -/
theorem model_spqrDropPanic_eq_of_ne_panic {C : Crypto} {S : SpqrModel} {x : TryDecryptGhost}
    (hne : (x.model C S uuidTryParse).1 ≠ .error .panic) :
    x.model C (spqrDropPanic S) uuidTryParse = x.model C S uuidTryParse := by
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk res0 st1 =>
    cases res0 with
    | error e =>
      rw [(model_of_fromSessionState_error (S := spqrDropPanic S) htr).1,
          (model_of_fromSessionState_error (S := S) htr).1]
    | ok tr =>
      cases herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
          (coinsOf x.rest)) tr.ratchet with
      | mk res1 r1 =>
        cases res1 with
        | error e =>
          rw [model_of_ensureReceiverChain_error (S := spqrDropPanic S) htr herc,
              model_of_ensureReceiverChain_error (S := S) htr herc]
        | ok ck =>
          cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck
              x.msg.counter x.msgType) r1 with
          | mk res2 r2 =>
            cases res2 with
            | error e =>
              rw [model_of_cmk_error (S := spqrDropPanic S) htr herc hcmk,
                  model_of_cmk_error (S := S) htr herc hcmk]
            | ok mkg =>
              have hpq : tr.pqrState = x.st.pqRatchetState := (fromSessionState_ok_inv htr).2.2.1
              have hnp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet = false := by
                cases hp : S.recvPanics x.st.pqRatchetState x.msg.pqRatchet
                · rfl
                · exact (hne (CryptoVerification.LibsignalTripleRatchet.Decrypt.Model.model_of_recvPanics
                    htr herc hcmk hp)).elim
              conv_lhs =>
                rw [model_unfold, htr]
                dsimp only
                unfold TripleRatchet.decrypt
                rw [exec_bind, onRatchet_eq, herc]
                dsimp only
                rw [exec_bind, onRatchet_eq]
                dsimp only
                rw [hcmk]
                dsimp only
                rw [exec_bind, exec_get]
                dsimp only [SpqrModel.spqr, spqrDropPanic]
                simp only [hpq, Bool.false_eq_true, ↓reduceIte]
              conv_rhs =>
                rw [model_unfold, htr]
                dsimp only
                unfold TripleRatchet.decrypt
                rw [exec_bind, onRatchet_eq, herc]
                dsimp only
                rw [exec_bind, onRatchet_eq]
                dsimp only
                rw [hcmk]
                dsimp only
                rw [exec_bind, exec_get]
                dsimp only [SpqrModel.spqr]
                simp only [hpq, hnp, Bool.false_eq_true, ↓reduceIte]

theorem onPanicTight_drop_frame {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R := by
  dsimp only [tryDecryptOnPanicTight] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

theorem onPanicTight_of_cmk_panic {C : Crypto} {S : SpqrModel}
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

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
