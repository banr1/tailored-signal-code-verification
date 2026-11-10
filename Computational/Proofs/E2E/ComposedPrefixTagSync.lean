/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.ComposedPrefixHelpers
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCoupling
import VCVio.EvalDist.Monad.Basic

/-!
# Helpers for tag-synchronized lazy `KeyInd` stepping

**Checked by Lean.**

List lookup and `StateT` lifting lemmas used by `ComposedPrefixSlot`.
-/

@[expose] public section

open scoped ENNReal
open OracleComp OracleSpec MeasureTheory
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E CryptoVerification.E2E.Prefix
open Proofs.SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security Proofs.SignalPqxdh.Security

namespace CryptoVerification.E2E

@[simp]
private theorem stateT_run_lift {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (StateT.lift mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

@[simp]
private theorem stateT_run_liftM {M : Type → Type} [Monad M] {σ α : Type}
    (mx : M α) (s : σ) :
    (liftM mx : StateT σ M α).run s = (mx >>= fun x => pure (x, s)) := rfl

theorem list_any_map_cond_fst {α β : Type} [BEq α]
    (l : List (α × β)) (k₀ : α) (f : β → β) (p : α → Bool) :
    (l.map (fun (k, v) => if k == k₀ then (k, f v) else (k, v))).any (fun (k, _) => p k) =
      l.any (fun (k, _) => p k) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.any_cons]
    split_ifs <;> simp [ih]

theorem eq_of_mem_of_nodup_map {α β : Type} (f : α → β) {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : f x = f y) :
    x = y := by
  induction l with
  | nil => cases hx
  | cons a tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact False.elim (hnd.1 (hxy ▸ List.mem_map_of_mem hy'))
    · exact False.elim (hnd.1 (hxy.symm ▸ List.mem_map_of_mem hx'))
    · exact ih hnd.2 hx' hy'

end CryptoVerification.E2E
