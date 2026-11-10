/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Chains
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.CryptoGames.SM.Theorem7Proof
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Epoch trace for session correctness

**Checked by Lean.**

Defines `EpochTrace`, tracking root keys, chain keys, and distinct ratchet public keys across
Double Ratchet epochs for `libsignal_corr`.
-/

@[expose] public section

namespace CryptoGames.LibsignalSM.Proofs.Correctness

open CryptoGames CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.LibsignalAead CryptoGames.CBC
open CryptoGames.SM CryptoGames.SM.Construction CryptoGames.CKA

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

theorem sendsIn_other_eq_not (Q : Party) (t : ℕ) :
    Q.other.sendsIn t = !Q.sendsIn t := by
  cases Q <;> dsimp only [Party.other, Party.sendsIn]
  · by_cases h : t % 2 = 1
    · have h0 : t % 2 ≠ 0 := by omega
      simp [h, h0]
    · have h0 : t % 2 = 0 := by omega
      simp [h, h0]
  · by_cases h : t % 2 = 0
    · have h1 : t % 2 ≠ 1 := by omega
      simp [h, h1]
    · have h1 : t % 2 = 1 := by omega
      simp [h, h1]

structure EpochTrace {Pt : Type} (F : ShaCompress) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) where
  tFront : ℕ
  rk : ℕ → BitVec 256
  ck : ℕ → BitVec 256
  x : ℕ → BitVec 256
  hFront_pos : 1 ≤ tFront
  hStep : ∀ e, e < tFront →
    rootKdf F (rk e) (encPt (Dh.dh (x (e + 1)) (Dh.dh (x e) Dh.base))) = (rk (e + 1), ck (e + 1))
  hDistinct : ∀ e₁ ≤ tFront, ∀ e₂ ≤ tFront,
    Dh.dh (x e₁) Dh.base = Dh.dh (x e₂) Dh.base → e₁ = e₂

namespace EpochTrace

variable {Pt : Type} {F : ShaCompress} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → List (BitVec 8)}

def T (tr : EpochTrace F Dh encPt) (e : ℕ) : Pt :=
  Dh.dh (tr.x e) Dh.base

theorem T_ne_zero [Zero Pt] {C : Crypto} {encT : Pt → PublicKey}
    (hX : X25519RealizesDh C Dh encPt encT) (tr : EpochTrace F Dh encPt) (e : ℕ) :
    tr.T e ≠ 0 := by
  have : DecidableEq Pt := Classical.decEq Pt
  exact dh_base_ne_zero hX (tr.x e)

theorem rootKdf_step_symm (hDh : Dh.Commutes) (tr : EpochTrace F Dh encPt)
    {e : ℕ} (he : e < tr.tFront) :
    rootKdf F (tr.rk e) (encPt (Dh.dh (tr.x e) (tr.T (e + 1)))) =
      (tr.rk (e + 1), tr.ck (e + 1)) := by
  dsimp only [T]
  rw [hDh (tr.x e) (tr.x (e + 1))]
  exact tr.hStep e he

end EpochTrace

section InvariantLemmas

variable {Pt PQ PQC : Type} [Zero Pt] [Inhabited PQ]
  {P : Params PQ PQC} {ℓ qep n : ℕ} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey}

theorem getD_eq_getElem {α : Type} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d = l[k] := by
  simp [List.getD, List.getElem?_eq_getElem hk]

end InvariantLemmas

end CryptoGames.LibsignalSM.Proofs.Correctness
