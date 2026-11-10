/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndShcrWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeSigWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacWire
public import Computational.Proofs.ReductionDsl.Size
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
public import Computational.Proofs.SignalPqxdh.Security.Reductions
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.Headline
import Computational.Proofs.SignalPqxdh.Security.AuthAssembly
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCoupling
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCk
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpaProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacProofs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkEval

/-!
# Atomic-Signature PQXDH Reduction Bundles and Bounds

Constructs the `pqAtomicOps` / `pqAtomicSamplers` costed reduction families `pqxdhKeyIndCostedSims`
and `pqxdhAuthCostedSims` (bundled as `pqxdhReds`), establishes their syntactic cost, query, and
block-size bounds and semantic query bounds, and equates their game advantages with the shallow
simulators.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.SignalPqxdh.Security

/-! ## Size honesty and budget comparisons -/

section SizeAndBudgets

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.ReductionDsl.AtomicSizeHonest

theorem valFits_iff_fits {S : Sig} (B : ℕ) :
    ∀ (t : Ty S) (x : t.denote), ValFits B t x ↔ t.Fits B x
  | .base _, _ => Iff.rfl
  | .unit, _ => Iff.rfl
  | .bool, _ => Iff.rfl
  | .nat, _ => Iff.rfl
  | .opt _, none => Iff.rfl
  | .opt t, some a => valFits_iff_fits B t a
  | .prod t u, x => and_congr (valFits_iff_fits B t x.1) (valFits_iff_fits B u x.2)
  | .sum t _, .inl a => valFits_iff_fits B t a
  | .sum _ u, .inr b => valFits_iff_fits B u b
  | .list t, _ => and_congr Iff.rfl
      (forall_congr' fun x => imp_congr_right fun _ => valFits_iff_fits B t x)
  | .tbl t, m => forall_congr' fun i => valFits_iff_fits B t (m i)

theorem pqOpsSizeHonest : PqOpsSizeHonest pqAtomicOps :=
  pqAtomicOps_sizeHonest

theorem pqSampSizeHonest : PqSampSizeHonest pqAtomicSamplers :=
  pqAtomicSamplers_sizeHonest

theorem stepCostBudget_le_quadratic_old (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤
      2 ^ 16 * (b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hMd : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have hMs : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have hLd : Nat.log 2 S.N_dh ≤ S.N_dh := Nat.log_le_self 2 S.N_dh
  have hLs : Nat.log 2 S.N_sess_tot ≤ S.N_sess_tot := Nat.log_le_self 2 S.N_sess_tot
  have h1 : 2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) ≤
      2 ^ 15 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add hMd hMs)
  have h2 : 2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) ≤
      2 ^ 10 * (b.q_total + 1) * (S.N_dh + S.N_sess_tot) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add hLd hLs)
  have h3 : 2 ^ 11 * min b.q_total S.N_dh ^ 2 ≤ 2 ^ 11 * S.N_dh ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hMd 2)
  have h4 : 2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot ≤
      2 ^ 8 * S.N_dh * S.N_sess_tot :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hMd) hMs
  nlinarith [Nat.zero_le (b.q_total * S.N_dh), Nat.zero_le (b.q_total * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

theorem stepCostBudget_le_old (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤
      2 ^ 18 * (b.q_total + 1) *
        (b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 := by
  have hQ := stepCostBudget_le_quadratic_old S b
  have hU : b.q_total + S.N_dh + S.N_sess_tot + 1 ≤
      b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1 := by omega
  have hU2 : (b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 ≤
      (b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 :=
    Nat.pow_le_pow_left hU 2
  have h1 : 2 ^ 16 ≤ 2 ^ 18 * (b.q_total + 1) := by omega
  exact le_trans hQ (Nat.mul_le_mul h1 hU2)

theorem outputSizeBudget_le_old (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    outputSizeBudget S b ℓ ≤
      2 * (2 ^ 18 * (b.q_total + 1) *
        (b.q_ro + b.q_roRoot + b.q_total + S.N_dh + S.N_sess_tot + 1) ^ 2 + b.q_total + 1) *
          (ℓ + 1) := by
  unfold outputSizeBudget
  have hStep := stepCostBudget_le_old S b
  nlinarith

end SizeAndBudgets

/-! ## Unsupported-query bounds for `KeyInd` programs -/

section KeyIndUnsupported

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqSamplers
  eufCmaSignOracle gapDhDdhOracle sigAndDdhOracle
open Computational.Proofs.SignalPqxdh.AtomicLift

def zPrimWS : SignalPqxdh.LegacyCosted.pqPrimIface.smp.Samp → ℕ := fun _ => 0
def zEufW : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.Tag → ℕ := tlEufCmaKeyInd.unsupportedW
def zEufWS : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.smp.Samp → ℕ := fun _ => 0
def zGapDhW : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW
def zGapDhWS : SignalPqxdh.LegacyCosted.pqGapDhIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem sBool_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem sBytes32_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem sRandom64_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem sDrKey96_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem sIndex_unsupported (N : ℕ) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[simp] theorem qX25519_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qX25519Base_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qPow8_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qIsCanonical_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qSigPkGen_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qSigSign_unsupported (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32)
        (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qSigVerify_unsupported (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32)
        (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qKemKeyGen_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 64)) :
    (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qKemEncaps_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 1568) (SignalPqxdh.LegacyCosted.B 32))) :
    (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qKemDecaps_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 3168) (SignalPqxdh.LegacyCosted.B 1568))) :
    (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[simp] theorem qHkdfDerive96_unsupported (w : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[simp] theorem liftBase_eufCma_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (liftBase c).queries zEufW zEufWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  induction c with
  | query g e => rfl
  | sample s e => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] theorem qChalSign_unsupported (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (qChalSign m e).queries zEufW zEufWS = 0 := rfl

@[simp] theorem gPrim_gapDh_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold gPrim
  induction c with
  | query g e => rfl
  | sample s e => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] theorem ddhQ_gapDh_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (x y z : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (ddhQ x y z).queries zGapDhW zGapDhWS = 0 := rfl

@[simp] theorem findHonestC_unsupported (S : Setup) (K : Nat) {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queries]

@[simp] theorem isAdvRegC_unsupported (K : Nat) {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isAdvRegC, bindV, Comp.queries]

@[simp] theorem isGameSpkC_unsupported (S : Setup) (K : Nat) {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]

@[simp] theorem isGameOpkC_unsupported (S : Setup) (K : Nat) {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]

@[simp] theorem koskBundleOkC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskBundleOkC, bindV, caseOptV, Comp.queries]

@[simp] theorem koskSenderOkC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskSenderOkC, letV, bindV, Comp.queries]

@[simp] theorem resolveSigPkC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [resolveSigPkC, letV, bindV, Comp.queries]

@[simp] theorem honestPeerC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [honestPeerC, bindV, Comp.queries]

@[simp] theorem checkProvC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [checkProvC, bindV, letV, caseOptV, anyMV, Comp.queries]

@[simp] theorem partnerC_unsupported {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[simp] theorem recordRespC_unsupported (S : Setup) (K : Nat)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [recordRespC, letV, bindV, caseOptV, findMV, Comp.queries]

@[simp] theorem hkdfOrRoC_true_unsupported (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (sec : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 192)) :
    (hkdfOrRoC K true st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.queries]

@[simp] theorem hkdfOrRoC_false_unsupported (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (sec : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 192)) :
    (hkdfOrRoC K false st sec).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [hkdfOrRoC, letV, bindV, Comp.queries]

@[simp] theorem acceptKeysC_unsupported {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (inp : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl

@[simp] theorem initFinishC_true_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ SignalPqxdh.LegacyCosted.bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) true S K st sid bu uE ekSk sc).queries
      keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initFinishC, bindV, letV, caseOptV, findMV, Comp.queries]

@[simp] theorem initFinishC_false_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ SignalPqxdh.LegacyCosted.bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) false S K st sid bu uE ekSk sc).queries
      keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [initFinishC, bindV, letV, caseOptV, findMV, Comp.queries]

@[simp] theorem preCheckC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ SignalPqxdh.LegacyCosted.sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [preCheckC, caseOptV, bindV, Comp.queries]

@[simp] theorem checkSigsC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [checkSigsC, bindV, Comp.queries]

@[simp] theorem extractC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ sigStTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (extractC (Δ := Δ) S K s bu).queries zEufW zEufWS = 0 := by
  simp [extractC, bindV, letV, Comp.queries]

@[simp] theorem onGame_unsupported {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ sigStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface
        (keyIndStateTy :: Δ) RS) :
    (onGame (Δ := Δ) s br).queries zEufW zEufWS =
      (br .zero).queries keyIndUnsupportedPrimW zPrimWS := by
  simp [Security.ReductionDsl.KeyInd.onGame, bindV, letV, Comp.queries]

@[simp] theorem onBase_unsupported {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface
        (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries keyIndUnsupportedPrimW zPrimWS =
      (br .zero).queries keyIndUnsupportedPrimW zPrimWS := by
  simp [onBase, bindV, letV, Comp.queries]

theorem sigKeyIndProg_init_unsupported (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).init.queries tlEufCmaKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigKeyIndProg useRo S K).init.queries zEufW zEufWS = 0
  simp [sigKeyIndProg, bindV, Comp.queries]

theorem sigKeyIndProg_finish_unsupported (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).finish.queries tlEufCmaKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

private theorem sigHandleC_false_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) false S K s q).queries zEufW zEufWS = 0 := by
  simp [sigHandleC, sigInitPrinB, sigCorruptB, sigGenSpkB, sigInitiateB,
    initPrinB, corruptB, genSpkB, genOpkB, initiateOpkB, initiateNoOpkB, initiateC,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB,
    bindV, letV, caseOptV, caseSumV, Comp.queries]

private theorem sigHandleC_true_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (sigHandleC (Δ := Δ) true S K s q).queries zEufW zEufWS = 0 := by
  simp [sigHandleC, sigInitPrinB, sigCorruptB, sigGenSpkB, sigInitiateB,
    initPrinB, corruptB, genSpkB, genOpkB, initiateOpkB, initiateNoOpkB, initiateC,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB,
    bindV, letV, caseOptV, caseSumV, Comp.queries]

theorem sigKeyIndProg_handle_unsupported (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).handle.queries tlEufCmaKeyInd.unsupportedW (fun _ => 0) = 0 := by
  cases useRo
  · exact sigHandleC_false_unsupported S K (Γ₁ := [sigStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [sigStTy, keyIndQueryTy]) .zero .zero
  · exact sigHandleC_true_unsupported S K (Γ₁ := [sigStTy, keyIndQueryTy])
      (Γ₂ := [keyIndQueryTy]) (Δ := [sigStTy, keyIndQueryTy]) .zero .zero

theorem shcrKeyIndProg_init_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).init.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyIndProg S Q K).init.queries keyIndUnsupportedPrimW zPrimWS = 0
  by_cases h : S.N_spk_tot = 0 ∨ S.N_send_tot = 0 <;>
    simp [shcrKeyIndProg, h, bindV, Comp.queries]

theorem shcrKeyIndProg_chDone_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).chDone.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

theorem shcrKeyIndProg_finish_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyIndProg S Q K).finish.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyIndProg, shcrExtractC, bindV, findMV, Comp.queries]

theorem shcrKeyIndProg_resume_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (shcrKeyIndProg S Q K).resume.queries keyIndUnsupportedPrimW zPrimWS = 0
  simp [shcrKeyIndProg, shcrResumeC, bindV, letV, Comp.queries]

@[simp] theorem shcrPostC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [shcrPostC, shcrGenSpkB, shcrInitiateC, shcrAcceptB,
    initPrinB, corruptB, genSpkB, genOpkB,
    acceptOpkB, acceptNoOpkB, testB, revealB, roB, revealDhB, registerB, revealSpkB,
    bindV, letV, caseOptV, caseSumV, Comp.queries]

theorem shcrKeyIndProg_handlePost_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrPostC_unsupported S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

private theorem shcrPreC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPreC (Δ := Δ) S K s q).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  have hPost := shcrPostC_unsupported S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  simp [shcrPreC, pauseCheckC, tryPauseC, hPost, bindV, letV, caseOptV, caseSumV, Comp.queries]

theorem shcrKeyIndProg_handlePre_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrPreC_unsupported S K (Γ₁ := [shcrStTy, keyIndQueryTy])
    (Γ₂ := [keyIndQueryTy]) (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero

@[simp] theorem koskSenderOkPowsC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskSenderOkPowsC, letV, bindV, Comp.queries]

@[simp] theorem koskBundleOkPowsC_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [koskBundleOkPowsC, letV, bindV, caseOptV, Comp.queries]

@[simp] theorem lookupSpkSkC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (spkPk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [lookupSpkSkC, letV, bindV, findMV, Comp.queries]

@[simp] theorem chooseRespRandC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGapDhW zGapDhWS = 0 := by
  simp [chooseRespRandC, bindV, caseOptV, findMV, Comp.queries]

@[simp] theorem chooseInitRandC_unsupported (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGapDhW zGapDhWS = 0 := by
  simp [chooseInitRandC, bindV, caseOptV, findMV, Comp.queries]

@[simp] theorem mkSecretPosC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (z : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkSecretPosC z).queries zGapDhW zGapDhWS = 0 := by
  simp [mkSecretPosC, letV, bindV, Comp.queries]

@[simp] theorem mkPairPosC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (pk1 pk2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkPairPosC pk1 pk2).queries zGapDhW zGapDhWS = 0 := by
  simp [mkPairPosC, letV, bindV, Comp.queries]

@[simp] theorem computePosC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (sk1 sk2 pk1 pk2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queries zGapDhW zGapDhWS = 0 := by
  simp [computePosC, bindV, Comp.queries]

@[simp] theorem computeOptPosInitC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (sk1 pk1 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32))
    (opkB? : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.opt (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGapDhW zGapDhWS = 0 := by
  simp [computeOptPosInitC, letV, caseOptV, bindV, Comp.queries]

@[simp] theorem ddhEqC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p1 p2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries zGapDhW zGapDhWS = 0 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]

@[simp] theorem ddhEqOptC_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p1? p2? : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries zGapDhW zGapDhWS = 0 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]

@[simp] theorem entryMatchesC_unsupported {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGapDhW zGapDhWS = 0 := by
  simp [entryMatchesC, bindV, Comp.queries]

@[simp] theorem fgPatchC_unsupported (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGapDhW zGapDhWS = 0 := by
  simp [fgPatchC, findMV, caseOptV, Comp.queries]

@[simp] theorem wrapBase_unsupported {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).queries zGapDhW zGapDhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  simp [wrapBase, bindV, Comp.queries]

@[simp] theorem wrapSim_unsupported {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ
      (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).queries zGapDhW zGapDhWS =
      c.queries zGapDhW zGapDhWS := by
  simp [wrapSim, bindV, Comp.queries]

theorem fgKeyIndGapDhProg_init_unsupported (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (fgKeyIndGapDhProg S K).init.queries zGapDhW zGapDhWS = 0
  simp [fgKeyIndGapDhProg, initAdv4, initParamsFlat, initParamsDh, initParamsIk, initParamsOpk,
    letV, bindV, Comp.queries]

theorem gdhHandle_unsupported (S : Setup) (K : Nat) :
    (gdhHandle S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhHandle S K).queries zGapDhW zGapDhWS = 0
  simp [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB, genOpkGdhB,
    initiateGdhB, finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

theorem gdhFinish_unsupported (S : Setup) (K : Nat) :
    (gdhFinish S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhFinish S K).queries zGapDhW zGapDhWS = 0
  simp [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, Comp.queries]

@[simp] private theorem wrapBase2_unsupported {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries zGapDhW zGapDhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  simp [wrapBase2, bindV, Comp.queries]

@[simp] private theorem wrapSim2_unsupported {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ
      (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries zGapDhW zGapDhWS =
      c.queries zGapDhW zGapDhWS := by
  simp [wrapSim2, bindV, Comp.queries]

@[simp] private theorem bernoulliRatioGdhC_unsupported
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries zGapDhW zGapDhWS = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, Comp.queries]

private theorem chooseArm2C_unsupported
    {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {α : Ty SignalPqxdh.LegacyCosted.pqSig}
    [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ'],
      Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ' α)
    (h1 : ∀ {Δ'} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0)
    (h2 : ∀ {Δ'} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries zGapDhW zGapDhWS = 0 := by
  unfold chooseArm2C
  split_ifs
  · exact h2
  · exact h1
  · simp [bindV, Comp.queries, h1, h2]

@[simp] private theorem samplePrin2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (samplePrin2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold samplePrin2C; split_ifs <;> simp [bindV, Comp.queries]

@[simp] private theorem sampleSpkPair2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleSpkPair2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold sampleSpkPair2C; split_ifs <;> simp [bindV, Comp.queries]

@[simp] private theorem sampleOpkTriple2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleOpkTriple2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold sampleOpkTriple2C; split_ifs <;> simp [bindV, Comp.queries]

@[simp] private theorem sampleSendOpkTarget2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleSendOpkTarget2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]

@[simp] private theorem sampleSendNoOpkTarget2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleSendNoOpkTarget2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]

@[simp] private theorem sampleSendTarget2C_unsupported (S : Setup)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sampleSendTarget2C S (Δ := Δ)).queries zGapDhW zGapDhWS = 0 := by
  unfold sampleSendTarget2C
  split_ifs
  · rfl
  · exact chooseArm2C_unsupported _ _ _ _ (by simp) (by simp)

private theorem fgKeyIndGapDh2Prog_init_unsupported (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (fgKeyIndGapDh2Prog S K).init.queries zGapDhW zGapDhWS = 0
  have hP : ∀ {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
      (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))),
      (initParams2C S (Δ := Δ) uv).queries zGapDhW zGapDhWS = 0 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · rfl
    · refine chooseArm2C_unsupported _ _ _ _ ?_ ?_
      · exact chooseArm2C_unsupported _ _ _ _
          (by simp [bindV, Comp.queries]) (by simp [bindV, Comp.queries])
      · exact chooseArm2C_unsupported _ _ _ _
          (by simp [bindV, Comp.queries]) (by simp [bindV, Comp.queries])
  simp [fgKeyIndGapDh2Prog, initAdv4_2, letV, bindV, Comp.queries, hP]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0
  simp [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

private theorem gdhFinish2_unsupported (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhFinish2 S K).queries zGapDhW zGapDhWS = 0
  simp [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, Comp.queries]


end KeyIndUnsupported

section KeyIndSizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)

@[simp] private theorem hl_F_X25519_length : F_X25519.length = 32 := by decide

@[simp] private theorem ki_liftBase_litSize {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftBase (C := C) c) = compLitSize c := by
  induction c <;> simp_all [liftBase, compLitSize, pqChalIface, pqPrimIface]

@[simp] private theorem ki_liftBase_euf_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqxdhEufCmaIface) (liftBase c) = compLitSize c := ki_liftBase_litSize c

@[simp] private theorem ki_gPrim_litSize {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (gPrim c) = compLitSize c := ki_liftBase_litSize c

@[simp] private theorem ki_liftBase_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem ki_liftBase_euf_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqxdhEufCmaIface) (liftBase c) = c.size := ki_liftBase_size c

@[simp] private theorem ki_gPrim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).size = c.size := ki_liftBase_size c

section KiAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[simp] private theorem ki_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem ki_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .zero).size + 1 := rfl
@[simp] private theorem ki_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .zero).size + 1 := rfl
@[simp] private theorem ki_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem ki_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] private theorem ki_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).size =
      xs.size + init.size + (f .zero (.succ .zero)).size + bits K + 1 := rfl
@[simp] private theorem ki_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl
@[simp] private theorem ki_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem ki_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] private theorem ki_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl
@[simp] private theorem ki_litB_size (w : ℕ+) (bs : Bytes) : (litB w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_catB_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (catB a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ki_consB_size {w : ℕ+} (b : UInt8) (e : Expr pqxdhOps Γ (B w)) :
    (consB b e).size = e.size + 1 := rfl
@[simp] private theorem ki_widenB_size (w d : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (widenB w d e).size = e.size + 1 := rfl
@[simp] private theorem ki_takeKB_size (w k : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (takeKB w k e).size = e.size + 1 := rfl
@[simp] private theorem ki_dropB_size {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (e : Expr pqxdhOps Γ (B w)) :
    (dropB n e).size = n.size + e.size + 2 := rfl
@[simp] private theorem ki_lenB_size {w : ℕ+} (e : Expr pqxdhOps Γ (B w)) : (lenB e).size = e.size + 1 := rfl
@[simp] private theorem ki_eqB_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (eqB a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ki_u32OfNat_size (e : Expr pqxdhOps Γ .nat) : (u32OfNat e).size = e.size + 1 := rfl
@[simp] private theorem ki_eqU32_size (a b : Expr pqxdhOps Γ U32) :
    (eqU32 a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ki_sBool_size : (sBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_sBytes32_size : (sBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_sRandom64_size : (sRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_sDrKey96_size : (sDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_sIndex_size (N : ℕ) : (sIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ki_qX25519_size (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).size = e.size + 1 := rfl
@[simp] private theorem ki_qX25519Base_size (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).size = e.size + 1 := rfl
@[simp] private theorem ki_qIsCanonical_size (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).size = e.size + 1 := rfl
@[simp] private theorem ki_qPow8_size (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).size = e.size + 1 := rfl
@[simp] private theorem ki_qSigPkGen_size (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).size = e.size + 1 := rfl
@[simp] private theorem ki_qSigSign_size (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).size = e.size + 1 := rfl
@[simp] private theorem ki_qSigVerify_size (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).size = e.size + 1 := rfl
@[simp] private theorem ki_qKemKeyGen_size (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).size = e.size + 1 := rfl
@[simp] private theorem ki_qKemEncaps_size (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).size = e.size + 1 := rfl
@[simp] private theorem ki_qKemDecaps_size (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).size = e.size + 1 := rfl
@[simp] private theorem ki_qHkdfDerive96_size (w : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (qHkdfDerive96 w e).size = e.size + 1 := rfl
@[simp] private theorem ki_qChalSign_size (m : ℕ+) (e : Expr pqxdhOps Γ (B m)) :
    (qChalSign m e).size = e.size + 1 := rfl
@[simp] private theorem ki_ddhQ_size (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).size = x.size + (y.size + z.size + 1) + 2 := rfl
@[simp] private theorem ki_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem ki_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) : (encKEM e).size = e.size + 1 := rfl

end KiAtomicSizeSimp

private theorem ki_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem ki_bits_le_of_le_four_mul_sq {x N : ℕ} (h : x ≤ 4 * (N * N)) :
    bits x ≤ 2 * bits N + 3 := by
  have h1 := ki_bits_mono h
  have h2 := bits_mul 4 (N * N)
  have h3 := bits_mul N N
  have h4 : bits 4 = 3 := by decide
  omega

private theorem ki_nRecv_le_dh (S : Setup) : nRecv S ≤ S.N_dh := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hspk : S.N_spk_tot = S.N_id * S.N_recv := rfl
  unfold nRecv
  split_ifs with h0
  · omega
  · have hpos : 1 ≤ S.N_id := by omega
    have hle : S.N_recv ≤ S.N_id * S.N_recv := by simpa using Nat.mul_le_mul_right S.N_recv hpos
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_sigKeyIndProg_handle_size_le (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).handle.size ≤ 100 * bits K + 11800 := by
  cases useRo <;> {
    dsimp only [sigKeyIndProg]
    simp (config := { maxSteps := 1000000 }) only [
      sigHandleC, sigInitPrinB, sigCorruptB, sigGenSpkB, sigInitiateB,
      Security.ReductionDsl.KeyInd.onGame, extractC, widenEC,
      sgGame, sgTarget, sgPk, sgForgery, sgBudget, sgUpd,
      initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
      initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
      testB, revealB, roB, revealDhB, registerB, revealSpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
      aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
      qK, qJ, qO, qHdr, qKJO,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd,
      reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
      reTested, reRevealed, reMk, reUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
      orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
      buildSecretsE, eLet2,
      ki_liftBase_size, ki_liftBase_euf_size, liftBase,
      v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
      sBool, sBytes32, sRandom64, sDrKey96, sIndex,
      qX25519, qX25519Base, qIsCanonical, qPow8,
      qSigPkGen, qSigSign, qSigVerify,
      qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
      qChalSign, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := rfl
    have hb1 : bits 1 = 1 := rfl
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    have : bits (min K S.N_spk_tot) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
    have : bits (min K S.N_dh) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
    have : bits (min K S.N_sess_tot) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
    omega
  }

set_option linter.unusedSimpArgs false in
private theorem ki_sigKeyIndProg_size_le_clamped (useRo : Bool) (S : Setup) (K : Nat) :
    (sigKeyIndProg useRo S K).size ≤ 101 * bits K + 12000 := by
  have hH := ki_sigKeyIndProg_handle_size_le useRo S K
  have hI : (sigKeyIndProg useRo S K).init.size ≤ bits K + 150 := by
    dsimp only [sigKeyIndProg]
    simp only [emptyStE, ki_liftBase_size, ki_liftBase_euf_size, liftBase,
      v, bindV, sBool, sIndex, Comp.size, Expr.size]
    have hb0 : bits 0 = 1 := rfl
    have : bits (min K S.N_spk_tot) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
    omega
  have hF : (sigKeyIndProg useRo S K).finish.size ≤ 40 := by
    dsimp only [sigKeyIndProg]
    split_ifs <;> simp [sgForgery, ki_eCaseOpt_size, ki_litB_size, ki_v_size, Comp.size, Expr.size]
  change (sigKeyIndProg useRo S K).init.size + (sigKeyIndProg useRo S K).handle.size +
    (sigKeyIndProg useRo S K).finish.size ≤ _
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_sigKeyIndProg_litSize_le (useRo : Bool) (S : Setup) (K : Nat) :
    red1LitSize (sigKeyIndProg useRo S K) ≤ 20000 := by
  cases useRo <;> {
    dsimp only [sigKeyIndProg, red1LitSize]
    simp (config := { maxSteps := 1000000 }) only [
      sigHandleC, sigInitPrinB, sigCorruptB, sigGenSpkB, sigInitiateB,
      Security.ReductionDsl.KeyInd.onGame, extractC, widenEC,
      sgGame, sgTarget, sgPk, sgForgery, sgBudget, sgUpd,
      initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
      initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
      testB, revealB, roB, revealDhB, registerB, revealSpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
      aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
      qK, qJ, qO, qHdr, qKJO,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, sbSpkSig, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd,
      reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
      reTested, reRevealed, reMk, reUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
      orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
      buildSecretsE, eLet2,
      ki_liftBase_litSize, ki_liftBase_euf_litSize, liftBase,
      v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
      sBool, sBytes32, sRandom64, sDrKey96, sIndex,
      qX25519, qX25519Base, qIsCanonical, qPow8,
      qSigPkGen, qSigSign, qSigVerify,
      qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
      qChalSign, encEC, encKEM,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
      Nat.add_zero, Nat.zero_add,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    split_ifs <;> simp only [exprLitSize, pqOpLitSize, List.length_nil, Nat.add_zero, Nat.zero_add] <;> omega
  }

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_shcrPostC_size_bounds (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPostC (Δ := Δ) S K s q).size ≤
      53 * bits K + 35 * bits (min K S.N_dh) + 2 * bits (min K S.N_sess_tot) + 11600 := by
  simp (config := { maxSteps := 1000000 }) only [
    shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC, shcrAcceptB, onBase, shcrFinE,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
    isNoneRespE,
    initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
    initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
    testB, revealB, roB, revealDhB, registerB, revealSpkB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
    qK, qJ, qO, qHdr, qKJO,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
    seTested, seRevealed, seMk, seUpd,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reRevealed, reMk, reUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
    orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
    buildSecretsE, eLet2,
    v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBool, sBytes32, sRandom64, sDrKey96, sIndex,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
    encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_shcrKeyIndProg_size_bounds (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).size ≤
      bits Q + 120 * bits K + 75 * bits (min K S.N_dh) + 5 * bits (min K S.N_sess_tot) + 26000 := by
  have hIni : (shcrKeyIndProg S Q K).init.size ≤ 60 := by
    dsimp only [shcrKeyIndProg]
    split_ifs <;> {
      simp only [scMk, emptyStE, v, bindV, sBool, sIndex, Comp.size, Expr.size]
      have hb0 : bits 0 = 1 := rfl
      omega
    }
  have hPre : (shcrKeyIndProg S Q K).handlePre.size ≤
      64 * bits K + 35 * bits (min K S.N_dh) + 2 * bits (min K S.N_sess_tot) + 12600 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrPreC, pauseCheckC, tryPauseC, shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC,
      shcrAcceptB, shcrResumeC, shcrExtractC, onBase, shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      isNoneRespE,
      initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
      initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
      testB, revealB, roB, revealDhB, registerB, revealSpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
      aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
      qK, qJ, qO, qHdr, qKJO,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd,
      reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
      reTested, reRevealed, reMk, reUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
      orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
      buildSecretsE, eLet2,
      v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
      sBool, sBytes32, sRandom64, sDrKey96, sIndex,
      qX25519, qX25519Base, qIsCanonical, qPow8,
      qSigPkGen, qSigSign, qSigVerify,
      qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
      encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := rfl
    have hb1 : bits 1 = 1 := rfl
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    omega
  have hPost : (shcrKeyIndProg S Q K).handlePost.size ≤
      53 * bits K + 35 * bits (min K S.N_dh) + 2 * bits (min K S.N_sess_tot) + 11600 := by
    dsimp only [shcrKeyIndProg, keyIndCodec]
    exact ki_shcrPostC_size_bounds S K _ _
  have hDone : (shcrKeyIndProg S Q K).chDone.size ≤ 20 := by
    simp [shcrKeyIndProg, scTPk, Comp.size, Expr.size]
  have hRes : (shcrKeyIndProg S Q K).resume.size ≤
      3 * bits K + 5 * bits (min K S.N_dh) + 1 * bits (min K S.N_sess_tot) + 1160 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrResumeC, initFinishC, shcrFinE, honestPeerC, checkProvC, hkdfOrRoC, partnerC,
      findHonestC, isGameSpkC, isGameOpkC, buildSecretsE, dhOptNZ,
      scBase, scCnt, scIR, scUpd, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stRo, stAdv, stUpd,
      peSecIKA0, peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reDrRand,
      buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rHdr, rInitUnfresh, getDBytes, rs, guardE, isSomeE, optFst, optSnd, nonZero32, kyberEq, sidEq, natEq, nat2Eq, optU32Eq, optBytesEq, eLet2,
      v, bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eFind, eAny,
      litB, catB, widenB, eqB, eqU32, sBytes32, sDrKey96, qX25519, qX25519Base, qIsCanonical, qPow8, qHkdfDerive96,
      Comp.size, Expr.size, ↓reduceIte]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := rfl
    have hb1 : bits 1 = 1 := rfl
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    omega
  have hFin : (shcrKeyIndProg S Q K).finish.size ≤ bits Q + 100 := by
    simp only [shcrKeyIndProg, shcrExtractC, scRR, scTSk, scChosen, scTPk, rrCt,
      optBytesEq, eLet2, orE, eqB, qKemDecaps,
      bindV, findMV, eLet, eCaseOpt, v, Comp.size, Expr.size]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    omega
  change (shcrKeyIndProg S Q K).init.size + (shcrKeyIndProg S Q K).handlePre.size +
    (shcrKeyIndProg S Q K).chDone.size + (shcrKeyIndProg S Q K).resume.size +
    (shcrKeyIndProg S Q K).handlePost.size +
    (shcrKeyIndProg S Q K).finish.size ≤ _
  omega

theorem ki_shcrKeyIndProg_size_le (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).size ≤
      bits Q + 120 * bits K + 75 * bits S.N_dh + 5 * bits S.N_sess_tot + 26000 := by
  have h := ki_shcrKeyIndProg_size_bounds S Q K
  have hd : bits (min K S.N_dh) ≤ bits S.N_dh := ki_bits_mono (Nat.min_le_right _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ki_bits_mono (Nat.min_le_right _ _)
  omega

private theorem ki_shcrKeyIndProg_size_le_clamped (S : Setup) (Q K : Nat) :
    (shcrKeyIndProg S Q K).size ≤
      bits Q + 200 * bits K + 26000 := by
  have h := ki_shcrKeyIndProg_size_bounds S Q K
  have hd : bits (min K S.N_dh) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits K := ki_bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ki_gdhHandle_size_le (S : Setup) (K : Nat) :
    (gdhHandle S K).size ≤ 54 * bits K + 42 * bits S.N_dh + 5 * bits S.N_sess_tot + 15000 := by
  simp (config := { maxSteps := 1000000 }) only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB,
    genOpkGdhB, initiateGdhB, finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase, wrapSim,
    fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    paU, paV, paUp, paPrinFlag, paPrinIdx, paDhFlag, paEphIdx, paSpkIdx, paOpkMode, paOpkIdx,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    spkFlatIdxE, opkFlatIdxE, initSlotIdxE, initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, optBytesEq, getDBytes, isSomeE, optFst, optSnd, nonZero32,
    orE, mulRight, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
    ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    ki_gPrim_size, gPrim, liftBase,
    v, letV, bindV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBytes32, sRandom64, sDrKey96,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, ddhQ, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := rfl
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have b1 : bits (S.N_recv.min S.N_spk_tot) ≤ bits S.N_dh :=
    ki_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b2 : bits (S.N_opk.min S.N_opk_tot) ≤ bits S.N_dh :=
    ki_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b3 : bits (S.N_send_opk.min S.N_send_opk_tot) ≤ bits S.N_dh :=
    ki_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b4 : bits S.N_send_opk_tot ≤ bits S.N_dh := ki_bits_mono (by omega)
  have b5 : bits (S.N_send_no_opk.min S.N_send_no_opk_tot) ≤ bits S.N_dh :=
    ki_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b6 : bits S.N_send_tot ≤ bits S.N_dh := ki_bits_mono (by omega)
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ki_bits_mono (Nat.min_le_right _ _)
  have : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ki_bits_mono (Nat.min_le_right _ _)
  omega

theorem ki_gdhFinish_size_le (S : Setup) (K : Nat) :
    (gdhFinish S K).size ≤ 9 * bits K + 5 * bits S.N_dh + 2 * bits S.N_sess_tot + 900 := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
    smBase, smLog, smPows, paU, paV, paMode, natEq, nat2Eq,
    ki_letV_size, ki_bindV_size, ki_caseOptV_size, ki_findMV_size, ki_mapMV_size, ki_foldMV_size,
    ki_eCaseOpt_size, ki_eCaseSum_size, ki_eFind_size, ki_eMap_size,
    ki_gPrim_size, ki_qPow8_size, ki_qX25519_size, ki_ddhQ_size,
    ki_litB_size, ki_takeKB_size, ki_dropB_size, ki_eqB_size, ki_v_size, Comp.size, Expr.size]
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ki_bits_mono (Nat.min_le_right _ _)
  have : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ki_bits_mono (Nat.min_le_right _ _)
  omega

private theorem ki_fgKeyIndGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).size ≤
      65 * bits K + 85 * bits S.N_dh + 10 * bits S.N_sess_tot + 17000 := by
  have hH := ki_gdhHandle_size_le S K
  have hF := ki_gdhFinish_size_le S K
  have hI : (fgKeyIndGapDhProg S K).init.size ≤ 36 * bits S.N_dh + 300 := by
    simp only [fgKeyIndGapDhProg, initAdv4, initParamsFlat, initParamsDh, initParamsIk,
      initParamsOpk, paMk, emptySimE, smMk, emptyStE,
      ki_letV_size, ki_bindV_size, ki_gPrim_size, ki_sIndex_size, ki_sBool_size, ki_v_size,
      Comp.size, Expr.size]
    have hb0 : bits 0 = 1 := rfl
    have hb1 : bits 1 = 1 := rfl
    have hb2 : bits 2 = 2 := rfl
    have hb3 : bits 3 = 2 := rfl
    have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
    have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
    have c1 := ki_bits_le_of_le_four_mul_sq (x := S.N_id * S.N_spk_tot) (N := S.N_dh) (by nlinarith)
    have c2 : bits S.N_spk_tot ≤ bits S.N_dh := ki_bits_mono (by omega)
    have c3 : bits S.N_opk_tot ≤ bits S.N_dh := ki_bits_mono (by omega)
    have c4 := ki_bits_le_of_le_four_mul_sq
      (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (N := S.N_dh) (by nlinarith)
    have c5 := ki_bits_le_of_le_four_mul_sq
      (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id)
      (N := S.N_dh) (by nlinarith)
    have c6 : bits S.N_id ≤ bits S.N_dh := ki_bits_mono (by omega)
    omega
  change (fgKeyIndGapDhProg S K).init.size + (gdhHandle S K).size + (gdhFinish S K).size ≤ _
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_shcrPostC_litSize_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcrPostC (Δ := Δ) S K s q) ≤ 8000 := by
  simp (config := { maxSteps := 1000000 }) only [
    shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC, shcrAcceptB, onBase, shcrFinE,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
    isNoneRespE,
    initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
    initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
    testB, revealB, roB, revealDhB, registerB, revealSpkB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
    aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
    qK, qJ, qO, qHdr, qKJO,
    stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
    seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
    seTested, seRevealed, seMk, seUpd,
    reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
    reTested, reRevealed, reMk, reUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
    orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
    buildSecretsE, eLet2,
    v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBool, sBytes32, sRandom64, sDrKey96, sIndex,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ki_shcrKeyIndProg_litSize_le (S : Setup) (Q K : Nat) :
    red2LitSize (shcrKeyIndProg S Q K) ≤ 20000 := by
  have hIni : compLitSize (shcrKeyIndProg S Q K).init = 0 := by
    dsimp only [shcrKeyIndProg]
    split_ifs <;> simp [scMk, emptyStE, v, bindV, sBool, sIndex,
      compLitSize, exprLitSize, pqOpLitSize]
  have hPre : compLitSize (shcrKeyIndProg S Q K).handlePre ≤ 10000 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrPreC, pauseCheckC, tryPauseC, shcrPostC, shcrGenSpkB, initGuardE, shcrInitiateC,
      shcrAcceptB, shcrResumeC, shcrExtractC, onBase, shcrFinE,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      isNoneRespE,
      initPrinB, corruptB, genSpkB, genOpkB, initSidE, initFinishC, preCheckC, checkSigsC,
      initiateC, initiateOpkB, initiateNoOpkB, acceptOpkB, acceptNoOpkB,
      testB, revealB, roB, revealDhB, registerB, revealSpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, checkProvC, partnerC, recordRespC, hkdfOrRoC,
      aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, acceptKeysC,
      qK, qJ, qO, qHdr, qKJO,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd,
      reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest, reDrReal, reDrRand,
      reTested, reRevealed, reMk, reUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
      orE, mulRight, natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32,
      buildSecretsE, eLet2,
      v, bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
      sBool, sBytes32, sRandom64, sDrKey96, sIndex,
      qX25519, qX25519Base, qIsCanonical, qPow8,
      qSigPkGen, qSigSign, qSigVerify,
      qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96,
      encEC, encKEM,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
      Nat.add_zero, Nat.zero_add,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    omega
  have hPost : compLitSize (shcrKeyIndProg S Q K).handlePost ≤ 8000 := by
    dsimp only [shcrKeyIndProg, keyIndCodec]
    exact ki_shcrPostC_litSize_le S K _ _
  have hRes : compLitSize (shcrKeyIndProg S Q K).resume ≤ 1500 := by
    dsimp only [shcrKeyIndProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrResumeC, initFinishC, shcrFinE, honestPeerC, checkProvC, hkdfOrRoC, partnerC,
      findHonestC, isGameSpkC, isGameOpkC, buildSecretsE, dhOptNZ,
      scBase, scCnt, scIR, scUpd, stSecb, stPrin, stSpks, stOpks, stSess, stResps, stRo, stAdv, stUpd,
      peSecIKA0, peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand, seHdr,
      seTested, seRevealed, seMk, seUpd, reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reDrRand,
      buIkB, buSpkId, buSpkB, buOpkB, buPqspkId, buPqspkB, hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rHdr, rInitUnfresh, getDBytes, rs, guardE, isSomeE, optFst, optSnd, nonZero32, kyberEq, sidEq, natEq, nat2Eq, optU32Eq, optBytesEq, eLet2,
      v, bindV, letV, caseOptV, findMV, anyMV, eLet, eCaseOpt, eFind, eAny,
      litB, catB, widenB, eqB, eqU32, sBytes32, sDrKey96, qX25519, qX25519Base, qIsCanonical, qPow8, qHkdfDerive96,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
      Nat.add_zero, Nat.zero_add, ↓reduceIte]
    omega
  have hDone : compLitSize (shcrKeyIndProg S Q K).chDone = 0 := by
    simp [shcrKeyIndProg, scTPk, compLitSize, exprLitSize, pqOpLitSize]
  have hFin : compLitSize (shcrKeyIndProg S Q K).finish = 0 := by
    simp [shcrKeyIndProg, shcrExtractC, scRR, scTSk, scChosen, scTPk, rrCt,
      optBytesEq, eLet2, orE, eqB, qKemDecaps, bindV, findMV, eLet, eCaseOpt, v,
      compLitSize, exprLitSize, pqOpLitSize]
  change compLitSize (shcrKeyIndProg S Q K).init + compLitSize (shcrKeyIndProg S Q K).handlePre +
    compLitSize (shcrKeyIndProg S Q K).chDone + compLitSize (shcrKeyIndProg S Q K).resume +
    compLitSize (shcrKeyIndProg S Q K).handlePost +
    compLitSize (shcrKeyIndProg S Q K).finish ≤ _
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ki_gdhHandle_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhHandle S K) ≤ 10000 := by
  simp (config := { maxSteps := 1000000 }) only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB,
    genOpkGdhB, initiateGdhB, finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase, wrapSim,
    fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    paU, paV, paUp, paPrinFlag, paPrinIdx, paDhFlag, paEphIdx, paSpkIdx, paOpkMode, paOpkIdx,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    spkFlatIdxE, opkFlatIdxE, initSlotIdxE, initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, optBytesEq, getDBytes, isSomeE, optFst, optSnd, nonZero32,
    orE, mulRight, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
    ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    ki_gPrim_litSize, gPrim, liftBase,
    v, letV, bindV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBytes32, sRandom64, sDrKey96,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, ddhQ, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
theorem ki_gdhFinish_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhFinish S K) ≤ 1000 := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
    smBase, smLog, smPows, paU, paV, paMode, natEq, nat2Eq,
    letV, bindV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    ki_gPrim_litSize, gPrim, liftBase, qPow8, qX25519, ddhQ,
    litB, takeKB, dropB, eqB, v,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem ki_fgKeyIndGapDhProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (fgKeyIndGapDhProg S K) ≤ 20000 := by
  have hH := ki_gdhHandle_litSize_le S K
  have hF := ki_gdhFinish_litSize_le S K
  have hI : compLitSize (fgKeyIndGapDhProg S K).init ≤ 100 := by
    simp only [fgKeyIndGapDhProg, initAdv4, initParamsFlat, initParamsDh, initParamsIk,
      initParamsOpk, paMk, emptySimE, smMk, emptyStE,
      letV, bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, sBool, v,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  change compLitSize (fgKeyIndGapDhProg S K).init + compLitSize (gdhHandle S K) + compLitSize (gdhFinish S K) ≤ _
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ki_gdhHandle2_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhHandle2 S K) ≤ 10000 := by
  simp (config := { maxSteps := 1000000 }) only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B,
    genOpkGdh2B, initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2, wrapSim2, ephSidMatchesE,
    fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget, pa2OpkMode, pa2OpkTarget,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, optBytesEq, getDBytes, isSomeE, optFst, optSnd, nonZero32,
    orE, mulRight, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
    ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    ki_gPrim_litSize, gPrim, liftBase,
    v, letV, bindV, caseOptV, caseSumV, findMV, anyMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBytes32, sRandom64, sDrKey96,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, ddhQ, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
private theorem ki_gdhFinish2_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhFinish2 S K) ≤ 1000 := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
    smBase, smLog, smPows, pa2U, pa2V, pa2Mode, natEq, nat2Eq,
    letV, bindV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    ki_gPrim_litSize, gPrim, liftBase, qPow8, qX25519, ddhQ,
    litB, takeKB, dropB, eqB, v,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem ki_chooseArm2C_litSize
    {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} {α : Ty SignalPqxdh.LegacyCosted.pqSig}
    [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ'],
      Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ' α)
    (h1 : ∀ {Δ'} [Ext Γ₁ Δ'], compLitSize (c1 (Δ' := Δ')) = 0)
    (h2 : ∀ {Δ'} [Ext Γ₁ Δ'], compLitSize (c2 (Δ' := Δ')) = 0) :
    compLitSize (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2) = 0 := by
  have hb : ∀ {Δ'} (a b : Nat),
      compLitSize (bernoulliRatioGdhC (Δ := Δ') a b) = 0 := by
    intro Δ' a b; unfold bernoulliRatioGdhC
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  unfold chooseArm2C
  split_ifs
  · exact h2
  · exact h1
  · simp [bindV, v, hb, h1, h2, compLitSize, exprLitSize, pqOpLitSize]

set_option linter.unusedSimpArgs false in
private theorem ki_fgKeyIndGapDh2Prog_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (fgKeyIndGapDh2Prog S K) ≤ 20000 := by
  have hH := ki_gdhHandle2_litSize_le S K
  have hF := ki_gdhFinish2_litSize_le S K
  have hP1 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (samplePrin2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold samplePrin2C
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  have hP2 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (sampleSpkPair2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold sampleSpkPair2C
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  have hP3 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (sampleOpkTriple2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold sampleOpkTriple2C
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  have hP4 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (sampleSendOpkTarget2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold sampleSendOpkTarget2C
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  have hP5 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (sampleSendNoOpkTarget2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold sampleSendNoOpkTarget2C
    split_ifs <;> simp [bindV, ki_gPrim_litSize, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize, pqOpLitSize]
  have hP6 : ∀ {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)},
      compLitSize (sampleSendTarget2C S (Δ := Δ)) = 0 := by
    intro Δ; unfold sampleSendTarget2C
    split_ifs
    · rfl
    · exact ki_chooseArm2C_litSize _ _ _ _ hP4 hP5
  have hIP : ∀ {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
      (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))),
      compLitSize (initParams2C S (Δ := Δ) uv) = 0 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp [pa2Mk, v, compLitSize, exprLitSize, pqOpLitSize]
    · refine ki_chooseArm2C_litSize _ _ _ _ ?_ ?_
      · exact ki_chooseArm2C_litSize _ _ _ _
          (by simp [bindV, pa2Mk, v, hP1, hP2, compLitSize, exprLitSize, pqOpLitSize])
          (by simp [bindV, pa2Mk, v, hP6, hP2, compLitSize, exprLitSize, pqOpLitSize])
      · exact ki_chooseArm2C_litSize _ _ _ _
          (by simp [bindV, pa2Mk, v, hP6, hP1, compLitSize, exprLitSize, pqOpLitSize])
          (by simp [bindV, pa2Mk, v, hP4, hP3, compLitSize, exprLitSize, pqOpLitSize])
  have hI : compLitSize (fgKeyIndGapDh2Prog S K).init ≤ 100 := by
    simp only [fgKeyIndGapDh2Prog, initAdv4_2, emptySimE, smMk, emptyStE,
      letV, bindV, ki_gPrim_litSize, gPrim, liftBase, sBool, v, hIP,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  change compLitSize (fgKeyIndGapDh2Prog S K).init + compLitSize (gdhHandle2 S K) + compLitSize (gdhFinish2 S K) ≤ _
  omega

end KeyIndSizeBounds

section ShcrAuthR64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift

private def zAuthPrimW : SignalPqxdh.LegacyCosted.pqPrimIface.Tag → ℕ := fun _ => 0
private def authR64WS : SignalPqxdh.LegacyCosted.pqPrimIface.smp.Samp → ℕ := r64W

@[simp] private theorem authR64WS_bool : authR64WS .bool = 0 := rfl
@[simp] private theorem authR64WS_bytes32 : authR64WS .bytes32 = 0 := rfl
@[simp] private theorem authR64WS_random64 : authR64WS .random64 = 1 := rfl
@[simp] private theorem authR64WS_drKey96 : authR64WS .drKey96 = 0 := rfl
@[simp] private theorem authR64WS_index (n : ℕ) : authR64WS (.index n) = 0 := rfl

@[simp] private theorem findHonestC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (findHonestC S K st ik).queries zAuthPrimW authR64WS = 0 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queryPrim, zAuthPrimW, Comp.queries]

@[simp] private theorem isAdvRegC_r64 (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isAdvRegC K st pk).queries zAuthPrimW authR64WS = 0 := by
  simp [isAdvRegC, bindV, Comp.queryPrim, zAuthPrimW, Comp.queries]

@[simp] private theorem isGameSpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameSpkC S K st pk).queries zAuthPrimW authR64WS = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queryPrim, zAuthPrimW, Comp.queries]

@[simp] private theorem isGameOpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameOpkC S K st pk).queries zAuthPrimW authR64WS = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queryPrim, zAuthPrimW, Comp.queries]

@[simp] private theorem koskBundleOkC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries zAuthPrimW authR64WS = 0 := by
  simp [koskBundleOkC, bindV, caseOptV, Comp.queries]

@[simp] private theorem koskSenderOkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkC S K st ik).queries zAuthPrimW authR64WS = 0 := by
  simp [koskSenderOkC, letV, bindV, Comp.queries]

@[simp] private theorem resolveSigPkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (resolveSigPkC S K st ik).queries zAuthPrimW authR64WS = 0 := by
  simp [resolveSigPkC, letV, bindV, Comp.queries]

@[simp] private theorem hkdfOrRoC_true_r64 (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (sec : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 192)) :
    (hkdfOrRoC K true st sec).queries zAuthPrimW authR64WS = 0 := by
  simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.sampleDrKey96, Comp.queries]

@[simp] private theorem rootRoC_r64 (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ authStateTy) [Ext Γ Δ]
    (rk dh : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (rootRoC K st rk dh).queries zAuthPrimW authR64WS = 0 := by
  simp [rootRoC, letV, caseOptV, bindV, Comp.sampleBytes32, Comp.queries]

theorem shcrReductionAuthProg_r64_le (S : Setup) (q : ℕ) :
    (shcrReductionAuthProg S q q).totalQueries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) q ≤
      4 * q := by
  change (shcrReductionAuthProg S q q).totalQueries zAuthPrimW authR64WS q ≤ 4 * q
  have hPre : (shcrReductionAuthProg S q q).handlePre.queries zAuthPrimW authR64WS ≤ 4 := by
    dsimp only [shcrReductionAuthProg, SignalPqxdh.LegacyCosted.authCodec]
    simp only [
      koskBundleOkC_r64, koskSenderOkC_r64, resolveSigPkC_r64,
      findHonestC_r64, hkdfOrRoC_true_r64, rootRoC_r64,
      shcrPreC, pauseCheckC, tryPauseC, shcrPostC,
      shcrAcceptB, shcrSendC, shcrGenSpkB, onBase,
      shcrFinC, finishC, checkSigsC, preCheckC,
      initPrinB, corruptB, genSpkB, genOpkB,
      registerB, roB, roRootB, recvB, recvTailC,
      bindV, letV, caseOptV, caseSumV,
      Comp.queries_letC, Comp.sampleBytes32, Comp.sampleRandom64,
      Comp.queryPrim, zAuthPrimW, authR64WS_bytes32, authR64WS_random64, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    omega
  have hPost : (shcrReductionAuthProg S q q).handlePost.queries zAuthPrimW authR64WS ≤ 4 := by
    dsimp only [shcrReductionAuthProg, SignalPqxdh.LegacyCosted.authCodec]
    simp only [
      koskBundleOkC_r64, koskSenderOkC_r64, resolveSigPkC_r64,
      findHonestC_r64, hkdfOrRoC_true_r64, rootRoC_r64,
      shcrPostC, shcrAcceptB, shcrSendC, shcrGenSpkB, onBase,
      shcrFinC, finishC, checkSigsC, preCheckC,
      initPrinB, corruptB, genSpkB, genOpkB,
      registerB, roB, roRootB, recvB, recvTailC,
      bindV, letV, caseOptV, caseSumV,
      Comp.queries_letC, Comp.sampleBytes32, Comp.sampleRandom64,
      Comp.queryPrim, zAuthPrimW, authR64WS_bytes32, authR64WS_random64, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    omega
  have hRes : (shcrReductionAuthProg S q q).resume.queries zAuthPrimW authR64WS = 0 := by
    dsimp only [shcrReductionAuthProg, SignalPqxdh.LegacyCosted.authCodec]
    simp only [hkdfOrRoC_true_r64, rootRoC_r64, shcrResumeC, finishC,
      shcrFinC, bindV, letV, caseOptV, Comp.queries_letC,
      Comp.sampleBytes32, Comp.queryPrim, zAuthPrimW, authR64WS_bytes32, Comp.queries]
    rfl
  have hFin : (shcrReductionAuthProg S q q).finish.queries zAuthPrimW authR64WS = 0 := by
    simp [shcrReductionAuthProg, SignalPqxdh.LegacyCosted.authCodec, shcrExtractC,
      bindV, findMV, Comp.queryPrim, zAuthPrimW, Comp.queries]
  have hIni : (shcrReductionAuthProg S q q).init.queries zAuthPrimW authR64WS = 0 := by
    dsimp only [shcrReductionAuthProg]
    split_ifs <;> simp [bindV, Comp.sampleIndex, Comp.sampleBool, Comp.queries]
  have hDone : (shcrReductionAuthProg S q q).chDone.queries zAuthPrimW authR64WS = 0 := by
    simp [shcrReductionAuthProg, SignalPqxdh.LegacyCosted.authCodec, Comp.queries]
  unfold TwoStageCostedReduction.totalQueries
  rw [hIni, hDone, hRes, hFin]
  have hMax : max ((shcrReductionAuthProg S q q).handlePre.queries zAuthPrimW authR64WS)
      ((shcrReductionAuthProg S q q).handlePost.queries zAuthPrimW authR64WS) ≤ 4 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  omega

end ShcrAuthR64

section AuthHsSizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)

@[simp] private theorem ah_liftChal_litSize {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqChalIface C) c.liftChal = compLitSize c := by
  induction c <;> simp_all [Comp.liftChal, compLitSize, pqChalIface, pqPrimIface]

@[simp] private theorem ah_liftChal_euf_litSize {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqxdhEufCmaIface) c.liftChal = compLitSize c := ah_liftChal_litSize c

@[simp] private theorem ah_liftChal_gdh_litSize {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqGapDhIface) c.liftChal = compLitSize c := ah_liftChal_litSize c

@[simp] private theorem ah_liftChal_size {C : ChallengerOracle} {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    c.liftChal.size (I := pqChalIface C) = c.size := by
  induction c <;> simp_all [Comp.liftChal, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem ah_liftChal_euf_size {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqxdhEufCmaIface) c.liftChal = c.size := ah_liftChal_size c

@[simp] private theorem ah_liftChal_gdh_size {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqGapDhIface) c.liftChal = c.size := ah_liftChal_size c

section AhAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List (Ty pqSig)} {τ τ₁ τ₂ : Ty pqSig}

@[simp] private theorem ah_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem ah_letC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem ah_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .vz).size + 1 := rfl
@[simp] private theorem ah_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .vz).size + 1 := rfl
@[simp] private theorem ah_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem ah_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem ah_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).size =
      xs.size + init.size + (f .vz (.vs .vz)).size + bits K + 1 := rfl
@[simp] private theorem ah_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .vz).size + 1 := rfl
@[simp] private theorem ah_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .vz).size + 1 := rfl
@[simp] private theorem ah_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .vz).size + (kr .vz).size + 1 := rfl
@[simp] private theorem ah_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .vz).size + bits K + 1 := rfl
@[simp] private theorem ah_litBytes_size (w : ℕ+) (bs : Bytes) :
    (Expr.litBytes w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_bytesAppend_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesAppend a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah_bytesCons_size {w : ℕ+} (b : UInt8) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesCons b a).size = a.size + 1 := rfl
@[simp] private theorem ah_bytesWiden_size (w d : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesWiden w d a).size = a.size + 1 := rfl
@[simp] private theorem ah_bytesTakeK_size {w : ℕ+} (k : ℕ+) (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesTakeK k a).size = a.size + 1 := rfl
@[simp] private theorem ah_bytesDrop_size {w : ℕ+} (n : Expr pqxdhOps Γ .nat)
    (a : Expr pqxdhOps Γ (B w)) : (Expr.bytesDrop n a).size = n.size + a.size + 2 := rfl
@[simp] private theorem ah_bytesLen_size {w : ℕ+} (a : Expr pqxdhOps Γ (B w)) :
    (Expr.bytesLen a).size = a.size + 1 := rfl
@[simp] private theorem ah_bytesBeq_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (Expr.bytesBeq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah_bytesVarint_size (n : Expr pqxdhOps Γ .nat) :
    (Expr.bytesVarint n).size = n.size + 1 := rfl
@[simp] private theorem ah_u32OfNat_size (n : Expr pqxdhOps Γ .nat) :
    (Expr.u32OfNat n).size = n.size + 1 := rfl
@[simp] private theorem ah_u32Beq_size (a b : Expr pqxdhOps Γ U32) :
    (Expr.u32Beq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ah_sampleBool_size : (Comp.sampleBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleBytes32_size : (Comp.sampleBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleRandom64_size : (Comp.sampleRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleDrKey96_size : (Comp.sampleDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleIndex_size (N : ℕ) : (Comp.sampleIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_queryPrim_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrim g e).size = e.size + 1 := rfl
@[simp] private theorem ah_sampleBoolC_size : (Comp.sampleBoolC (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleBytes32C_size : (Comp.sampleBytes32C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleRandom64C_size : (Comp.sampleRandom64C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleDrKey96C_size : (Comp.sampleDrKey96C (C := C) (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_sampleIndexC_size (N : ℕ) :
    (Comp.sampleIndexC (C := C) N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ah_queryPrimC_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (Comp.queryPrimC (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem ah_queryChal_size (g : C.Tag) (e : Expr pqxdhOps Γ (C.dom g)) :
    (Comp.queryChal (C := C) g e).size = e.size + 1 := rfl
@[simp] private theorem ah_queryDdh_size (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B 32) (B 32)))) :
    (AuthHs.Comp.queryDdh e).size = e.size + 1 := rfl
@[simp] private theorem ah_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem ah_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) :
    (encKEM e).size = e.size + 1 := rfl

end AhAtomicSizeSimp

private theorem ah_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem ah_eff_le_dh (S : Setup) :
    nRecvEff S ≤ S.N_dh ∧ nSendOpkEff S ≤ S.N_dh ∧ nSendNoOpkEff S ≤ S.N_dh := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hspk : S.N_spk_tot = S.N_id * S.N_recv := rfl
  have hso : S.N_send_opk_tot = S.N_id * S.N_send_opk := rfl
  have hsn : S.N_send_no_opk_tot = S.N_id * S.N_send_no_opk := rfl
  unfold nRecvEff nSendOpkEff nSendNoOpkEff
  split_ifs with h0
  · omega
  · have hpos : 1 ≤ S.N_id := by omega
    have h1 : S.N_recv ≤ S.N_id * S.N_recv := by simpa using Nat.mul_le_mul_right S.N_recv hpos
    have h2 : S.N_send_opk ≤ S.N_id * S.N_send_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_opk hpos
    have h3 : S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_no_opk hpos
    omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ah_sigReductionAuthProg_size_le (S : Setup) (K : Nat) :
    (sigReductionAuthProg S K).size ≤
      80 * bits K + 20 * bits S.N_dh + 20 * bits S.N_sess_tot + 12000 := by
  dsimp only [sigReductionAuthProg, CostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    sigInitDsl, sigHandleDsl, sigFinishDsl, sigStepC, extractC, wrapC,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC, sendGuardE,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ah_liftChal_size, ah_liftChal_euf_size, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal,
    encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have bId : bits S.N_id ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSpk : bits S.N_spk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bOpk : bits S.N_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSend : bits S.N_send_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSendO : bits S.N_send_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSendN : bits S.N_send_no_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  have : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ah_bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ah_shcrReductionAuthProg_size_bounds (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).size ≤
      bits Q + 115 * bits K + 50 * bits (min K S.N_dh) + 5 * bits (min K S.N_sess_tot) + 21000 := by
  have hIni : (shcrReductionAuthProg S Q K).init.size ≤ 100 := by
    dsimp only [shcrReductionAuthProg]
    split_ifs <;> {
      simp only [scMk, emptyAuthStE, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
        Expr.noneE, Expr.someE, Expr.listNil, v, Comp.letC, bindV, letV,
        Comp.sampleBool, Comp.sampleIndex, Comp.size, Expr.size]
      have hb0 : bits 0 = 1 := rfl
      omega
    }
  have hRest : (shcrReductionAuthProg S Q K).handlePre.size +
      (shcrReductionAuthProg S Q K).chDone.size +
      (shcrReductionAuthProg S Q K).resume.size +
      (shcrReductionAuthProg S Q K).handlePost.size +
      (shcrReductionAuthProg S Q K).finish.size ≤
      bits Q + 115 * bits K + 50 * bits (min K S.N_dh) + 5 * bits (min K S.N_sess_tot) + 20900 := by
    dsimp only [shcrReductionAuthProg]
    simp (config := { maxSteps := 1000000 }) only [
      shcrPreC, pauseCheckC, tryPauseC, shcrPostC, shcrGenSpkB, sendGuardE, shcrSendC, shcrAcceptB,
      shcrResumeC, shcrExtractC, shcrFinC, onBase, preCheckC, checkSigsC, finishC,
      scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
      pdSid, pdBu, pdM0, pdM1, pdUI,
      initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
      seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seEphASk, seFresh, seChal, seMk,
      pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
      natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      v, Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, mapMV,
      foldMV, eLet, eCaseOpt, eCaseSum,
      eFind, eAny, eMap,
      Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
      Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
      Expr.u32OfNat, Expr.u32Beq,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
      Comp.sampleIndex, Comp.queryPrim, encEC, encKEM,
      Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    have hb0 : bits 0 = 1 := by decide
    have hb1 : bits 1 = 1 := by decide
    have hb32 : bits 32 = 6 := by decide
    have hb64 : bits 64 = 7 := by decide
    have hb96 : bits 96 = 7 := by decide
    have hb128 : bits 128 = 8 := by decide
    have hb160 : bits 160 = 8 := by decide
    have hb192 : bits 192 = 8 := by decide
    omega
  change (shcrReductionAuthProg S Q K).init.size + (shcrReductionAuthProg S Q K).handlePre.size +
    (shcrReductionAuthProg S Q K).chDone.size + (shcrReductionAuthProg S Q K).resume.size +
    (shcrReductionAuthProg S Q K).handlePost.size + (shcrReductionAuthProg S Q K).finish.size ≤ _
  omega

theorem ah_shcrReductionAuthProg_size_le (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).size ≤
      bits Q + 115 * bits K + 50 * bits S.N_dh + 5 * bits S.N_sess_tot + 21000 := by
  have h := ah_shcrReductionAuthProg_size_bounds S Q K
  have hd : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ah_bits_mono (Nat.min_le_right _ _)
  omega

private theorem ah_shcrReductionAuthProg_size_le_clamped (S : Setup) (Q K : Nat) :
    (shcrReductionAuthProg S Q K).size ≤
      bits Q + 170 * bits K + 21000 := by
  have h := ah_shcrReductionAuthProg_size_bounds S Q K
  have hd : bits (min K S.N_dh) ≤ bits K := ah_bits_mono (Nat.min_le_left _ _)
  have hs : bits (min K S.N_sess_tot) ≤ bits K := ah_bits_mono (Nat.min_le_left _ _)
  omega

set_option linter.unusedSimpArgs false in
theorem ah_extractC_size_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (bu : Var Γ₄ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (AuthHs.extractC (Δ := Δ) S K tp tpk st bu).size ≤
      4 * bits K + 2 * bits S.N_dh + 300 := by
  simp only [AuthHs.extractC, honestPeerC, findHonestC,
    stPrin, stSpks, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig,
    natEq, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.findBounded, Expr.anyBounded, Comp.findBoundedM,
    v, Comp.letC, bindV, letV, findMV,
    eCaseOpt, eAny, Expr.bytesCons, Expr.bytesWiden, Expr.bytesBeq,
    Comp.queryPrim, encEC, encKEM, Comp.size, Expr.size]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have bId : bits S.N_id ≤ bits S.N_dh := ah_bits_mono (by omega)
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
theorem ah_fgInitDsl_size_le (S : Setup) :
    (AuthHs.fgInitDsl S).size ≤ 4 * bits S.N_dh + 200 := by
  simp only [fgInitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil,
    v, Comp.letC, bindV, letV,
    Comp.sampleBoolC, Comp.sampleIndexC, Comp.size, Expr.size]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have bId : bits S.N_id ≤ bits S.N_dh := ah_bits_mono (by omega)
  omega

set_option linter.unusedSimpArgs false in
theorem ah_fgFinishDsl_size_le (S : Setup) (K : Nat) :
    (AuthHs.fgFinishDsl S K).size ≤
      10 * bits K + 10 * bits S.N_dh + 4 * bits S.N_sess_tot + 800 := by
  simp only [fgFinishDsl, fgExtractC, initDh1CandC, respCandC, logScanC, findMapC,
    paDh1, paU, paV, fsLog, fsBase, fsPows, fsResp,
    stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
    slice32, bytesEmpty, zero32, natEq, nat2Eq,
    Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC,
    Expr.findBounded, Expr.mapBounded, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
    v, Comp.letC, bindV, letV, caseOptV,
    findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
    Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh, Comp.size, Expr.size]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  have hb96 : bits 96 = 7 := by decide
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  have : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ah_bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ah_fgStepC_size_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ AuthHs.paramsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    (AuthHs.fgStepC (Δ := Δ) S K pa sim q).size ≤
      105 * bits K + 45 * bits S.N_dh + 15 * bits S.N_sess_tot + 18500 := by
  simp (config := { maxSteps := 1000000 }) only [fgStepC, fgInitPrinC, fgGenSpkC, fgSendC,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
    isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, sendGuardE,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    q4, bytesEmpty, slice32, zero32, emptySimE,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ah_liftChal_size, ah_liftChal_gdh_size, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
    encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  obtain ⟨hNR, hSO, hSN⟩ := ah_eff_le_dh S
  have bNR : bits (nRecvEff S) ≤ bits S.N_dh := ah_bits_mono hNR
  have bSO : bits (nSendOpkEff S) ≤ bits S.N_dh := ah_bits_mono hSO
  have bSN : bits (nSendNoOpkEff S) ≤ bits S.N_dh := ah_bits_mono hSN
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have bId : bits S.N_id ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSpk : bits S.N_spk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bOpk : bits S.N_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSend : bits S.N_send_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSendO : bits S.N_send_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have bSendN : bits S.N_send_no_opk_tot ≤ bits S.N_dh := ah_bits_mono (by omega)
  have b1 : bits (S.N_recv.min S.N_spk_tot) ≤ bits S.N_dh :=
    ah_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b2 : bits (S.N_opk.min S.N_opk_tot) ≤ bits S.N_dh :=
    ah_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b3 : bits (S.N_send_opk.min S.N_send_opk_tot) ≤ bits S.N_dh :=
    ah_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b4 : bits (S.N_send_no_opk.min S.N_send_no_opk_tot) ≤ bits S.N_dh :=
    ah_bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  have : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ah_bits_mono (Nat.min_le_right _ _)
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ah_fgAuthGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).size ≤
      120 * bits K + 60 * bits S.N_dh + 20 * bits S.N_sess_tot + 20000 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hmd : bits (min K S.N_dh) ≤ bits S.N_dh := ah_bits_mono (Nat.min_le_right _ _)
  have hms : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ah_bits_mono (Nat.min_le_right _ _)
  have hT : (fgSampleTargetC S (Γ := [.prod (B 32) (B 32)])).size ≤ 100 := by
    unfold fgSampleTargetC
    dsimp only
    split_ifs <;>
      (simp only [bindV, natEq, v, Comp.sampleIndexC, Expr.litBool, Expr.litNat,
        Comp.iteC, Comp.size, Expr.size, hb0, hb1, hb2]; omega)
  have hSpk : (fgSampleSpkC S (Γ := [targetChoiceTy, .prod (B 32) (B 32)])).size ≤ 30 := by
    unfold fgSampleSpkC
    split_ifs <;>
      (simp only [bindV, v, Comp.sampleIndexC, Expr.noneE, Expr.someE, Comp.size, Expr.size]; omega)
  have hI : (fg2InitDsl S).size ≤ 220 := by
    simp only [fg2InitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
      Expr.litUnit, Expr.litBool, Expr.listNil, v, bindV, Comp.sampleBoolC,
      Comp.size, Expr.size]
    omega
  have hF : (fg2FinishDsl S K).size ≤
      10 * bits K + 10 * bits S.N_dh + 4 * bits S.N_sess_tot + 800 := by
    simp only [fg2FinishDsl, fg2ExtractC, fg2InitDh1CandC, fg2RespCandC, fg2LogScanC, fg2FindMapC,
      fg2PaDh1, fg2PaU, fg2PaV, fsLog, fsBase, fsPows, fsResp,
      stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
      slice32, bytesEmpty, zero32, natEq, nat2Eq,
      Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC,
      Expr.findBounded, Expr.mapBounded, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
      v, Comp.letC, bindV, letV, caseOptV, findMV, mapMV, foldMV,
      eCaseOpt, eCaseSum, eFind, eMap,
      Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
      Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh, Comp.size, Expr.size, hb32, hb96]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    omega
  have hS : (fg2StepC (Δ := fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy]) S K
      (.vz : Var (fg2ParamsTy :: fg2GsTy :: [authQueryTy]) fg2ParamsTy)
      (.vz : Var (fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy]) fgSimTy)
      (.vs .vz : Var [fg2GsTy, authQueryTy] authQueryTy)).size ≤
      105 * bits K + 45 * bits S.N_dh + 15 * bits S.N_sess_tot + 18500 := by
    simp (config := { maxSteps := 1000000 }) only [fg2StepC, fg2InitPrinC, fg2GenSpkC, fg2SendC,
      fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
      isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
      mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
      patchC, rootPatchC, sendGuardE,
      fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
      fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, fg2PaTS,
      feP1, feP2, feP3, feP4, feSs, feDk,
      pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
      q4, bytesEmpty, slice32, zero32, emptySimE,
      corruptB, genOpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
      seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seEphASk, seFresh, seChal, seMk,
      pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
      natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      ah_liftChal_size, ah_liftChal_gdh_size, v, Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV, eLet, eCaseOpt, eCaseSum,
      eFind, eAny, eMap,
      Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
      Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
      Expr.u32OfNat, Expr.u32Beq,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
      Comp.sampleIndex, Comp.queryPrim,
      Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
      Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
      encEC, encKEM, Comp.size, Expr.size,
      hb0, hb1, hb32, hb64, hb96, hb128, hb160, hb192,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
      _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
    omega
  have hH : (fg2HandleDsl S K).size ≤
      106 * bits K + 45 * bits S.N_dh + 15 * bits S.N_sess_tot + 18600 := by
    simp only [fg2HandleDsl, fg2PaDh1, fg2PaTI, fsBase, stPrin, peCorrupted, aNone, natEq,
      Expr.litUnit, Expr.litBool, Expr.boolAnd, Comp.iteC, Expr.findBounded,
      v, Comp.letC, bindV, letV, eCaseOpt, eFind,
      Comp.size, Expr.size]
    omega
  change (fg2InitDsl S).size + (fg2HandleDsl S K).size + (fg2FinishDsl S K).size ≤ _
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ah_sigReductionAuthProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (sigReductionAuthProg S K) ≤ 20000 := by
  dsimp only [sigReductionAuthProg, red1LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    sigInitDsl, sigHandleDsl, sigFinishDsl, sigStepC, extractC, wrapC,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC, sendGuardE,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ah_liftChal_litSize, ah_liftChal_euf_litSize, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
private theorem ah_sigReductionAuthProg2_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (sigReductionAuthProg2 S K) ≤ 20000 := by
  have h0 := ah_sigReductionAuthProg_litSize_le S K
  have hI2 : compLitSize (sigInit2Dsl S K) = 0 := by
    unfold sigInit2Dsl
    split_ifs <;> simp [emptyAuthStE, Expr.litUnit, Expr.litBool, Expr.litNat,
      Expr.noneE, Expr.listNil, v, bindV, Comp.sampleIndexC, Comp.sampleBoolC,
      compLitSize, exprLitSize, pqOpLitSize]
  have hF2 : compLitSize (sigFinish2Dsl S) = 0 := by
    unfold sigFinish2Dsl
    split_ifs <;> simp [eCaseOpt, Expr.litBytes, v, compLitSize, exprLitSize, pqOpLitSize]
  dsimp only [sigReductionAuthProg2, sigReductionAuthProg, red1LitSize] at h0 ⊢
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ah_shcrReductionAuthProg_litSize_le (S : Setup) (Q K : Nat) :
    red2LitSize (shcrReductionAuthProg S Q K) ≤ 20000 := by
  dsimp only [shcrReductionAuthProg, red2LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    shcrPreC, pauseCheckC, tryPauseC, shcrPostC, shcrGenSpkB, sendGuardE, shcrSendC, shcrAcceptB,
    shcrResumeC, shcrExtractC, shcrFinC, onBase, preCheckC, checkSigsC, finishC,
    scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, scMk, scUpd, rrCt,
    pdSid, pdBu, pdM0, pdM1, pdUI,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  split_ifs <;>
    (simp only [scMk, emptyAuthStE, stMk, Expr.litUnit, Expr.litBool, Expr.litNat,
      Expr.noneE, Expr.listNil, v, Comp.letC, bindV, letV,
      Comp.sampleBool, Comp.sampleIndex, compLitSize, exprLitSize, pqOpLitSize,
      Nat.add_zero, Nat.zero_add]; omega)

set_option linter.unusedSimpArgs false in
theorem ah_fgInitDsl_litSize_le (S : Setup) :
    compLitSize (AuthHs.fgInitDsl S) ≤ 200 := by
  simp only [fgInitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.listNil,
    v, Comp.letC, bindV, letV,
    Comp.sampleBoolC, Comp.sampleIndexC,
    compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
theorem ah_fgFinishDsl_litSize_le (S : Setup) (K : Nat) :
    compLitSize (AuthHs.fgFinishDsl S K) ≤ 1000 := by
  simp only [fgFinishDsl, fgExtractC, initDh1CandC, respCandC, logScanC, findMapC,
    paDh1, paU, paV, fsLog, fsBase, fsPows, fsResp,
    stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
    slice32, bytesEmpty, zero32, natEq, nat2Eq,
    Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC,
    Expr.findBounded, Expr.mapBounded, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
    v, Comp.letC, bindV, letV, caseOptV,
    findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
    Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ah_fgStepC_litSize_le (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (pa : Var Γ₁ AuthHs.paramsTy) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    compLitSize (AuthHs.fgStepC (Δ := Δ) S K pa sim q) ≤ 18500 := by
  simp (config := { maxSteps := 1000000 }) only [fgStepC, fgInitPrinC, fgGenSpkC, fgSendC,
    fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
    isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
    mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
    patchC, rootPatchC, sendGuardE,
    fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
    paU, paV, paDh1, paTI, paTS, feP1, feP2, feP3, feP4, feSs, feDk,
    pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
    q4, bytesEmpty, slice32, zero32, emptySimE,
    initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
    stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
    seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
    seEkASk, seEphASk, seFresh, seChal, seMk,
    pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
    oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
    isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
    natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ah_liftChal_litSize, ah_liftChal_gdh_litSize, v, Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, mapMV,
    foldMV, eLet, eCaseOpt, eCaseSum,
    eFind, eAny, eMap,
    Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
    Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
    Expr.u32OfNat, Expr.u32Beq,
    Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
    Comp.sampleIndex, Comp.queryPrim,
    Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
    Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ah_fgAuthGapDhProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (fgAuthGapDhProg S K) ≤ 20000 := by
  have hT : compLitSize (fgSampleTargetC S (Γ := [.prod (B 32) (B 32)])) = 0 := by
    unfold fgSampleTargetC
    dsimp only
    split_ifs <;>
      simp only [bindV, natEq, v, Comp.sampleIndexC, Expr.litBool, Expr.litNat,
        Comp.iteC, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  have hSpk : compLitSize (fgSampleSpkC S (Γ := [targetChoiceTy, .prod (B 32) (B 32)])) = 0 := by
    unfold fgSampleSpkC
    split_ifs <;>
      simp only [bindV, v, Comp.sampleIndexC, Expr.noneE, Expr.someE,
        compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
  have hI : compLitSize (fg2InitDsl S) ≤ 200 := by
    simp only [fg2InitDsl, emptySimE, emptyAuthStE, fsMk, stMk,
      Expr.litUnit, Expr.litBool, Expr.listNil, v, bindV, Comp.sampleBoolC,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add, hT, hSpk]
    omega
  have hF : compLitSize (fg2FinishDsl S K) ≤ 1000 := by
    simp only [fg2FinishDsl, fg2ExtractC, fg2InitDh1CandC, fg2RespCandC, fg2LogScanC, fg2FindMapC,
      fg2PaDh1, fg2PaU, fg2PaV, fsLog, fsBase, fsPows, fsResp,
      stSpks, stSess, stPrin, sbSpkPk, sbSpkSk, sePeerSpk, seSid, seEkASk, peIkAPk,
      slice32, bytesEmpty, zero32, natEq, nat2Eq,
      Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd, Comp.iteC, Comp.caseOptC,
      Expr.findBounded, Expr.mapBounded, Comp.findBoundedM, Comp.mapBoundedM, Comp.foldBoundedM,
      v, Comp.letC, bindV, letV, caseOptV, findMV, mapMV, foldMV,
      eCaseOpt, eCaseSum, eFind, eMap,
      Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
      Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
      Nat.add_zero, Nat.zero_add]
    omega
  have hS : compLitSize (fg2StepC (Δ := fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy]) S K
      (.vz : Var (fg2ParamsTy :: fg2GsTy :: [authQueryTy]) fg2ParamsTy)
      (.vz : Var (fgSimTy :: fg2ParamsTy :: fg2GsTy :: [authQueryTy]) fgSimTy)
      (.vs .vz : Var [fg2GsTy, authQueryTy] authQueryTy)) ≤ 18500 := by
    simp (config := { maxSteps := 1000000 }) only [fg2StepC, fg2InitPrinC, fg2GenSpkC, fg2SendC,
      fgRecvC, fgRecvB, fgRoC, fgRoRootC, fgRegisterC, onBaseF,
      isAdvPowsC, koskBundleOkPowsC, koskSenderOkPowsC, lookupSpkSkC,
      mkSecretPosC, mkPairPosC, twoSideC, twoSideOptC, ddhEqC, ddhEqOptC, entryMatchesC,
      patchC, rootPatchC, sendGuardE,
      fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows, fsMk, fsUpd,
      fg2PaU, fg2PaV, fg2PaDh1, fg2PaTI, fg2PaSendOpk, fg2PaSendIdx, fg2PaTS,
      feP1, feP2, feP3, feP4, feSs, feDk,
      pkP1, pkP2, pkP3, pkP4, pkSs, reRk, rePos, reRk1, reCk,
      q4, bytesEmpty, slice32, zero32, emptySimE,
      corruptB, genOpkB,
      findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
      resolveSigPkC, honestPeerC, hkdfOrRoC, rootRoC,
      stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb,
      stSOE, stSNE, stROE, stRNE, stRo, stRoot, stAdv, stMk, stUpd,
      seSid, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk, seSpkHon, seOpkHon, sePqspkHon,
      seEkASk, seEphASk, seFresh, seChal, seMk,
      pmHdr, pmEphAPk, pmPqMsg, pmAeadCt, pmMk, pmUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk, buUpd,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk, hdUpd,
      aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
      aDrKey, aRootKdf, rs, firstMsgADE, bytes2Eq, emptyAuthStE,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, kyberCheckE,
      natEq, nat2Eq, nat3Eq, optBytesEq, optU32Eq, sidEq, kyberEq, nonZero32, buildSecretsE, eLet2,
      Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
      Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
      Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
      Comp.foldBoundedM,
      ah_liftChal_litSize, ah_liftChal_gdh_litSize, v, Comp.letC, bindV, letV,
      caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV, eLet, eCaseOpt, eCaseSum,
      eFind, eAny, eMap,
      Expr.litBytes, Expr.bytesAppend, Expr.bytesCons, Expr.bytesWiden,
      Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq, Expr.bytesVarint,
      Expr.u32OfNat, Expr.u32Beq,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96,
      Comp.sampleIndex, Comp.queryPrim,
      Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C,
      Comp.sampleIndexC, Comp.queryPrimC, Comp.queryChal, AuthHs.Comp.queryDdh,
      encEC, encKEM,
      compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
      Nat.add_zero, Nat.zero_add,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
    omega
  have hH : compLitSize (fg2HandleDsl S K) ≤ 18600 := by
    simp only [fg2HandleDsl, fg2PaDh1, fg2PaTI, fsBase, stPrin, peCorrupted, aNone, natEq,
      Expr.litUnit, Expr.litBool, Expr.boolAnd, Comp.iteC, Expr.findBounded,
      v, Comp.letC, bindV, letV, eCaseOpt, eFind,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  change compLitSize (fg2InitDsl S) + compLitSize (fg2HandleDsl S K) + compLitSize (fg2FinishDsl S K) ≤ _
  omega

end AuthHsSizeBounds


section GapDhTight
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqSamplers
  eufCmaSignOracle gapDhDdhOracle sigAndDdhOracle

theorem fg_finish_cost_le_tight (S : Setup) (K : Nat) :
    (fgAuthGapDhProg S K).finish.cost ≤
      1000 + 1100 * K + 1000 * S.N_dh + 1000 * S.N_sess_tot +
        200 * (K * S.N_dh) + 200 * (S.N_dh * S.N_dh) + 50 * (S.N_dh * S.N_sess_tot) := by
  have h := fg_finish_cost_le_clamped S K
  have hd : min K S.N_dh ≤ S.N_dh := Nat.min_le_right K S.N_dh
  have hs : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right K S.N_sess_tot
  have h1 : K * min K S.N_dh ≤ K * S.N_dh := Nat.mul_le_mul_left K hd
  have h2 : min K S.N_dh * min K S.N_dh ≤ S.N_dh * S.N_dh := Nat.mul_le_mul hd hd
  have h3 : min K S.N_dh * min K S.N_sess_tot ≤ S.N_dh * S.N_sess_tot := Nat.mul_le_mul hd hs
  omega

end GapDhTight

section PrfCpaR64
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead

private def zP : pqPrimIface.Tag → ℕ := fun _ => 0
private def zMk : pqPrfMkIface.Tag → ℕ := fun _ => 0
private def r64S : pqPrimIface.smp.Samp → ℕ := r64W
private def r64SMk : pqPrfMkIface.smp.Samp → ℕ := r64W

@[simp] private theorem r64S_bool : r64S .bool = 0 := rfl
@[simp] private theorem r64S_bytes32 : r64S .bytes32 = 0 := rfl
@[simp] private theorem r64S_random64 : r64S .random64 = 1 := rfl
@[simp] private theorem r64S_drKey96 : r64S .drKey96 = 0 := rfl
@[simp] private theorem r64S_msgKeys80 : r64S .msgKeys80 = 0 := rfl
@[simp] private theorem r64S_index (n : ℕ) : r64S (.index n) = 0 := rfl
@[simp] private theorem r64SMk_bool : r64SMk .bool = 0 := rfl
@[simp] private theorem r64SMk_bytes32 : r64SMk .bytes32 = 0 := rfl
@[simp] private theorem r64SMk_random64 : r64SMk .random64 = 1 := rfl
@[simp] private theorem r64SMk_drKey96 : r64SMk .drKey96 = 0 := rfl
@[simp] private theorem r64SMk_msgKeys80 : r64SMk .msgKeys80 = 0 := rfl
@[simp] private theorem r64SMk_index (n : ℕ) : r64SMk (.index n) = 0 := rfl

@[simp] private theorem queries_authPrf_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (AuthPrf.Comp.letC e k).queries w ws = k.queries w ws := by
  simp [AuthPrf.Comp.letC, Comp.queries]

@[simp] private theorem queries_liftPrimComp_r64 {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := msgKeyPrfOracle) c).queries zMk r64SMk = c.queries zP r64S := by
  induction c with
  | ret _ | sample _ _ | query _ _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [liftPrimComp, Comp.queries, ih1, ih2]
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [liftPrimComp, Comp.queries, ih]

set_option linter.unusedSimpArgs false in
theorem prfCkRedProg_r64_le (S : Setup) (K q : ℕ) :
    (prfCkRedProg S K).totalQueries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) q ≤ 4 * q := by
  change (prfCkRedProg S K).totalQueries zP r64S q ≤ 4 * q
  have hI : (prfCkInitDslK S K).queries zP r64S = 0 := by
    simp [prfCkInitDslK, bindV, samplePrim, Comp.queries]
  have hF : (prfCkFinishDsl S K).queries zP r64S = 0 := by
    simp only [prfCkFinishDsl, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
      allHonestEcPksAuthDslK, letV, queries_authPrf_letC, queries_letC, samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries]
    omega
  have hH : (prfCkHandleDsl S K).queries zP r64S ≤ 4 := by
    dsimp only [prfCkHandleDsl, authCkStepC, authCkSendB, authCkRecvB]
    simp (config := { maxSteps := 20000000 }) only [sampAtCkC, sampCkPairC,
      initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
      registerFixedB, hkdfRoC, rootRoC, resolveSigPkC, checkBundleProvenanceExactC,
      checkBundleSpkHonIdealC, koskBundleOkC, koskSenderOkC, findHonestC, isAdvRegC,
      isGameSpkC, isGameOpkC, matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
      recvFinishTagRunC, prepareAuthHybridRecvC, finishAuthHybridSendC, finishAuthRecvCkC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      queries_authPrf_letC, queries_letC, samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    try simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  unfold CostedReduction.totalQueries prfCkRedProg
  dsimp only
  rw [hI, hF]
  have hMul := Nat.mul_le_mul_left q hH
  omega
set_option linter.unusedSimpArgs false in
theorem prfMsgKeysRedProg_r64_le (S : Setup) (K q : ℕ) :
    (prfMsgKeysRedProg S K).totalQueries (fun _ => 0) (sampR64W tlPrfMk.hsmp) q ≤ 4 * q := by
  change (prfMsgKeysRedProg S K).totalQueries zMk r64SMk q ≤ 4 * q
  have hI : (prfMsgKeysInitDslK S K).queries zMk r64SMk = 0 := by
    simp [prfMsgKeysInitDslK, bindV, sampleChal, Comp.queries]
  have hF : (prfMsgKeysFinishDsl S K).queries zMk r64SMk = 0 := by
    simp only [prfMsgKeysFinishDsl, finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl,
      allHonestEcPksAuthDslK, letV, queries_liftPrimComp_r64, queries_authPrf_letC, queries_letC,
      samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries]
    omega
  have hH : (prfMsgKeysHandleDsl S K).queries zMk r64SMk ≤ 4 := by
    dsimp only [prfMsgKeysHandleDsl, prfMkStepPreC, prfMkStepPostC, authMkSendPreB, authMkRecvPreB]
    simp (config := { maxSteps := 20000000 }) only [
      wrapMkBase, finishAuthSendMkC, finishAuthRecvMkC, finishRecvUnmatchedMkPreC,
      initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
      registerFixedB, hkdfRoC, rootRoC, resolveSigPkC, checkBundleProvenanceExactC,
      checkBundleSpkHonIdealC, koskBundleOkC, koskSenderOkC, findHonestC, isAdvRegC,
      isGameSpkC, isGameOpkC, matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
      recvFinishTagRunC, prepareAuthHybridRecvC, finishAuthHybridSendC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
      queries_liftPrimComp_r64, queries_authPrf_letC, queries_letC, samplePrim, queryPrim, queryDeriveMk,
      pqPrfMkIface, zP, zMk, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries, ite_true, ite_false, Bool.false_eq_true]
    try simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  unfold CostedReduction.totalQueries prfMsgKeysRedProg
  dsimp only
  rw [hI, hF]
  have hMul := Nat.mul_le_mul_left q hH
  omega

set_option linter.unusedSimpArgs false in
theorem aeadCpaRedProg_r64_le (S : Setup) (K q : ℕ) :
    (aeadCpaRedProg S K).totalQueries (fun _ => 0) (sampR64W tlAuthPrim.hsmp) q ≤ 4 * q := by
  change (aeadCpaRedProg S K).totalQueries zP r64S q ≤ 4 * q
  have hI : (aeadCpaRedProg S K).init.queries zP r64S = 0 := by
    simp [aeadCpaRedProg, authCodec, cpaInitC, bindV, samplePrim, Comp.queries]
  have hD : (aeadCpaRedProg S K).chDone.queries zP r64S = 0 := by
    simp [aeadCpaRedProg, authCodec, cpaDefaultChC, Comp.queries]
  have hR : (aeadCpaRedProg S K).resume.queries zP r64S = 0 := by
    simp [aeadCpaRedProg, authCodec, cpaResumeC, letV, bindV, finishCpaC,
      queries_authPrf_letC, queries_letC, Comp.queries]
  have hF : (aeadCpaRedProg S K).finish.queries zP r64S = 0 := by
    simp only [aeadCpaRedProg, authCodec, cpaFinishC, finalizeAuthFixedDsl,
      finalizeAuthFixedBodyDsl, allHonestEcPksAuthDslK, letV, queries_authPrf_letC, queries_letC,
      samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries]
    omega
  have hPre : (aeadCpaRedProg S K).handlePre.queries zP r64S ≤ 4 := by
    dsimp only [aeadCpaRedProg, authCodec, cpaPreC, cpaStepC, cpaNonSendSlotC]
    simp (config := { maxSteps := 20000000 }) only [wrapCpaSlot,
      cpaSendSlotB, cpaRecvC, finishCpaC, spkHonIdealFromPeerC, checkBundleProvenanceExactC,
      koskBundleOkC, koskSenderOkC, matchIdealAuthHandshakeC, hkdfRoC, rootRoC,
      initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
      registerFixedB, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      queries_authPrf_letC, queries_letC, samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    try simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  have hPost : (aeadCpaRedProg S K).handlePost.queries zP r64S ≤ 4 := by
    dsimp only [aeadCpaRedProg, authCodec, cpaPostC, cpaStepC, cpaNonSendSlotC]
    simp (config := { maxSteps := 20000000 }) only [wrapCpaSlot,
      cpaSendSlotB, cpaRecvC, finishCpaC, spkHonIdealFromPeerC, checkBundleProvenanceExactC,
      koskBundleOkC, koskSenderOkC, matchIdealAuthHandshakeC, hkdfRoC, rootRoC,
      initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
      registerFixedB, findHonestC, isAdvRegC, isGameSpkC, isGameOpkC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV,
      queries_authPrf_letC, queries_letC, samplePrim, queryPrim, zP, r64S_bool, r64S_bytes32, r64S_random64, r64S_drKey96, r64S_msgKeys80, r64S_index, r64SMk_bool, r64SMk_bytes32, r64SMk_random64, r64SMk_drKey96, r64SMk_msgKeys80, r64SMk_index, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true, id_eq]
    try simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  unfold TwoStageCostedReduction.totalQueries
  rw [hI, hD, hR, hF]
  have hMax : max ((aeadCpaRedProg S K).handlePre.queries zP r64S)
      ((aeadCpaRedProg S K).handlePost.queries zP r64S) ≤ 4 := max_le hPre hPost
  have hMul := Nat.mul_le_mul_left q hMax
  omega

end PrfCpaR64

section AuthPrfCpaSizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)

@[simp] private theorem ap_liftPrimComp_litSize {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftPrimComp (C := C) c) = compLitSize c := by
  induction c <;> simp_all [liftPrimComp, compLitSize, pqChalIface, pqPrimIface]

@[simp] private theorem ap_liftPrimComp_mk_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqPrfMkIface) (liftPrimComp c) = compLitSize c := ap_liftPrimComp_litSize c

@[simp] private theorem ap_defaultMsgKeysE_litSize {Γ : List PT} :
    exprLitSize (defaultMsgKeysE (Γ := Γ)) = 0 := by
  simp [defaultMsgKeysE, litB, exprLitSize, pqOpLitSize]; exact ⟨rfl, rfl, rfl⟩

@[simp] private theorem ap_liftPrimComp_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := C) c).size = c.size := by
  induction c <;> simp_all [liftPrimComp, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem ap_liftPrimComp_mk_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfMkIface) (liftPrimComp c) = c.size := ap_liftPrimComp_size c

section ApAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {C : ChallengerOracle} {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[simp] private theorem ap_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem ap_letC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (AuthPrf.Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem ap_rletC_size (e : Expr pqxdhOps Γ τ₁) (k : Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (_root_.ReductionDsl.Comp.letC e k).size = e.size + 1 + k.size + 1 := rfl
@[simp] private theorem ap_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .zero).size + 1 := rfl
@[simp] private theorem ap_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .zero).size + 1 := rfl
@[simp] private theorem ap_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem ap_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] private theorem ap_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_consumeFirstMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool)
    (mark : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) τ) :
    (consumeFirstMV K xs p mark).size =
      xs.size + (p .zero).size + (mark .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl
@[simp] private theorem ap_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem ap_eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] private theorem ap_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl
@[simp] private theorem ap_litB_size (w : ℕ+) (bs : Bytes) : (litB w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ap_catB_size (m n : ℕ+) (a : Expr pqxdhOps Γ (B m))
    (b : Expr pqxdhOps Γ (B n)) : (catB m n a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ap_bytesCons_size (b : UInt8) (w : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (bytesCons b w x).size = x.size + 1 := rfl
@[simp] private theorem ap_widenB_size (w d : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (widenB w d x).size = x.size + 1 := rfl
@[simp] private theorem ap_takeKB_size (w k : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (takeKB w k x).size = x.size + 1 := rfl
@[simp] private theorem ap_bytesLen_size (w : ℕ+) (x : Expr pqxdhOps Γ (B w)) :
    (bytesLen w x).size = x.size + 1 := rfl
@[simp] private theorem ap_bytesBeq_size (w : ℕ+) (a b : Expr pqxdhOps Γ (B w)) :
    (bytesBeq w a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ap_bytesVarint_size (n : Expr pqxdhOps Γ .nat) :
    (bytesVarint n).size = n.size + 1 := rfl
@[simp] private theorem ap_u32OfNat_size (n : Expr pqxdhOps Γ .nat) :
    (u32OfNat n).size = n.size + 1 := rfl
@[simp] private theorem ap_u32Beq_size (a b : Expr pqxdhOps Γ U32) :
    (u32Beq a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem ap_samplePrim_size (s : PSamp) :
    (samplePrim s (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ap_sampleChal_size (s : PSamp) :
    (sampleChal (C := C) s (Γ := Γ)).size = 2 := rfl
@[simp] private theorem ap_queryPrim_size (g : PTag) (e : Expr pqxdhOps Γ g.dom) :
    (queryPrim g e).size = e.size + 1 := rfl
@[simp] private theorem ap_queryDeriveMk_size (e : Expr pqxdhOps Γ (.opt (B 32))) :
    (queryDeriveMk e).size = e.size + 1 := rfl
@[simp] private theorem ap_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem ap_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) :
    (encKEM e).size = e.size + 1 := rfl

end ApAtomicSizeSimp

private theorem ap_bits_mono {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem ap_eff_le_dh (S : Setup) :
    (if S.N_id = 0 then 0 else S.N_send_opk) ≤ S.N_dh ∧
    (if S.N_id = 0 then 0 else S.N_send_no_opk) ≤ S.N_dh := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hso : S.N_send_opk_tot = S.N_id * S.N_send_opk := rfl
  have hsn : S.N_send_no_opk_tot = S.N_id * S.N_send_no_opk := rfl
  split_ifs with h0
  · omega
  · have hpos : 1 ≤ S.N_id := by omega
    have h1 : S.N_send_opk ≤ S.N_id * S.N_send_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_opk hpos
    have h2 : S.N_send_no_opk ≤ S.N_id * S.N_send_no_opk := by
      simpa using Nat.mul_le_mul_right S.N_send_no_opk hpos
    omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_recvFinishTagRunC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).size =
      res?.size + bits K + 4 * bits (min K S.N_dh) + 1864 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, Comp.size, Expr.size]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_prepareAuthHybridRecvC_true_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      6 * bits K + 3 * bits (min K S.N_dh) + 875 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_prepareAuthHybridRecvC_false_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      5 * bits K + 3 * bits (min K S.N_dh) + 813 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_finishAuthHybridSendC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).size =
      args.size + 4 * bits (min K S.N_dh) + 2 * bits K + 1040 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV,
    eCaseOpt, eAny, bytesBeq, queryPrim, Comp.size, Expr.size]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_finalizeAuthFixedDsl_size (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).size =
      4 * bits (min K S.N_dh) + 5 * bits (4 * min K S.N_dh) + 7 * bits K + 292 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDslK,
    hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, samplePrim, queryPrim, Comp.size, Expr.size]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ap_prfCkRedProg_size_bounds (S : Setup) (K : Nat) :
    (prfCkRedProg S K).size ≤
      90 * bits K + 120 * bits (min K S.N_dh) + 5 * bits (4 * min K S.N_dh) +
        20 * bits (min K S.N_sess_tot) + 49900 := by
  dsimp only [prfCkRedProg, CostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    prfCkInitDslK, prfCkHandleDsl, prfCkFinishDsl,
    ckSecb, ckIdx, ckChal, ckFhst,
    sampCkPairC, sampAtCkC, authCkSendB, finishAuthRecvCkC, authCkRecvB, authCkStepC,
    ap_recvFinishTagRunC_size, ap_prepareAuthHybridRecvC_true_size,
    ap_prepareAuthHybridRecvC_false_size, ap_finishAuthHybridSendC_size, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  omega

theorem ap_prfCkRedProg_size_le (S : Setup) (K : Nat) :
    (prfCkRedProg S K).size ≤
      90 * bits K + 125 * bits S.N_dh + 20 * bits S.N_sess_tot + 50000 := by
  have h := ap_prfCkRedProg_size_bounds S K
  have h1 : bits (min K S.N_dh) ≤ bits S.N_dh := ap_bits_mono (Nat.min_le_right _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ap_bits_mono (Nat.min_le_right _ _)
  have h4 : bits (4 * min K S.N_dh) ≤ bits S.N_dh + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 S.N_dh
    have hb4 : bits 4 = 3 := by decide
    have hmle := ap_bits_mono (Nat.mul_le_mul_left 4 (Nat.min_le_right K S.N_dh))
    omega
  omega

private theorem ap_prfCkRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfCkRedProg S K).size ≤ 250 * bits K + 55000 := by
  have h := ap_prfCkRedProg_size_bounds S K
  have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h4 : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have hb4 : bits 4 = 3 := by decide
    omega
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ap_prfMsgKeysRedProg_size_bounds (S : Setup) (K : Nat) :
    (prfMsgKeysRedProg S K).size ≤
      110 * bits K + 215 * bits (min K S.N_dh) + 10 * bits (4 * min K S.N_dh) +
        10 * bits (min K S.N_recv_tot + 1) + 10 * bits (min K S.N_sess_tot) + 94900 := by
  dsimp only [prfMsgKeysRedProg, CostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    prfMsgKeysInitDslK, prfMsgKeysHandleDsl, prfMsgKeysFinishDsl,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    wrapMkBase, finishAuthSendMkC, finishAuthRecvMkC, authMkSendPreB,
    finishRecvUnmatchedMkPreC, authMkRecvPreB, prfMkStepPreC, prfMkStepPostC,
    ap_recvFinishTagRunC_size, ap_prepareAuthHybridRecvC_true_size,
    ap_prepareAuthHybridRecvC_false_size, ap_finishAuthHybridSendC_size, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_size, ap_liftPrimComp_mk_size,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim, queryDeriveMk,
    encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  omega

theorem ap_prfMsgKeysRedProg_size_le (S : Setup) (K : Nat) :
    (prfMsgKeysRedProg S K).size ≤
      110 * bits K + 225 * bits S.N_dh + 20 * bits S.N_sess_tot + 95000 := by
  have h := ap_prfMsgKeysRedProg_size_bounds S K
  have h1 : bits (min K S.N_dh) ≤ bits S.N_dh := ap_bits_mono (Nat.min_le_right _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ap_bits_mono (Nat.min_le_right _ _)
  have h4 : bits (4 * min K S.N_dh) ≤ bits S.N_dh + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 S.N_dh
    have hb4 : bits 4 = 3 := by decide
    have hmle := ap_bits_mono (Nat.mul_le_mul_left 4 (Nat.min_le_right K S.N_dh))
    omega
  have bMinRecv : bits (min K S.N_recv_tot + 1) ≤ bits S.N_sess_tot + 2 := by
    have hss : S.N_sess_tot = S.N_send_tot + S.N_recv_tot := rfl
    rcases Nat.eq_zero_or_pos S.N_sess_tot with h0 | hpos
    · have h1r : S.N_recv_tot = 0 := by omega
      have hmin0 : min K S.N_recv_tot = 0 := by omega
      rw [hmin0, h0]; decide
    · have hle := ap_bits_mono (show min K S.N_recv_tot + 1 ≤ 2 * S.N_sess_tot by
        have := Nat.min_le_right K S.N_recv_tot; omega)
      have hm := _root_.ReductionDsl.bits_mul 2 S.N_sess_tot
      have hb2 : bits 2 = 2 := by decide
      omega
  omega

private theorem ap_prfMsgKeysRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfMsgKeysRedProg S K).size ≤ 355 * bits K + 98000 := by
  have h := ap_prfMsgKeysRedProg_size_bounds S K
  have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h4 : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have hb4 : bits 4 = 3 := by decide
    omega
  have bMinRecv : bits (min K S.N_recv_tot + 1) ≤ bits K + 2 := by
    rcases Nat.eq_zero_or_pos K with rfl | hpos
    · simp
    · have hle := ap_bits_mono (show min K S.N_recv_tot + 1 ≤ 2 * K by
        have := Nat.min_le_left K S.N_recv_tot; omega)
      have hm := _root_.ReductionDsl.bits_mul 2 K
      have hb2 : bits 2 = 2 := by decide
      omega
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem ap_aeadCpaRedProg_size_bounds (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).size ≤
      150 * bits K + 215 * bits (min K S.N_dh) + 15 * bits (4 * min K S.N_dh) +
        10 * bits (min K S.N_send_tot) + 5 * bits (min K S.N_sess_tot) + 49900 := by
  dsimp only [aeadCpaRedProg, TwoStageCostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    cpaInitC, cpaPreC, cpaDefaultChC, cpaResumeC, cpaPostC, cpaFinishC,
    cpaStepC, cpaNonSendSlotC, wrapCpaSlot, cpaSendSlotB, cpaRecvC, finishCpaC, spkHonIdealFromPeerC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    ap_recvFinishTagRunC_size, ap_prepareAuthHybridRecvC_true_size,
    ap_prepareAuthHybridRecvC_false_size, ap_finishAuthHybridSendC_size, ap_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]; dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum, _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  omega

theorem ap_aeadCpaRedProg_size_le (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).size ≤
      155 * bits K + 245 * bits S.N_dh + 5 * bits S.N_sess_tot + 50000 := by
  have h := ap_aeadCpaRedProg_size_bounds S K
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have bSend : bits S.N_send_tot ≤ bits S.N_dh := ap_bits_mono (by omega)
  have h1 : bits (min K S.N_dh) ≤ bits S.N_dh := ap_bits_mono (Nat.min_le_right _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := ap_bits_mono (Nat.min_le_right _ _)
  have hSend : bits (min K S.N_send_tot) ≤ bits S.N_dh :=
    (ap_bits_mono (Nat.min_le_right K S.N_send_tot)).trans bSend
  have h4 : bits (4 * min K S.N_dh) ≤ bits S.N_dh + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 S.N_dh
    have hb4 : bits 4 = 3 := by decide
    have hmle := ap_bits_mono (Nat.mul_le_mul_left 4 (Nat.min_le_right K S.N_dh))
    omega
  omega

private theorem ap_aeadCpaRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (aeadCpaRedProg S K).size ≤ 400 * bits K + 55000 := by
  have h := ap_aeadCpaRedProg_size_bounds S K
  have h1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h2 : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hSend : bits (min K S.N_send_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have h4 : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have hb4 : bits 4 = 3 := by decide
    omega
  omega

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_recvFinishTagRunC_litSize (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    compLitSize (recvFinishTagRunC S K tag res?) = exprLitSize res? := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_prepareAuthHybridRecvC_true_litSize (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)) = 64 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add, ↓reduceIte]

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_prepareAuthHybridRecvC_false_litSize (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)) = 64 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add, ↓reduceIte, Bool.false_eq_true]

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_finishAuthHybridSendC_litSize (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    compLitSize (finishAuthHybridSendC S K hst args) = exprLitSize args := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV,
    eCaseOpt, eAny, bytesBeq, queryPrim, compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
@[simp] private theorem ap_finalizeAuthFixedDsl_litSize (S : Setup) (K : Nat) {Γ : List PT} :
    compLitSize (finalizeAuthFixedDsl S K (Γ := Γ)) = 0 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDslK,
    hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, samplePrim, queryPrim, compLitSize, exprLitSize, pqOpLitSize]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ap_prfCkRedProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfCkRedProg S K) ≤ 20000 := by
  dsimp only [prfCkRedProg, red1LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    prfCkInitDslK, prfCkHandleDsl, prfCkFinishDsl,
    ckSecb, ckIdx, ckChal, ckFhst,
    sampCkPairC, sampAtCkC, authCkSendB, finishAuthRecvCkC, authCkRecvB, authCkStepC,
    ap_recvFinishTagRunC_litSize, ap_prepareAuthHybridRecvC_true_litSize,
    ap_prepareAuthHybridRecvC_false_litSize, ap_finishAuthHybridSendC_litSize, ap_finalizeAuthFixedDsl_litSize,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ap_prfMsgKeysRedProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfMsgKeysRedProg S K) ≤ 20000 := by
  dsimp only [prfMsgKeysRedProg, red1LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    prfMsgKeysInitDslK, prfMsgKeysHandleDsl, prfMsgKeysFinishDsl,
    mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
    wrapMkBase, finishAuthSendMkC, finishAuthRecvMkC, authMkSendPreB,
    finishRecvUnmatchedMkPreC, authMkRecvPreB, prfMkStepPreC, prfMkStepPostC,
    ap_recvFinishTagRunC_litSize, ap_prepareAuthHybridRecvC_true_litSize,
    ap_prepareAuthHybridRecvC_false_litSize, ap_finishAuthHybridSendC_litSize, ap_finalizeAuthFixedDsl_litSize,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_litSize, ap_liftPrimComp_mk_litSize,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim, queryDeriveMk,
    encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem ap_aeadCpaRedProg_litSize_le (S : Setup) (K : Nat) :
    red2LitSize (aeadCpaRedProg S K) ≤ 20000 := by
  dsimp only [aeadCpaRedProg, red2LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    cpaInitC, cpaPreC, cpaDefaultChC, cpaResumeC, cpaPostC, cpaFinishC,
    cpaStepC, cpaNonSendSlotC, wrapCpaSlot, cpaSendSlotB, cpaRecvC, finishCpaC, spkHonIdealFromPeerC,
    getDBytes, ap_defaultMsgKeysE_litSize, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    ap_recvFinishTagRunC_litSize, ap_prepareAuthHybridRecvC_true_litSize,
    ap_prepareAuthHybridRecvC_false_litSize, ap_finishAuthHybridSendC_litSize, ap_finalizeAuthFixedDsl_litSize,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMkSlots, ahsfMk, ahsfUpdSlots, ahsfUpd,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, queryPrim, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  omega

end AuthPrfCpaSizeBounds

section AuthPrfHmacSizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.SignalPqxdh.AtomicLift (pqOpLitSize exprLitSize compLitSize red1LitSize red2LitSize)

@[simp] private theorem hm_liftPrimComp_hmac_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (I := pqPrfHmacIface) (liftPrimComp c) = compLitSize c := ap_liftPrimComp_litSize c

section HmAtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ : List PT} {τ₁ τ₂ : PT}

@[simp] private theorem hm_bytesTake_size (w : ℕ+) (n : Expr pqxdhOps Γ .nat)
    (x : Expr pqxdhOps Γ (B w)) :
    (AuthPrfHmac.bytesTake w n x).size = n.size + x.size + 2 := rfl
@[simp] private theorem hm_bytesDrop_size (w : ℕ+) (n : Expr pqxdhOps Γ .nat)
    (x : Expr pqxdhOps Γ (B w)) :
    (AuthPrfHmac.bytesDrop w n x).size = n.size + x.size + 2 := rfl
@[simp] private theorem hm_queryHmacEval_size (x : Expr pqxdhOps Γ (B 359)) :
    (queryHmacEval x).size = x.size + 1 := rfl
@[simp] private theorem hm_mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (AuthPrfHmac.mapMV K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl

end HmAtomicSizeSimp

@[simp] private theorem hm_liftPrimComp_hmac_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    Comp.size (I := pqPrfHmacIface) (liftPrimComp c) = c.size := ap_liftPrimComp_size c

set_option linter.unusedSimpArgs false in
private theorem sc_recvFinishTagRunC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy) [Ext Γ₁ Δ] :
    (recvFinishTagRunC S K tag res?).size =
      res?.size + bits K + 4 * bits (min K S.N_dh) + 1864 := by
  simp only [recvFinishTagRunC, findHonestC, matchSentOPKC, matchSentNoOPKC,
    natEq, nat2Eq, nat3Eq, oeMk, oeUpd, roMk, rnoMk, stMk, stUpd, ahsMk, ahsUpd,
    aNone, aRecvHonest, aRecvUnfresh, peIkAPk, peCorrupted,
    sbSpkPk, sbPqspkPk, oeOpkSk, oeOpkPk, hdrIkAPk, hdrEkAPk, hdrKemCt,
    pkmHdr, soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched, snoA0, snoB0,
    snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched, roBCorr, roA0, roB0, roSb, roOb,
    roA1, roPk1, roCt, roM, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM, asSecb,
    asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions,
    asUsedRecvOPK, asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents,
    asRecvdNoOPKEvents, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    boolOr, Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, consumeFirstMV, eMap,
    bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
private theorem sc_prepareAuthHybridRecvC_true_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K true hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      6 * bits K + 3 * bits (min K S.N_dh) + 875 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    oeOpkSk, oeOpkPk, oeConsumed, hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk,
    iasPeerPqspkPk, iasKemCt, iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asUsedRecvOPK, asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
private theorem sc_prepareAuthHybridRecvC_false_size (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prepareAuthHybridRecvC S K false hst x :
      Comp pqxdhOps pqPrimIface Δ (.opt preparedAuthRecvTy)).size =
      5 * bits K + 3 * bits (min K S.N_dh) + 813 := by
  simp only [prepareAuthHybridRecvC, koskSenderOkC, findHonestC, isAdvRegC,
    matchIdealAuthHandshakeC, natEq, nat2Eq, nat3Eq, optU32Eq, kyberCheckE, buildSecretsE,
    kyberEq, isSomeE, eLet2, boolOr, rkrMk,
    ahsMk, ahsUpd, peSecIKA0, peIkAPk, peCorrupted, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt, pkmHdr, pkmEphAPk,
    iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk, iasKemCt,
    iasEphAPk, asHasWonAuth, asPrincipals, asSpkBundles, asUsedRecvNoOPK,
    asUsedKyberTriples, asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV,
    eLet, eFind, eAny, eCaseOpt,
    litB, catB, bytesCons, widenB, takeKB, bytesLen, bytesBeq, u32OfNat, u32Beq,
    queryPrim, encEC, encKEM, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have hb32 : bits 32 = 6 := by decide
  omega

set_option linter.unusedSimpArgs false in
private theorem sc_finishAuthHybridSendC_size (S : Setup) (K : Nat) {Γ₁ Δ : List PT}
    (hst : Var Γ₁ authHybridStateTy) (args : Expr pqxdhOps Δ finishSendArgsTy) [Ext Γ₁ Δ] :
    (finishAuthHybridSendC S K hst args).size =
      args.size + 4 * bits (min K S.N_dh) + 2 * bits K + 1040 := by
  simp only [finishAuthHybridSendC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    findHonestC, natEq, isSomeE, boolOr,
    optFst, optSnd, hdMk, pmMk, seMk, iasMk, soMk, snoMk, ikrMk, stMk, stUpd, ahsMk, ahsUpd,
    aSendFresh, aSendUnfresh, peIkAPk, peCorrupted, sbSpkPk, sbPqspkPk, oeOpkPk, pkbIkB, pkbSpkId,
    pkbSpkB, pkbOpkB?, pkbPqspkId, pkbPqspkB, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
    asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
    asUsedKyberTriples, asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV, caseOptV, findMV, anyMV,
    eCaseOpt, eAny, bytesBeq, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
private theorem sc_finalizeAuthFixedDsl_size (S : Setup) (K : Nat) {Γ : List PT} :
    (finalizeAuthFixedDsl S K (Γ := Γ)).size =
      4 * bits (min K S.N_dh) + 5 * bits (4 * min K S.N_dh) + 7 * bits K + 292 := by
  simp only [finalizeAuthFixedDsl, finalizeAuthFixedBodyDsl, allHonestEcPksAuthDslK,
    hasDuplicateBytesDsl, hasBadSigAuthDsl, hasKemPkCollisionAuthDsl,
    hasBadKemShCrRecordsDsl, notAllChallengedCleanDsl,
    asHasWonAuth, asSessions, asSpkBundles, asPrincipals, asOpkEntries,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
    aseFresh, aseSpkHonest, asePqspkHonest, aseChallenged, aseEkASk,
    peIkAPk, sbSpkPk, sbPqspkPk, oeOpkPk,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    boolOr, boolBeq,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    eLet, eAny, eMap, bytesBeq, samplePrim, queryPrim, Comp.size, Expr.size]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem hm_prfHmacRedProg_size_le_clamped (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).size ≤ 120 * bits K + 35000 := by
  dsimp only [prfHmacRedProg, CostedReduction.size]
  simp (config := { maxSteps := 1000000 }) only [
    hmInitC, hmHandleC, hmFinishC, hmPreC, hmContX0E, hmPostC, hmDispatchC, hmOther,
    hmKeyIdC, hmKeyC, encPostC, hmEncPreIdC, hmEncPreC, hmForgeIdC, hmForgeC,
    finishIntC, intSendPrepC, sendSidE, hmSendTailC, hmSendC,
    hmRecvPrepC, hmSchedPrepC, forgeRetIdC, forgeRetC, hmSchedFinC, hmSchedC, finErasedE,
    hmRecvTailC, hmRecvC,
    natLe, muKeys, muChal, muPend, muBad, muMk, emptyMuE,
    etmBodyE, etmBody24E, etmTagE, macInputE, initSlotE, muKeyIdEq, initKeyIdE,
    pendFilterE, pendHitE, dedupE,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey, ipRks4,
    ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
    getDBytes, defaultMsgKeysE, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    spkHonIdealFromPeerC,
    sc_recvFinishTagRunC_size, sc_prepareAuthHybridRecvC_true_size,
    sc_prepareAuthHybridRecvC_false_size, sc_finishAuthHybridSendC_size, sc_finalizeAuthFixedDsl_size,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd, ahsfMkSlots, ahsfUpdSlots,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_size, hm_liftPrimComp_hmac_size,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim,
    encEC, encKEM,
    AuthPrfHmac.bytesTake, AuthPrfHmac.bytesDrop, queryHmacEval, AuthPrfHmac.mapMV,
    Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  dsimp only [_root_.SignalPqxdh.LegacyCosted.pqxdhOps, _root_.ReductionDsl.Ops.sum,
    _root_.SignalPqxdh.LegacyCosted.pqBytesOps, _root_.SignalPqxdh.LegacyCosted.pqU32Ops, Sum.elim]
  have bHdr : bits firstMsgHdrLen ≤ 16 := by decide
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb8 : bits 8 = 4 := by decide
  have hb24 : bits 24 = 5 := by decide
  have hb32 : bits 32 = 6 := by decide
  have hb64 : bits 64 = 7 := by decide
  have hb96 : bits 96 = 7 := by decide
  have hb128 : bits 128 = 8 := by decide
  have hb160 : bits 160 = 8 := by decide
  have hb192 : bits 192 = 8 := by decide
  have hK1 : bits (min K S.N_dh) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hK2 : bits (min K S.N_sess_tot) ≤ bits K := ap_bits_mono (Nat.min_le_left _ _)
  have hK4 : bits (4 * min K S.N_dh) ≤ bits K + 3 := by
    have hm := _root_.ReductionDsl.bits_mul 4 (min K S.N_dh)
    have hb4 : bits 4 = 3 := by decide
    omega
  omega

theorem hm_prfHmacRedProg_size_le (S : Setup) (K : Nat) :
    (prfHmacRedProg S K).size ≤
      120 * bits K + 80 * bits S.N_dh + 20 * bits S.N_sess_tot + 35000 := by
  have h := hm_prfHmacRedProg_size_le_clamped S K
  omega

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem hm_prfHmacRedProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (prfHmacRedProg S K) ≤ 20000 := by
  dsimp only [prfHmacRedProg, red1LitSize]
  simp (config := { maxSteps := 1000000 }) only [
    hmInitC, hmHandleC, hmFinishC, hmPreC, hmContX0E, hmPostC, hmDispatchC, hmOther,
    hmKeyIdC, hmKeyC, encPostC, hmEncPreIdC, hmEncPreC, hmForgeIdC, hmForgeC,
    finishIntC, intSendPrepC, sendSidE, hmSendTailC, hmSendC,
    hmRecvPrepC, hmSchedPrepC, forgeRetIdC, forgeRetC, hmSchedFinC, hmSchedC, finErasedE,
    hmRecvTailC, hmRecvC,
    natLe, muKeys, muChal, muPend, muBad, muMk, emptyMuE,
    etmBodyE, etmBody24E, etmTagE, macInputE, initSlotE, muKeyIdEq, initKeyIdE,
    pendFilterE, pendHitE, dedupE,
    ipUEntry, ipPeer, ipFim, ipFresh, ipIdeal, ipMsgPlain, ipT3, ipKeys6, ipDrKey, ipRks4,
    ipSalt, ipPqMsg, ipAd, ipProv, ipRoC, ipRootC,
    getDBytes, ap_defaultMsgKeysE_litSize, iasAdE, iasAeadCtE, iasMsgPlainE, iasCk1_0E,
    spkHonIdealFromPeerC,
    ap_recvFinishTagRunC_litSize, ap_prepareAuthHybridRecvC_true_litSize,
    ap_prepareAuthHybridRecvC_false_litSize, ap_finishAuthHybridSendC_litSize, ap_finalizeAuthFixedDsl_litSize,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskBundleOkC, koskSenderOkC,
    resolveSigPkC, hkdfRoC, rootRoC, checkBundleProvenanceExactC, checkBundleSpkHonIdealC,
    matchSentOPKC, matchSentNoOPKC, matchIdealAuthHandshakeC,
    parKEntry, parSecrets, parDhRatchet, parIsUncorrSender,
    parMatchedSess?, parSameEph, parHstDec, parFinishTag, fhstSetBase,
    initPrinFixedB, corruptFixedB, genSpkFixedB, genOpkFixedB, roFixedB, roRootFixedB,
    registerFixedB,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted,
    sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk, oeOpkSk, oeOpkPk, oeConsumed,
    pkbIkB, pkbSpkId, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkId, pkbPqspkB, pkbPqspkSig,
    hdrIkAPk, hdrEkAPk, hdrSpkId, hdrOpkId?, hdrPqspkId, hdrKemCt,
    pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched, soMarkMatched,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched, snoMarkMatched,
    roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    aseSpkHonest, asePqspkHonest, aseEkASk, aseFresh, aseChallenged,
    ikrPqspkPk, ikrKemCt, ikrKemSs, rkrPqspkPk, rkrKemCt, rkrKemSs,
    iasSid, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?, iasEkAPk, iasPeerPqspkPk,
    iasKemCt, iasEphAPk, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
    asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys,
    ahsBase, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots,
    assNext, assSendOpk, assSendNoOpk, assRecv, assMk, emptyAuthSlotStE,
    lookupSendSlotE, lookupSendSlotOrZeroE, allocSendSlotE,
    lookupRecvSlotE, lookupRecvSlotOrZeroE, allocRecvSlotE,
    natEq, natLt, nat2Eq, nat3Eq, bytes2Eq, optU32Eq, sidEq, saltBytesE, sameSaltKeyE, kyberEq,
    isSomeE, optFst, optSnd, firstMsgADE, buildSecretsE, kyberCheckE, sessionSlotIndexE,
    peMk, peUpd, sbMk, oeMk, oeUpd, buMk, hdMk, pmMk, seMk, iasMk, soMk, snoMk, roMk, rnoMk,
    ikrMk, rkrMk, stMk, stUpd, ahsMk, ahsUpd, ahsfMk, ahsfUpd, ahsfMkSlots, ahsfUpdSlots,
    emptyAuthStE, emptyAuthHybridStE, emptyAuthHybridStFixedE,
    aNone, aInitPrin, aPk, aCorr, aBundle, aSendFresh, aSendUnfresh, aRecvHonest, aRecvUnfresh,
    aDrKey, aRootKdf, sendGuardE, boolOr, boolBeq, eLet2,
    Expr.litUnit, Expr.litBool, Expr.litNat, Expr.noneE, Expr.someE, Expr.boolNot, Expr.boolAnd,
    Expr.boolOr, Expr.listNil, Expr.listCons, Expr.findBounded, Expr.anyBounded, Expr.mapBounded,
    Comp.iteC, Comp.caseOptC, Comp.caseSumC, Comp.findBoundedM, Comp.anyBoundedM, Comp.mapBoundedM,
    Comp.foldBoundedM,
    ap_liftPrimComp_litSize, hm_liftPrimComp_hmac_litSize,
    v, AuthPrf.Comp.letC, _root_.ReductionDsl.Comp.letC, bindV, letV,
    caseOptV, caseSumV, findMV, anyMV, consumeFirstMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, bytesCons, widenB, takeKB,
    bytesLen, bytesBeq, bytesVarint, u32OfNat, u32Beq,
    samplePrim, sampleChal, queryPrim,
    encEC, encKEM,
    AuthPrfHmac.bytesTake, AuthPrfHmac.bytesDrop, queryHmacEval, AuthPrfHmac.mapMV,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, hl_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false, id_eq]
  omega

end AuthPrfHmacSizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed (pqPrimIface pqxdhEufCmaIface pqGapDhIface pqAuthPrimIface pqAuthEufCmaIface pqAuthGapDhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd hiding bits_0 bits_1 bits_2 bits_3 bits_32
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open OracleSpec OracleComp


/-! ## Lifted atomic reductions and step-cost bounds -/

def sigKeyIndAtomicProg (useRo : Bool) (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqxdhEufCmaIface (keyIndSpec S) (pqKeyIndCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftKeyInd1Stage tlEufCmaKeyInd S (sigKeyIndDslProg useRo S b)

def shcrKeyIndAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftKeyInd2Stage tlPrimKeyInd S (shcrKeyIndDslProg S b)

def fgKeyIndGapDhAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqGapDhIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)

def sigReductionAuthAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthEufCmaIface (authSpec S) (authCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftAuth1Stage tlAuthEufCma S (sigReductionAuthDslProg2 S b)

def shcrAuthAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftAuth2Stage tlAuthPrim S (shcrAuthDslProg S b)

def fgAuthGapDhAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthGapDhIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftAuth1Stage tlAuthGapDh S (fgAuthGapDhDslProg S b)

def prfCkAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool .bool :=
  liftAuth1Stage tlAuthPrim S (prfCkRedProg S b.q_total)

def prfMsgKeysAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg S b.q_total)

def aeadCpaAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
      (.opt (PB 32)) .bool :=
  liftAuth2Stage tlAuthPrim S (aeadCpaDslProg S b)

def prfHmacAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  liftAuth1Stage tlPrfHmac S (prfHmacDslProg S b)

private theorem eleven_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h11 : 11 * c ≤ 720896 + 1441792 * b.q_total +
      360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      720896 * (b.q_total * b.q_total) +
      360448 * (b.q_total * min b.q_total S.N_dh) +
      360448 * (b.q_total * min b.q_total S.N_sess_tot) +
      22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hEq : 11 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      720896 + 1441792 * b.q_total +
        360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
        11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        720896 * (b.q_total * b.q_total) +
        360448 * (b.q_total * min b.q_total S.N_dh) +
        360448 * (b.q_total * min b.q_total S.N_sess_tot) +
        22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h11.trans_eq hEq.symm) (by omega)

private theorem two_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h2 : 2 * c ≤ 131072 + 262144 * b.q_total +
      65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      131072 * (b.q_total * b.q_total) +
      65536 * (b.q_total * min b.q_total S.N_dh) +
      65536 * (b.q_total * min b.q_total S.N_sess_tot) +
      4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hEq : 2 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      131072 + 262144 * b.q_total +
        65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
        2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        131072 * (b.q_total * b.q_total) +
        65536 * (b.q_total * min b.q_total S.N_dh) +
        65536 * (b.q_total * min b.q_total S.N_sess_tot) +
        4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h2.trans_eq hEq.symm) (by omega)

end Proofs.SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

section FgKeyIndGapDh2Helpers

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd hiding bits_0 bits_1 bits_2 bits_3 bits_32
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

private theorem fg2_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem fg2_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

private theorem fg2_bernoulliRatioGdhC_costUB_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).costUB ≤
      if A = 0 ∨ B = 0 then 2 else 3 * _root_.ReductionDsl.bits (A + B) + 25 := by
  unfold bernoulliRatioGdhC
  by_cases hA : A = 0
  · simp [hA, Comp.costUB, Expr.costUB]
  by_cases hB : B = 0
  · simp [hA, hB, Comp.costUB, Expr.costUB]
  simp only [hA, hB, or_self, ↓reduceIte]
  split_ifs with hle
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : _root_.ReductionDsl.bits A ≤ _root_.ReductionDsl.bits (A + B) :=
      _root_.ReductionDsl.bits_mono (by omega)
    omega
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : _root_.ReductionDsl.bits B ≤ _root_.ReductionDsl.bits (A + B) :=
      _root_.ReductionDsl.bits_mono (by omega)
    omega

private theorem fg2_coordSamplers2_costUB_le (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).costUB ≤ _root_.ReductionDsl.bits S.N_dh + 10 ∧
    (sampleSpkPair2C S (Δ := Δ)).costUB ≤ 2 * _root_.ReductionDsl.bits S.N_dh + 15 ∧
    (sampleOpkTriple2C S (Δ := Δ)).costUB ≤ 3 * _root_.ReductionDsl.bits S.N_dh + 20 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * _root_.ReductionDsl.bits S.N_dh + 20 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * _root_.ReductionDsl.bits S.N_dh + 20 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C
    split_ifs
    · simp [Comp.costUB, Expr.costUB]
    · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm := _root_.ReductionDsl.bits_mono (show S.N_id ≤ S.N_dh by omega)
      omega
  · unfold sampleSpkPair2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 := _root_.ReductionDsl.bits_mono (show S.N_id ≤ S.N_dh by omega)
      have bm2 := _root_.ReductionDsl.bits_mono (show S.N_recv ≤ S.N_dh by omega)
      omega
  · unfold sampleOpkTriple2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hSpk : 0 < S.N_spk_tot := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_opk_tot, hc])
      have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc =>
        Nat.ne_of_gt hSpk (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      have hO : S.N_opk ≤ S.N_opk_tot := Nat.le_mul_of_pos_left _ hSpk
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 := _root_.ReductionDsl.bits_mono (show S.N_id ≤ S.N_dh by omega)
      have bm2 := _root_.ReductionDsl.bits_mono (show S.N_recv ≤ S.N_dh by omega)
      have bm3 := _root_.ReductionDsl.bits_mono (show S.N_opk ≤ S.N_dh by omega)
      omega
  · unfold sampleSendOpkTarget2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_opk_tot, hc])
      have hS : S.N_send_opk ≤ S.N_send_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 := _root_.ReductionDsl.bits_mono (show S.N_id ≤ S.N_dh by omega)
      have bm2 := _root_.ReductionDsl.bits_mono (show S.N_send_opk ≤ S.N_dh by omega)
      omega
  · unfold sampleSendNoOpkTarget2C
    split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_no_opk_tot, hc])
      have hS : S.N_send_no_opk ≤ S.N_send_no_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have bm1 := _root_.ReductionDsl.bits_mono (show S.N_id ≤ S.N_dh by omega)
      have bm2 := _root_.ReductionDsl.bits_mono (show S.N_send_no_opk ≤ S.N_dh by omega)
      omega

private theorem fg2_chooseArm2C_costUB_le_arms {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (B1 B2 : Nat)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).costUB ≤ B1)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).costUB ≤ B2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).costUB ≤
      3 * _root_.ReductionDsl.bits (w1 + w2) + B1 + B2 + 30 := by
  unfold chooseArm2C
  split_ifs with hw1 hw2
  · exact le_trans hc2 (by omega)
  · exact le_trans hc1 (by omega)
  · dsimp only [bindV]
    simp only [Comp.costUB, v_costUB]
    have hb := fg2_bernoulliRatioGdhC_costUB_le (Δ := Δ) w1 w2
    simp only [hw1, hw2, or_self, ↓reduceIte] at hb
    have h1 := hc1 (Δ' := .bool :: Δ)
    have h2 := hc2 (Δ' := .bool :: Δ)
    omega

private theorem fg2_sampleSendTarget2C_costUB_le (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).costUB ≤ 7 * _root_.ReductionDsl.bits S.N_dh + 75 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  unfold sampleSendTarget2C
  split_ifs
  · simp [Comp.costUB, Expr.costUB]
  · have hc := fg2_chooseArm2C_costUB_le_arms (Γ₁ := Δ) (Δ := Δ)
      S.N_send_opk_tot S.N_send_no_opk_tot
      (fun {Δ'} [_] => sampleSendOpkTarget2C S (Δ := Δ'))
      (fun {Δ'} [_] => sampleSendNoOpkTarget2C S (Δ := Δ'))
      (2 * _root_.ReductionDsl.bits S.N_dh + 20) (2 * _root_.ReductionDsl.bits S.N_dh + 20)
      (fun {Δ'} [_] => (fg2_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (fg2_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.2)
    have bm := _root_.ReductionDsl.bits_mono
      (show S.N_send_opk_tot + S.N_send_no_opk_tot ≤ S.N_dh by omega)
    omega

private theorem fg2_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).init.cost ≤ 45 * _root_.ReductionDsl.bits S.N_dh + 620 := by
  refine le_trans (fgKeyIndGapDh2Prog S K).init.cost_le_costUB ?_
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh →
      _root_.ReductionDsl.bits x ≤ 2 * _root_.ReductionDsl.bits S.N_dh + 1 := fun x hx =>
    le_trans (_root_.ReductionDsl.bits_mono hx)
      (by have hm := _root_.ReductionDsl.bits_mul S.N_dh S.N_dh; omega)
  have hArmA : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤
      3 * _root_.ReductionDsl.bits S.N_dh + 60 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0]
    have h1 := (fg2_coordSamplers2_costUB_le S (Δ := Δ)).1
    have h2 := (fg2_coordSamplers2_costUB_le S (Δ := .opt .nat :: Δ)).2.1
    omega
  have hArmC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤
      9 * _root_.ReductionDsl.bits S.N_dh + 135 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have h1 := fg2_sampleSendTarget2C_costUB_le S (Δ := Δ)
    have h2 := (fg2_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).2.1
    omega
  have hArmB : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
          (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤
      8 * _root_.ReductionDsl.bits S.N_dh + 130 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_2]
    have h1 := fg2_sampleSendTarget2C_costUB_le S (Δ := Δ)
    have h2 := (fg2_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).1
    omega
  have hArmD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
        Comp.ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
          .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)) :
        Comp pqxdhOps pqGapDhIface Δ params2Ty).costUB ≤
      5 * _root_.ReductionDsl.bits S.N_dh + 75 := by
    intro Γ₁ Δ _ uv
    simp only [bindV_costUB, pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_3]
    have h1 := (fg2_coordSamplers2_costUB_le S (Δ := Δ)).2.2.2.1
    have h2 := (fg2_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ)).2.2.1
    omega
  have hSubAC : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_id * S.N_spk_tot) (S.N_send_tot * S.N_spk_tot)
        (fun {_} [_] => bindV (samplePrin2C S) fun pt => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            (v pt) (.bool true) .none (v st) (.bool false) .none (.nat 0)))
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (sampleSpkPair2C S) fun st =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) (v st) (.bool false) .none (.nat 1)))).costUB ≤
      18 * _root_.ReductionDsl.bits S.N_dh + 230 := by
    intro Γ₁ Δ _ uv
    have hc := fg2_chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ)
      (S.N_id * S.N_spk_tot) (S.N_send_tot * S.N_spk_tot) _ _
      (3 * _root_.ReductionDsl.bits S.N_dh + 60) (9 * _root_.ReductionDsl.bits S.N_dh + 135)
      (fun {Δ'} [_] => hArmA (Δ := Δ') uv) (fun {Δ'} [_] => hArmC (Δ := Δ') uv)
    have bsum := hsq (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith)
    omega
  have hSubBD : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) (S.N_send_tot * S.N_id) (S.N_send_opk_tot * S.N_opk_tot)
        (fun {_} [_] => bindV (sampleSendTarget2C S) fun et => bindV (samplePrin2C S) fun pt =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.snd (v uv))
            (v pt) (.bool false) (v et) .none (.bool false) .none (.nat 2)))
        (fun {_} [_] => bindV (sampleSendOpkTarget2C S) fun et => bindV (sampleOpkTriple2C S) fun ot =>
          .ret (pa2Mk (.fst (v uv)) (.snd (v uv)) (.fst (v uv))
            .none (.bool false) (v et) .none (.bool true) (v ot) (.nat 3)))).costUB ≤
      19 * _root_.ReductionDsl.bits S.N_dh + 240 := by
    intro Γ₁ Δ _ uv
    have hc := fg2_chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ)
      (S.N_send_tot * S.N_id) (S.N_send_opk_tot * S.N_opk_tot) _ _
      (8 * _root_.ReductionDsl.bits S.N_dh + 130) (5 * _root_.ReductionDsl.bits S.N_dh + 75)
      (fun {Δ'} [_] => hArmB (Δ := Δ') uv) (fun {Δ'} [_] => hArmD (Δ := Δ') uv)
    have bsum := hsq (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot)
      (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
    omega
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).costUB ≤ 43 * _root_.ReductionDsl.bits S.N_dh + 505 := by
    intro Γ₁ Δ _ uv
    unfold initParams2C
    split_ifs
    · simp only [pa2Mk, v_costUB, Comp.costUB, Expr.costUB, bits_0, bits_3]; omega
    · let wAC := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot
      let wBD := S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot
      have hc := fg2_chooseArm2C_costUB_le_arms (Γ₁ := Γ₁) (Δ := Δ) wAC wBD _ _
        (18 * _root_.ReductionDsl.bits S.N_dh + 230) (19 * _root_.ReductionDsl.bits S.N_dh + 240)
        (fun {Δ'} [_] => hSubAC (Δ := Δ') uv) (fun {Δ'} [_] => hSubBD (Δ := Δ') uv)
      have bsum : _root_.ReductionDsl.bits (wAC + wBD) ≤ 2 * _root_.ReductionDsl.bits S.N_dh + 1 :=
        hsq (wAC + wBD)
          (by dsimp only [wAC, wBD]; nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
      linarith
  simp only [fgKeyIndGapDh2Prog, initAdv4_2, emptySimE, smMk, emptyStE, stMk,
    letV_costUB, bindV_costUB, gPrim_costUB, sBool_costUB, v_costUB, Comp.costUB, Expr.costUB]
  have hp := hInitP (Γ₁ := [.prod (B 32) (B 32), .prod (B 32) (B 32)])
    (Δ := [.prod (B 32) (B 32), .prod (B 32) (B 32)]) .zero
  linarith

set_option maxRecDepth 100000 in
private theorem fg2_handle_cost_le_min (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 62000 := by
  refine le_trans (gdhHandle2 S K).cost_le_costUB ?_
  simp only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
    initiateGdh2B, finishAcceptGdhC_costUB, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    fg2_wrapBase2_costUB, fg2_wrapSim2_costUB,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget, pa2SpkTarget,
    pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
    stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
    smMk, smUpd, qKJO, rs, slice32_costUB,
    qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
    rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
    rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
    eLet2, reMk,
    letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
    eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eAny_costUB, eMap_costUB,
    gPrim_costUB, koskBundleOkPowsC_costUB, koskSenderOkPowsC_costUB,
    resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB,
    findHonestC_costUB, chooseInitRandC_costUB,
    computePosC_costUB, computeOptPosInitC_costUB, mkSecretPosC_costUB, fgPatchC_costUB,
    sBytes32_costUB, sRandom64_costUB, sDrKey96_costUB,
    qX25519_costUB, qX25519Base_costUB, qIsCanonical_costUB, qPow8_costUB,
    qSigPkGen_costUB, qSigSign_costUB, qSigVerify_costUB,
    qKemKeyGen_costUB, qKemEncaps_costUB, qKemDecaps_costUB,
    litB_costUB, takeKB_costUB, lenB_costUB, eqB_costUB,
    u32OfNat_costUB, eqU32_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_nil, List.length_replicate, F_X25519_length', PNat.val_ofNat,
    bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  linarith

private theorem fg2_finish_cost_le_min (S : Setup) (K : Nat) :
    (gdhFinish2 S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * (min K S.N_dh) +
        66 * (min K S.N_dh) * (min K S.N_sess_tot) +
        423 * (min K S.N_dh) + 263 * (min K S.N_sess_tot) + 2132 * K + 409 := by
  refine le_trans (gdhFinish2 S K).cost_le_costUB ?_
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC_costUB, findMapStep2C,
    initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
    smBase_costUB, smLog_costUB, smPows_costUB, pa2U, pa2V, pa2Mode,
    natEq,
    letV_costUB, bindV_costUB, caseOptV_costUB,
    findMV_costUB, foldMV_costUB,
    eCaseOpt_costUB, eMap_costUB,
    ddhQ_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_replicate, PNat.val_ofNat,
    bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
  have h : 69 * (min K S.N_dh) ^ 2 = 69 * (min K S.N_dh * min K S.N_dh) := by ring
  nlinarith

private def fg2_zGdhW : pqGapDhIface.Tag → ℕ := fun _ => 0
private def fg2_r64GdhWS : pqGapDhIface.smp.Samp → ℕ := r64W

@[local simp] private theorem fg2_queries_gPrim_r64 {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries fg2_zGdhW fg2_r64GdhWS = c.queries (fun _ => 0) r64W := by
  induction c with
  | ret _ | sample _ _ | query _ _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [gPrim, liftBase, Comp.queries, ih1, ih2]
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [gPrim, liftBase, Comp.queries, ih]

private theorem fg2_chooseArm2C_r64_zero {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT}
    (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (hc1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries fg2_zGdhW fg2_r64GdhWS = 0)
    (hc2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries fg2_zGdhW fg2_r64GdhWS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).queries fg2_zGdhW fg2_r64GdhWS = 0 := by
  unfold chooseArm2C bernoulliRatioGdhC
  split_ifs
  · exact hc2
  · exact hc1
  · simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]; exact ⟨hc1, hc2⟩
  · simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]; exact ⟨hc1, hc2⟩

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem fgKeyIndGapDh2Prog_r64_le (S : Setup) (q : ℕ) :
    (fgKeyIndGapDh2Prog S q).totalQueries (fun _ => 0) (sampR64W tlGapDhKeyInd.hsmp) q ≤ 4 * q := by
  have hWS : sampR64W tlGapDhKeyInd.hsmp = fg2_r64GdhWS := by funext s; cases s <;> rfl
  rw [hWS]
  change (fgKeyIndGapDh2Prog S q).totalQueries fg2_zGdhW fg2_r64GdhWS q ≤ 4 * q
  have hCoord : ∀ {Δ : List PT},
      (samplePrin2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 ∧
      (sampleSpkPair2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 ∧
      (sampleOpkTriple2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 ∧
      (sampleSendOpkTarget2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 ∧
      (sampleSendNoOpkTarget2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 := by
    intro Δ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold samplePrin2C; split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]
    · unfold sampleSpkPair2C; split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]
    · unfold sampleOpkTriple2C; split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]
    · unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]
    · unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, fg2_r64GdhWS, r64W, Comp.queries]
  have hST : ∀ {Δ : List PT}, (sampleSendTarget2C S (Δ := Δ)).queries fg2_zGdhW fg2_r64GdhWS = 0 := by
    intro Δ; unfold sampleSendTarget2C; split_ifs
    · rfl
    · exact fg2_chooseArm2C_r64_zero _ _ _ _ (fun {_} [_] => hCoord.2.2.2.1) (fun {_} [_] => hCoord.2.2.2.2)
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (uv : Var Γ₁ (.prod (B 32) (B 32))),
      (initParams2C S (Δ := Δ) uv).queries fg2_zGdhW fg2_r64GdhWS = 0 := by
    intro Γ₁ Δ _ uv; unfold initParams2C; split_ifs
    · rfl
    · refine fg2_chooseArm2C_r64_zero _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
      · refine fg2_chooseArm2C_r64_zero _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV, Comp.queries, hCoord.1, hCoord.2.1]
        · simp [bindV, Comp.queries, hST, hCoord.2.1]
      · refine fg2_chooseArm2C_r64_zero _ _ _ _ (fun {_} [_] => ?_) (fun {_} [_] => ?_)
        · simp [bindV, Comp.queries, hST, hCoord.1]
        · simp [bindV, Comp.queries, hCoord.2.2.2.1, hCoord.2.2.1]
  have hI : (fgKeyIndGapDh2Prog S q).init.queries fg2_zGdhW fg2_r64GdhWS = 0 := by
    simp only [fgKeyIndGapDh2Prog, initAdv4_2, letV, bindV, Comp.queries, hInitP]
    simp [gPrim, liftBase, sBool, fg2_r64GdhWS, r64W, Comp.queries]
  have hF : (gdhFinish2 S q).queries fg2_zGdhW fg2_r64GdhWS = 0 := by
    simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
      initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV,
      gPrim, liftBase, qPow8, qX25519, ddhQ, fg2_zGdhW, fg2_r64GdhWS, r64W, Comp.queries,
      Nat.add_zero, Nat.zero_add, Nat.max_zero, Nat.zero_max, Nat.mul_zero]
  have hH : (gdhHandle2 S q).queries fg2_zGdhW fg2_r64GdhWS ≤ 4 := by
    simp (config := { maxSteps := 10000000 }) only [
      gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
      initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
      testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
      wrapBase2, wrapSim2,
      mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
      ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
      findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
      lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
      chooseRespRandC, chooseInitRandC,
      letV, bindV, caseOptV, caseSumV, findMV, anyMV,
      gPrim, liftBase, sBytes32, sRandom64, sDrKey96,
      qX25519, qX25519Base, qIsCanonical, qPow8,
      qSigPkGen, qSigSign, qSigVerify,
      qKemKeyGen, qKemEncaps, qKemDecaps, ddhQ, fg2_zGdhW, fg2_r64GdhWS, r64W, Comp.queries,
      ite_true, ite_false, Bool.false_eq_true]
    try simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  unfold CostedReduction.totalQueries
  rw [hI]
  have hF' : (fgKeyIndGapDh2Prog S q).finish.queries fg2_zGdhW fg2_r64GdhWS = 0 := hF
  have hH' : (fgKeyIndGapDh2Prog S q).handle.queries fg2_zGdhW fg2_r64GdhWS ≤ 4 := hH
  rw [hF']
  have hMul := Nat.mul_le_mul_left q hH'
  omega

end FgKeyIndGapDh2Helpers

section SigAuth2R64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open Computational.Proofs.SignalPqxdh.AtomicLift

private def ah2_zEufW : pqxdhEufCmaIface.Tag → ℕ := fun _ => 0
private def ah2_r64EufWS : pqxdhEufCmaIface.smp.Samp → ℕ := r64W

@[local simp] private theorem ah2_queries_liftChal_euf_r64 {Γ : List (Ty pqSig)} {t : Ty pqSig}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (c.liftChal (C := eufCmaSignOracle)).queries ah2_zEufW ah2_r64EufWS =
      c.queries zAuthPrimW authR64WS := by
  induction c with
  | ret _ | sample _ _ | query _ _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [Comp.liftChal, Comp.queries, ih1, ih2]
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [Comp.liftChal, Comp.queries, ih]

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
private theorem sigReductionAuthProg2_r64_le (S : Setup) (q : ℕ) :
    (sigReductionAuthProg2 S q).totalQueries (fun _ => 0) (sampR64W tlAuthEufCma.hsmp) q ≤
      4 * q := by
  have hWS : sampR64W tlAuthEufCma.hsmp = ah2_r64EufWS := by funext s; cases s <;> rfl
  rw [hWS]
  change (sigReductionAuthProg2 S q).totalQueries ah2_zEufW ah2_r64EufWS q ≤ 4 * q
  have hI : (sigInit2Dsl S q).queries ah2_zEufW ah2_r64EufWS = 0 := by
    unfold sigInit2Dsl
    split_ifs <;> simp [bindV, Comp.sampleIndexC, Comp.sampleBoolC, ah2_r64EufWS, r64W, Comp.queries]
  have hF : (sigFinish2Dsl S).queries ah2_zEufW ah2_r64EufWS = 0 := by
    unfold sigFinish2Dsl
    split_ifs <;> simp [Comp.queries]
  have hH : (sigHandleDsl S q).queries ah2_zEufW ah2_r64EufWS ≤ 4 := by
    dsimp only [sigHandleDsl, sigStepC]
    simp (config := { maxSteps := 10000000 }) only [
      ah2_queries_liftChal_euf_r64,
      koskBundleOkC_r64, koskSenderOkC_r64, resolveSigPkC_r64,
      findHonestC_r64, hkdfOrRoC_true_r64, rootRoC_r64,
      extractC, wrapC,
      initPrinB, corruptB, genSpkB, genOpkB, registerB, sendC, sendB, recvTailC, recvB, roB, roRootB,
      honestPeerC,
      bindV, letV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      Comp.queries_letC, _root_.ReductionDsl.Comp.letC,
      _root_.ReductionDsl.Comp.caseOptC, _root_.ReductionDsl.Comp.caseSumC, _root_.ReductionDsl.Comp.iteC,
      Comp.liftChal,
      Comp.sampleBool, Comp.sampleBytes32, Comp.sampleRandom64, Comp.sampleDrKey96, Comp.sampleIndex,
      Comp.sampleBoolC, Comp.sampleBytes32C, Comp.sampleRandom64C, Comp.sampleDrKey96C, Comp.sampleIndexC,
      Comp.queryPrim, Comp.queryPrimC, Comp.queryChal,
      ah2_zEufW, zAuthPrimW,
      authR64WS_bool, authR64WS_bytes32, authR64WS_random64, authR64WS_drKey96, authR64WS_index,
      Comp.queries, ite_true, ite_false, Bool.false_eq_true]
    simp only [ah2_r64EufWS, r64W, Comp.queries,
      Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_max, Nat.max_zero, max_self]
    omega
  unfold CostedReduction.totalQueries sigReductionAuthProg2
  dsimp only
  rw [hI, hF]
  have hMul := Nat.mul_le_mul_left q hH
  omega

end SigAuth2R64

section PrfCkMkClampedCost

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf

private theorem apc_bits_0 : _root_.ReductionDsl.bits 0 = 1 := rfl
private theorem apc_bits_1 : _root_.ReductionDsl.bits 1 = 1 := rfl
private theorem apc_bits_32 : _root_.ReductionDsl.bits 32 = 6 := by decide

@[local simp] private theorem apc_lookupSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ AuthPrf.sessionIdTy) :
    (lookupSendSlotE ss sid).cost = ss.cost + sid.cost + 148 := by
  simp only [lookupSendSlotE, eLet2, eLet, eCaseSum, assSendOpk, assSendNoOpk, v, Expr.cost]
  omega

@[local simp] private theorem apc_allocSendSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (sid : Expr pqxdhOps Γ AuthPrf.sessionIdTy) :
    (allocSendSlotE ss sid).cost = ss.cost + sid.cost + 436 := by
  simp only [allocSendSlotE, eLet2, eLet, eCaseSum, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, apc_bits_0, apc_bits_1]
  omega

@[local simp] private theorem apc_allocRecvSlotE_cost {Γ : List PT}
    (ss : Expr pqxdhOps Γ authSlotStateTy) (rc : Expr pqxdhOps Γ .nat) :
    (allocRecvSlotE ss rc).cost = ss.cost + rc.cost + 231 := by
  simp only [allocRecvSlotE, eLet2, eLet, eCaseOpt, assMk, assNext, assSendOpk,
    assSendNoOpk, assRecv, v, Expr.cost, apc_bits_1]
  omega

private theorem apc_authCkSendB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkSendB S K opk idx chalP fhst x :
      Comp pqxdhOps pqPrimIface Δ (.prod AuthPrf.authRespTy authHybridStateFixedTy)).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkSendB, sampAtCkC, sampCkPairC, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      hkdfRoC_cost, rootRoC_cost, apc_allocSendSlotE_cost, sidEq_cost, firstMsgADE_cost,
      buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC, sendGuardE,
      cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny, eCaseOpt,
      natEq, natLt, isSomeE, ahsfHybrid, ahsfRecvCount, ahsfSlots, ahsfMkSlots,
      ahsBase, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      asRoCache, asRootRoCache, peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      AuthPrf.cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, apc_bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem apc_authCkRecvB_cost_tight_le (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkRecvB S K opk idx chalP fhst x :
      Comp pqxdhOps pqPrimIface Δ (.prod AuthPrf.authRespTy authHybridStateFixedTy)).cost ≤
      19000 + K * 14000 + min K S.N_dh * 16000 := by
  cases opk <;>
  · simp only [authCkRecvB, sampAtCkC, sampCkPairC, recvFinishTagRunC_cost,
      prepareAuthHybridRecvC_true_cost, prepareAuthHybridRecvC_false_cost,
      finishAuthRecvCkC_cost, apc_allocRecvSlotE_cost, hkdfRoC_cost, rootRoC_cost, firstMsgADE_cost,
      bindV, letV, caseOptV, eCaseOpt, natEq, natLt, isSomeE,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots,
      ahsfUpd, ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasDrKey, iasRk1, iasMkSeed, iasCk1_1,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, AuthPrf.cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, apc_bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem apc_authCkStepC_cost_tight_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ AuthPrf.authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (authCkStepC S K idx chalP fhst q :
      Comp pqxdhOps pqPrimIface Δ (.prod AuthPrf.authRespTy authHybridStateFixedTy)).cost ≤
      19500 + K * 15000 + min K S.N_dh * 16000 := by
  unfold authCkStepC
  refine le_trans
    (caseSumV_cost_le _ _ _ (initPrinFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (corruptFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genSpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (genOpkFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (apc_authCkSendB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (apc_authCkSendB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (apc_authCkRecvB_cost_tight_le S K true _ _ _ _) <|
     caseSumV_cost_le _ _ _ (apc_authCkRecvB_cost_tight_le S K false _ _ _ _) <|
     caseSumV_cost_le _ _ _ (roFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (roRootFixedB_cost_le K _ _) <|
     caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
     registerFixedB_cost_le _ _)
    (by omega)

private theorem apc_prfCkHandleDsl_cost_tight_le (S : Setup) (K : Nat) :
    (prfCkHandleDsl S K).cost ≤
      20000 + K * 15000 + min K S.N_dh * 16000 := by
  unfold prfCkHandleDsl
  have h := apc_authCkStepC_cost_tight_le S K
    (Δ := authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool ::
      prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy])
    (.zero : Var (.nat :: .bool :: prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy]) .nat)
    (.zero : Var (.prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy :: [prfCkStTy, AuthPrf.authQueryTy]) _)
    (.zero : Var (authHybridStateFixedTy :: .prod (B 32) (B 32) :: .nat :: .bool :: prfCkStTy ::
      [prfCkStTy, AuthPrf.authQueryTy]) _)
    (.succ .zero : Var [prfCkStTy, AuthPrf.authQueryTy] AuthPrf.authQueryTy)
  simp only [bindV, letV, ckSecb, ckIdx, ckChal, ckFhst, cost_letC, v, Comp.cost, Expr.cost]
  omega

private theorem apc_wrapMkBase_cost_le {Γ₁ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) [Ext Γ₁ Δ]
    (m : Comp pqxdhOps pqPrimIface Δ (.prod AuthPrf.authRespTy authHybridStateFixedTy))
    {M : Nat} (hm : m.cost ≤ M) :
    (wrapMkBase core m).cost ≤ M + 30 := by
  simp only [wrapMkBase, bindV, mkcMk, mkcSecb, mkcIdx, mkcSentChal, v, Comp.cost, Expr.cost]
  omega

private theorem apc_authMkSendPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkSendPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkSendPreB, koskBundleOkC_cost, finishAuthHybridSendC_cost,
      finishAuthSendMkC_cost, hkdfRoC_cost, rootRoC_cost, apc_allocSendSlotE_cost, sidEq_cost,
      firstMsgADE_cost, buildSecretsE_cost, resolveSigPkC, checkBundleSpkHonIdealC, findHonestC,
      sendGuardE, cost_encEC, cost_encKEM, bindV, letV, caseOptV, findMV, anyMV, eFind, eAny,
      eCaseOpt, natEq, natLt, isSomeE, mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asUsedSendSessions,
      peSecIKA0, peIkAPk, peIkSignPk, peCorrupted,
      sbSpkPk, sbPqspkPk, pkbIkB, pkbSpkB, pkbSpkSig, pkbOpkB?, pkbPqspkB, pkbPqspkSig,
      aNone, cost_letC, cost_samplePrim, cost_queryPrim, cost_bytesLen, cost_bytesBeq,
      AuthPrf.cost_boolOr, cost_litB, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, List.length_nil, apc_bits_32, ite_true, ite_false, Bool.false_eq_true]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem apc_authMkRecvPreB_cost_le_clamped (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (authMkRecvPreB S K opk core x : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      15000 + K * 10000 + min K S.N_dh * 20000 := by
  cases opk <;>
  · simp only [authMkRecvPreB, recvFinishTagRunC_cost,
      prepareAuthHybridRecvC_true_cost, prepareAuthHybridRecvC_false_cost,
      finishAuthRecvMkC_cost, finishRecvUnmatchedMkPreC_cost, hkdfRoC_cost, rootRoC_cost,
      apc_allocRecvSlotE_cost, apc_lookupSendSlotE_cost, sidEq_cost, sameSaltKeyE_cost,
      firstMsgADE_cost,
      bindV, letV, caseOptV, eFind, eCaseOpt, natEq, natLt, isSomeE,
      mkcSecb, mkcIdx, mkcSentChal, mkcFhst, mkcMk,
      ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, ahsfSlots, ahsfMkSlots, ahsfUpd,
      ahsfUpdSlots, ahsBase,
      peIkAPk, hdrIkAPk, pkmHdr, pkmEphAPk, pkmPqRatchetMsg, pkmAeadCt,
      iasSid, iasSpqrSalt?, iasDrKey, iasRk1, iasMkSeed, iasCk1_1, iasMsgKeys,
      parKEntry, parSecrets, parDhRatchet, parIsUncorrSender, parMatchedSess?, parSameEph,
      parHstDec, parFinishTag, aNone,
      cost_letC, cost_samplePrim, cost_queryPrim, AuthPrf.cost_boolOr,
      PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost,
      PNat.val_ofNat, apc_bits_0, apc_bits_1]
    repeat' first
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
      | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
    omega

private theorem apc_prfMkStepPreC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ AuthPrf.authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPreC S K core q : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy).cost ≤
      16000 + K * 11000 + min K S.N_dh * 22000 := by
  unfold prfMkStepPreC
  refine le_trans
    (letV_cost_le _ _
      (caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (initPrinFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (corruptFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (genSpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (genOpkFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (apc_authMkSendPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (apc_authMkSendPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (apc_authMkRecvPreB_cost_le_clamped S K true _ _) <|
       caseSumV_cost_le _ _ _ (apc_authMkRecvPreB_cost_le_clamped S K false _ _) <|
       caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (roFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (apc_wrapMkBase_cost_le _ _ (roRootFixedB_cost_le K _ _)) <|
       caseSumV_cost_le _ _ _ (by simp only [aNone, v, Comp.cost, Expr.cost]; exact le_rfl) <|
       apc_wrapMkBase_cost_le _ _ (registerFixedB_cost_le _ _)))
    ?_
  simp only [v, Expr.cost]
  omega

private theorem apc_prfMkStepPostC_cost_le_clamped (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (cont : Var Γ₁ prfMkChalContTy) (mk : Var Γ₂ AuthPrf.msgKeysTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPostC S K cont mk : Comp pqxdhOps pqPrimIface Δ (.prod AuthPrf.authRespTy prfMkCoreTy)).cost ≤
      3500 + K * 4000 + min K S.N_dh * 9000 := by
  simp only [prfMkStepPostC, finishAuthSendMkC_cost, finishAuthRecvMkC_cost,
    bindV, letV, caseSumV, eCaseOpt, mkcMk, ahsfUpdSlots, ahsfMkSlots,
    ahsfHybrid, ahsfRecvCount, ahsfMkSaltCache, cost_letC, cost_litB,
    v, Comp.cost, Expr.cost, PNat.val_ofNat, List.length_nil]
  repeat' first
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_right]
    | simp (discharger := clear *- ; omega) only [Nat.max_eq_left]
  omega

private theorem apc_prfMsgKeysHandleDsl_cost_le_clamped (S : Setup) (K : Nat) :
    (prfMsgKeysHandleDsl S K).cost ≤
      25000 + K * 20000 + min K S.N_dh * 35000 := by
  unfold prfMsgKeysHandleDsl
  have hPre := apc_prfMkStepPreC_cost_le_clamped S K
    (Δ := prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy])
    (.zero : Var (prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) prfMkCoreTy)
    (.succ .zero : Var [prfMkStTy, AuthPrf.authQueryTy] AuthPrf.authQueryTy)
  have hPost := apc_prfMkStepPostC_cost_le_clamped S K
    (Δ := AuthPrf.msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy])
    (.zero : Var (prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) prfMkChalContTy)
    (.zero : Var (AuthPrf.msgKeysTy :: prfMkChalContTy :: .opt (B 32) :: (.prod (.opt (B 32)) prfMkChalContTy) ::
      prfMkStepPreTy :: prfMkCoreTy :: .nat :: prfMkStTy :: [prfMkStTy, AuthPrf.authQueryTy]) AuthPrf.msgKeysTy)
  simp only [bindV, letV, caseSumV, natEq, aNone,
    cost_liftPrimComp, cost_letC, cost_queryDeriveMk,
    v, Comp.cost, Expr.cost, apc_bits_0, apc_bits_1]
  omega

private theorem apc_prfCkInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfCkInitDslK S K).cost = 71 + _root_.ReductionDsl.bits (min K S.N_sess_tot) := by
  simp only [prfCkInitDslK, bindV, emptyAuthHybridStFixedE, emptyAuthHybridStE, emptyAuthStE,
    ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk, cost_samplePrim, PSamp.cost,
    Ty.wd, v, Comp.cost, Expr.cost, apc_bits_0]
  omega

private theorem apc_prfMsgKeysInitDslK_cost_eq (S : Setup) (K : Nat) :
    (prfMsgKeysInitDslK S K).cost =
      72 + _root_.ReductionDsl.bits (min K S.N_sess_tot) +
        _root_.ReductionDsl.bits (min K S.N_recv_tot + 1) := by
  simp only [prfMsgKeysInitDslK, bindV, mkcMk, emptyAuthHybridStFixedE, emptyAuthHybridStE,
    emptyAuthStE, ahsfMk, ahsfMkSlots, emptyAuthSlotStE, assMk, ahsMk, stMk,
    cost_sampleChal, PSamp.cost, Ty.wd, v, Comp.cost, Expr.cost, apc_bits_0]
  omega

private theorem apc_prfCkRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfCkRedProg S K).totalCost q ≤
      71 + _root_.ReductionDsl.bits (min K S.N_sess_tot) +
      q * (20032 + K * 15000 + min K S.N_dh * 16000) +
      (114 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfCkRedProg, SignalPqxdh.LegacyCosted.authCodec,
    apc_prfCkInitDslK_cost_eq, prfCkFinishDsl_cost]
  have hH := apc_prfCkHandleDsl_cost_tight_le S K
  have hMax : max SignalPqxdh.LegacyCosted.pqPrimIface.uCost ((prfCkHandleDsl S K).cost + 32) =
      (prfCkHandleDsl S K).cost + 32 := by
    change max 1 ((prfCkHandleDsl S K).cost + 32) = (prfCkHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfCkHandleDsl S K).cost + 32) ≤
      q * (20032 + K * 15000 + min K S.N_dh * 16000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

private theorem apc_prfMsgKeysRedProg_totalCost_le_clamped (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg S K).totalCost q ≤
      72 + _root_.ReductionDsl.bits (min K S.N_sess_tot) +
      _root_.ReductionDsl.bits (min K S.N_recv_tot + 1) +
      q * (25032 + K * 20000 + min K S.N_dh * 35000) +
      (118 + min K S.N_dh * 413 + (min K S.N_dh) ^ 2 * 1088 + K * 97 + K ^ 2 * 9511) := by
  simp only [CostedReduction.totalCost, prfMsgKeysRedProg, SignalPqxdh.LegacyCosted.authCodec,
    apc_prfMsgKeysInitDslK_cost_eq, prfMsgKeysFinishDsl_cost]
  have hH := apc_prfMsgKeysHandleDsl_cost_le_clamped S K
  have hMax : max SignalPqxdh.LegacyCosted.pqPrfMkIface.uCost
      ((prfMsgKeysHandleDsl S K).cost + 32) = (prfMsgKeysHandleDsl S K).cost + 32 := by
    change max 1 ((prfMsgKeysHandleDsl S K).cost + 32) = (prfMsgKeysHandleDsl S K).cost + 32
    omega
  rw [hMax]
  have hMul : q * ((prfMsgKeysHandleDsl S K).cost + 32) ≤
      q * (25032 + K * 20000 + min K S.N_dh * 35000) :=
    Nat.mul_le_mul_left q (by omega)
  omega

end PrfCkMkClampedCost

section PrfHmacR64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

private def hm_zP : pqPrimIface.Tag → ℕ := fun _ => 0
private def hm_r64S : pqPrimIface.smp.Samp → ℕ := r64W
private def zHmacW : pqPrfHmacIface.Tag → ℕ := fun _ => 0
private def r64SHmac : pqPrfHmacIface.smp.Samp → ℕ := r64W

@[local simp] private theorem hm_r64S_bool : hm_r64S .bool = 0 := rfl
@[local simp] private theorem hm_r64S_bytes32 : hm_r64S .bytes32 = 0 := rfl
@[local simp] private theorem hm_r64S_random64 : hm_r64S .random64 = 1 := rfl
@[local simp] private theorem hm_r64S_drKey96 : hm_r64S .drKey96 = 0 := rfl
@[local simp] private theorem hm_r64S_msgKeys80 : hm_r64S .msgKeys80 = 0 := rfl
@[local simp] private theorem hm_r64S_index (n : ℕ) : hm_r64S (.index n) = 0 := rfl

@[local simp] private theorem r64SHmac_bool : r64SHmac .bool = 0 := rfl
@[local simp] private theorem r64SHmac_bytes32 : r64SHmac .bytes32 = 0 := rfl
@[local simp] private theorem r64SHmac_random64 : r64SHmac .random64 = 1 := rfl
@[local simp] private theorem r64SHmac_drKey96 : r64SHmac .drKey96 = 0 := rfl
@[local simp] private theorem r64SHmac_msgKeys80 : r64SHmac .msgKeys80 = 0 := rfl
@[local simp] private theorem r64SHmac_index (n : ℕ) : r64SHmac (.index n) = 0 := rfl

@[local simp] private theorem hm_queries_authPrf_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (AuthPrf.Comp.letC e k).queries w ws = k.queries w ws := by
  simp [AuthPrf.Comp.letC, Comp.queries]

@[local simp] private theorem queries_liftPrimComp_hmac_r64 {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := hmacPrfOracle) c).queries zHmacW r64SHmac =
      c.queries hm_zP hm_r64S := by
  induction c with
  | ret _ | sample _ _ | query _ _ => rfl
  | bind _ _ ih1 ih2 | ite _ _ _ ih1 ih2 | caseOpt _ _ _ ih1 ih2 | caseSum _ _ _ ih1 ih2 =>
    simp [liftPrimComp, Comp.queries, ih1, ih2]
  | iter _ _ _ ih | findM _ _ _ ih | anyM _ _ _ ih | mapM _ _ _ ih
  | consumeFirstM _ _ _ _ ih | foldM _ _ _ _ ih =>
    simp [liftPrimComp, Comp.queries, ih]

@[local simp] private theorem hm_findHonestC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries hm_zP hm_r64S = 0 := by
  simp [findHonestC, letV, findMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isAdvRegC_r64 (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isAdvRegC, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isGameSpkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_isGameOpkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries hm_zP hm_r64S = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_koskBundleOkC_r64 (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ AuthPrf.authStateTy) (bu : Var Γ₂ AuthPrf.preKeyBundleTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (koskBundleOkC S K st bu : Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [koskBundleOkC, bindV, caseOptV, Comp.queries]

@[local simp] private theorem hm_koskSenderOkC_r64 (S : Setup) (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries hm_zP hm_r64S = 0 := by
  simp [koskSenderOkC, letV, bindV, Comp.queries]

@[local simp] private theorem hm_hkdfRoC_r64 (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfRoC K st sec).queries hm_zP hm_r64S = 0 := by
  simp [hkdfRoC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_rootRoC_r64 (K : Nat) {Γ Δ : List PT}
    (st : Var Γ AuthPrf.authStateTy) [AuthPrf.Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32)) :
    (rootRoC K st rk dh).queries hm_zP hm_r64S = 0 := by
  simp [rootRoC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_checkBundleProvenanceExactC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ AuthPrf.authStateTy) (bu : Var Γ₂ AuthPrf.preKeyBundleTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (checkBundleProvenanceExactC S K st bu : Comp pqxdhOps pqPrimIface Δ _).queries hm_zP hm_r64S = 0 := by
  simp [checkBundleProvenanceExactC, bindV, caseOptV, letV, anyMV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_spkHonIdealFromPeerC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Δ : List PT} (st : Var Γ₁ AuthPrf.authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat AuthPrf.principalEntryTy))) (bu : Var Γ₃ AuthPrf.preKeyBundleTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] :
    (spkHonIdealFromPeerC S K st pp bu : Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [spkHonIdealFromPeerC, caseOptV, letV, anyMV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_matchIdealAuthHandshakeC_r64
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ AuthPrf.handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ]
    [AuthPrf.Ext Γ₄ Δ] [AuthPrf.Ext Γ₅ Δ] [AuthPrf.Ext Γ₆ Δ] :
    (matchIdealAuthHandshakeC ikB spkB opkB? pqspkB hdr s :
      Comp pqxdhOps pqPrimIface Δ .bool).queries hm_zP hm_r64S = 0 := by
  simp [matchIdealAuthHandshakeC, bindV, caseOptV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_initPrinFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (initPrinFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [initPrinFixedB, letV, bindV, samplePrim, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_corruptFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (corruptFixedB K fhst u : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [corruptFixedB, letV, caseOptV, Comp.queries]

private theorem hm_genSpkFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat))
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (genSpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S ≤ 3 := by
  simp [genSpkFixedB, letV, caseOptV, bindV, samplePrim, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_genOpkFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (genOpkFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [genOpkFixedB, letV, bindV, samplePrim, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_roFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192))
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (roFixedB K fhst sec : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [roFixedB, letV, bindV, Comp.queries]

@[local simp] private theorem hm_roRootFixedB_r64 (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod (B 32) (B 32)))
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (roRootFixedB K fhst x : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [roRootFixedB, letV, bindV, Comp.queries]

@[local simp] private theorem hm_registerFixedB_r64 {Γ₁ Γ₂ Δ : List PT}
    (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32))
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (registerFixedB fhst sk : Comp pqxdhOps pqPrimIface Δ RSF).queries hm_zP hm_r64S = 0 := by
  simp [registerFixedB, letV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmKeyIdC_r64 (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    (hmKeyIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmKeyIdC, letV, caseOptV, bindV, samplePrim, Comp.queries]

@[local simp] private theorem hm_encPostC_r64 (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) :
    (encPostC K a).queries hm_zP hm_r64S = 0 := by
  simp [encPostC, letV, Comp.queries]

@[local simp] private theorem hm_hmEncPreIdC_r64 (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmEncPreIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmEncPreIdC, letV, caseOptV, bindV, samplePrim, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmForgeIdC_r64 (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    (hmForgeIdC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmForgeIdC, letV, bindV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_finishIntC_r64 {Δ : List PT}
    (a : Expr pqxdhOps Δ intFinArgsTy) :
    (finishIntC a).queries hm_zP hm_r64S = 0 := by
  simp [finishIntC, letV, Comp.queries]

@[local simp] private theorem hm_intSendPrepC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (intSendPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy)).queries hm_zP hm_r64S = 0 := by
  simp only [intSendPrepC, letV, bindV, caseOptV, samplePrim, queryPrim,
    hm_findHonestC_r64, hm_koskBundleOkC_r64, hm_checkBundleProvenanceExactC_r64,
    hm_spkHonIdealFromPeerC_r64, hm_hkdfRoC_r64, hm_rootRoC_r64,
    hm_queries_authPrf_letC, hm_zP, hm_r64S_bytes32, hm_r64S_drKey96, Comp.queries]
  omega

@[local simp] private theorem hm_hmSendTailC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] [AuthPrf.Ext Γ₄ Δ] [AuthPrf.Ext Γ₅ Δ] :
    (hmSendTailC S K opk jt fhst mst x p : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries hm_zP hm_r64S = 0 := by
  simp [hmSendTailC, letV, bindV, caseSumV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSendC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] [AuthPrf.Ext Γ₄ Δ] :
    (hmSendC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries hm_zP hm_r64S = 0 := by
  simp [hmSendC, bindV, caseOptV, Comp.queries]

@[local simp] private theorem hm_hmRecvPrepC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] :
    (hmRecvPrepC S K opk fhst x : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy)).queries hm_zP hm_r64S = 0 := by
  cases opk <;>
    simp [hmRecvPrepC, letV, bindV, caseOptV, caseSumV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSchedPrepC_r64 (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) :
    (hmSchedPrepC S K a).queries hm_zP hm_r64S = 0 := by
  simp only [hmSchedPrepC, letV, bindV, caseOptV, findMV, samplePrim, queryPrim,
    hm_findHonestC_r64, hm_matchIdealAuthHandshakeC_r64, hm_hkdfRoC_r64, hm_rootRoC_r64,
    hm_queries_authPrf_letC, hm_zP, hm_r64S_bytes32, hm_r64S_drKey96, Comp.queries]
  omega

@[local simp] private theorem hm_forgeRetIdC_r64 (K : Nat) {Γ₁ Δ : List PT}
    (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [AuthPrf.Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) :
    (forgeRetIdC K fc idx cache').queries hm_zP hm_r64S = 0 := by
  simp [forgeRetIdC, letV, bindV, Comp.queries]

@[local simp] private theorem hm_hmSchedFinC_r64 (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedFinArgsTy) :
    (hmSchedFinC S K a).queries hm_zP hm_r64S = 0 := by
  simp [hmSchedFinC, letV, bindV, caseOptV, queryPrim, hm_zP, Comp.queries]

@[local simp] private theorem hm_hmSchedC_r64 (S : Setup) (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ schedArgsTy) :
    (hmSchedC S K a).queries hm_zP hm_r64S = 0 := by
  simp [hmSchedC, letV, bindV, caseOptV, Comp.queries]

@[local simp] private theorem hm_hmRecvTailC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] [AuthPrf.Ext Γ₄ Δ] [AuthPrf.Ext Γ₅ Δ] :
    (hmRecvTailC S K opk jt fhst mst x d : Comp pqxdhOps pqPrimIface Δ hmResTy).queries hm_zP hm_r64S = 0 := by
  simp [hmRecvTailC, letV, bindV, Comp.queries]

@[local simp] private theorem hm_hmRecvC_r64 (S : Setup) (K : Nat) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] [AuthPrf.Ext Γ₄ Δ] :
    (hmRecvC S K opk jt fhst mst x : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries hm_zP hm_r64S = 0 := by
  simp [hmRecvC, bindV, caseOptV, Comp.queries]

private theorem hm_hmDispatchC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (q : Var Γ₄ AuthPrf.authQueryTy)
    [AuthPrf.Ext Γ₁ Δ] [AuthPrf.Ext Γ₂ Δ] [AuthPrf.Ext Γ₃ Δ] [AuthPrf.Ext Γ₄ Δ] :
    (hmDispatchC S K jt fhst mst q : Comp pqxdhOps pqPrimIface Δ hmPreTy).queries hm_zP hm_r64S ≤ 3 := by
  unfold hmDispatchC
  simp only [hmOther, caseSumV, bindV,
    hm_initPrinFixedB_r64, hm_corruptFixedB_r64, hm_genOpkFixedB_r64,
    hm_hmSendC_r64, hm_hmRecvC_r64, hm_roFixedB_r64, hm_roRootFixedB_r64, hm_registerFixedB_r64,
    Comp.queries, Nat.add_zero, Nat.zero_max, Nat.max_zero]
  exact hm_genSpkFixedB_r64 K fhst .zero

private theorem hm_hmPreC_r64 (S : Setup) (K : Nat) :
    (hmPreC S K).queries hm_zP hm_r64S ≤ 3 := by
  unfold hmPreC
  simp only [letV, hm_queries_authPrf_letC]
  exact hm_hmDispatchC_r64 S K _ _ _ _

@[local simp] private theorem hm_hmPostC_r64 (K : Nat) {Δ : List PT}
    (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))) :
    (hmPostC K a).queries hm_zP hm_r64S = 0 := by
  simp [hmPostC, letV, bindV, Comp.queries]

private theorem hm_hmInitC_r64 (S : Setup) :
    (hmInitC S).queries zHmacW r64SHmac = 0 := by
  simp [hmInitC, bindV, sampleChal, Comp.queries]

private theorem hm_hmFinishC_r64 (K : Nat) :
    (hmFinishC K).queries zHmacW r64SHmac = 0 := by
  simp [hmFinishC, letV, bindV, AuthPrfHmac.mapMV, sampleChal, queryHmacEval, zHmacW, Comp.queries]

private theorem prfHmacRedProg_r64_le (S : Setup) (K q : ℕ) :
    (prfHmacRedProg S K).totalQueries (fun _ => 0) (sampR64W tlPrfHmac.hsmp) q ≤ 4 * q := by
  have hWS : sampR64W tlPrfHmac.hsmp = r64SHmac := by funext s; cases s <;> rfl
  rw [hWS]
  change (prfHmacRedProg S K).totalQueries zHmacW r64SHmac q ≤ 4 * q
  have hI := hm_hmInitC_r64 S
  have hF := hm_hmFinishC_r64 K
  have hH : (hmHandleC S K).queries zHmacW r64SHmac ≤ 4 := by
    unfold hmHandleC
    simp only [bindV, letV, caseSumV, hm_queries_authPrf_letC,
      queries_liftPrimComp_hmac_r64, hm_hmPostC_r64, queryHmacEval, zHmacW, Comp.queries]
    have hPre := hm_hmPreC_r64 S K
    omega
  unfold CostedReduction.totalQueries prfHmacRedProg
  dsimp only
  rw [hI, hF]
  have hMul := Nat.mul_le_mul_left q hH
  omega

end PrfHmacR64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed (pqPrimIface pqxdhEufCmaIface pqGapDhIface pqAuthPrimIface pqAuthEufCmaIface pqAuthGapDhIface pqPrfMkIface pqPrfHmacIface authCodec)
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.AuthSubHops1to3
open _root_.SignalPqxdh.Security.ReductionDsl
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd hiding bits_0 bits_1 bits_2 bits_3 bits_32
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open OracleSpec OracleComp

theorem eleven_mul_cost_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h11 : 11 * c ≤ 720896 + 1441792 * b.q_total +
      360448 * min b.q_total S.N_dh + 360448 * min b.q_total S.N_sess_tot +
      11264 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      720896 * (b.q_total * b.q_total) +
      360448 * (b.q_total * min b.q_total S.N_dh) +
      360448 * (b.q_total * min b.q_total S.N_sess_tot) +
      22528 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      2816 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b :=
  eleven_mul_clamped_le_stepCostBudget S b h11

theorem two_mul_cost_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h2 : 2 * c ≤ 131072 + 262144 * b.q_total +
      65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      131072 * (b.q_total * b.q_total) +
      65536 * (b.q_total * min b.q_total S.N_dh) +
      65536 * (b.q_total * min b.q_total S.N_sess_tot) +
      4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b :=
  two_mul_clamped_le_stepCostBudget S b h2

private theorem sc_log_dh_le_prod (S : Setup) (q : ℕ) :
    Nat.log 2 S.N_dh ≤ (q + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
  have h1 : 1 ≤ q + 1 := by omega
  have h2 : Nat.log 2 S.N_dh ≤ Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot := Nat.le_add_right _ _
  simpa using Nat.mul_le_mul h1 h2

private theorem sc_log_sum_le_prod (S : Setup) (q : ℕ) :
    Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot ≤
      (q + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) := by
  have h1 : 1 ≤ q + 1 := by omega
  simpa using Nat.mul_le_mul_right (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) h1

theorem sigKeyIndAtomicProg_totalCost_le_stepCostBudget (useRo : Bool) (S : Setup)
    (b : QueryBudget) :
    (sigKeyIndAtomicProg useRo S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine eleven_mul_clamped_le_stepCostBudget S b
    (le_trans (liftKeyInd1Stage_totalCost_eleven_mul_le tlEufCmaKeyInd rfl S
      (sigKeyIndDslProg useRo S b) b.q_total) ?_)
  dsimp only [sigKeyIndDslProg]
  have hh := sigKeyIndProg_handle_cost_le useRo S b.q_total
  have hi := sigKeyIndProg_init_cost useRo S b.q_total
  have hf := sigKeyIndProg_finish_cost_le useRo S b.q_total
  have hIdLeDh : S.N_id ≤ S.N_dh := by unfold Setup.N_dh; omega
  have hbId : _root_.ReductionDsl.bits S.N_id ≤ Nat.log 2 S.N_dh + 1 := by
    simp only [_root_.ReductionDsl.bits]
    exact Nat.add_le_add_right (Nat.log_mono_right hIdLeDh) 1
  have hbSpk : _root_.ReductionDsl.bits (min b.q_total S.N_spk_tot) ≤ b.q_total + 1 := by
    simp only [_root_.ReductionDsl.bits]
    have := Nat.log_le_self 2 (min b.q_total S.N_spk_tot)
    have := Nat.min_le_left b.q_total S.N_spk_tot
    omega
  have hC : (SignalPqxdh.LegacyCosted.keyIndCodec S).codecCost = 32 := rfl
  have hU : SignalPqxdh.LegacyCosted.pqxdhEufCmaIface.uCost = 1 := rfl
  rw [CostedReduction.totalCost, hC, hU, hi]
  generalize (sigKeyIndProg useRo S b.q_total).handle.cost = hc at hh ⊢
  generalize (sigKeyIndProg useRo S b.q_total).finish.cost = hfc at hf ⊢
  have hMax : max 1 (hc + 32) ≤
      14421 + 7980 * min b.q_total S.N_dh + 7362 * min b.q_total S.N_sess_tot +
        7046 * b.q_total := by omega
  have hMul := Nat.mul_le_mul_left b.q_total hMax
  have hExp : b.q_total * (14421 + 7980 * min b.q_total S.N_dh +
      7362 * min b.q_total S.N_sess_tot + 7046 * b.q_total) =
      14421 * b.q_total + 7046 * (b.q_total * b.q_total) +
        7980 * (b.q_total * min b.q_total S.N_dh) +
        7362 * (b.q_total * min b.q_total S.N_sess_tot) := by ring
  rw [hExp] at hMul
  rw [Nat.mul_assoc 11264 (b.q_total + 1)]
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left _ _)
  have hLog := sc_log_dh_le_prod S b.q_total
  generalize (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) = lg at hLog ⊢
  omega

theorem shcrKeyIndAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyIndAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine eleven_mul_clamped_le_stepCostBudget S b
    (le_trans (liftKeyInd2Stage_totalCost_eleven_mul_le tlPrimKeyInd rfl S
      (shcrKeyIndDslProg S b) b.q_total) ?_)
  dsimp only [shcrKeyIndDslProg]
  have h1 := shcrKeyIndProg_handlePre_cost_tight_le S b.q_total (keyIndLoopBound b)
  have h2 := shcrKeyIndProg_handlePost_cost_tight_le S b.q_total (keyIndLoopBound b)
  have h3 := shcrKeyIndProg_resume_cost S b.q_total (keyIndLoopBound b)
  have h4 := shcrKeyIndProg_finish_cost S b.q_total (keyIndLoopBound b)
  have h5 := shcrKeyIndProg_init_cost_le S b.q_total (keyIndLoopBound b)
  have h6 := shcrKeyIndProg_chDone_cost S b.q_total (keyIndLoopBound b)
  have hC : (SignalPqxdh.LegacyCosted.keyIndCodec S).codecCost = 32 := rfl
  have hU : SignalPqxdh.LegacyCosted.pqPrimIface.uCost = 1 := rfl
  rw [TwoStageCostedReduction.totalCost, hC, hU, h3, h4, h6]
  dsimp only [keyIndLoopBound] at h1 h2 h5 ⊢
  have hmd : min (2 * b.q_total + 1) S.N_dh ≤ 2 * min b.q_total S.N_dh + 1 := by omega
  have hms : min (2 * b.q_total + 1) S.N_sess_tot ≤ 2 * min b.q_total S.N_sess_tot + 1 := by omega
  generalize min (2 * b.q_total + 1) S.N_dh = mkd at h1 h2 hmd ⊢
  generalize min (2 * b.q_total + 1) S.N_sess_tot = mks at h1 h2 hms ⊢
  generalize (shcrKeyIndProg S b.q_total (2 * b.q_total + 1)).handlePre.cost = hc1 at h1 ⊢
  generalize (shcrKeyIndProg S b.q_total (2 * b.q_total + 1)).handlePost.cost = hc2 at h2 ⊢
  generalize (shcrKeyIndProg S b.q_total (2 * b.q_total + 1)).init.cost = hc5 at h5 ⊢
  have hMaxH : max 1 (max hc1 hc2 + 32) ≤
      43039 + 17608 * min b.q_total S.N_dh + 14724 * min b.q_total S.N_sess_tot +
        8126 * b.q_total := by omega
  have hMul := Nat.mul_le_mul_left b.q_total hMaxH
  have hExp : b.q_total * (43039 + 17608 * min b.q_total S.N_dh +
      14724 * min b.q_total S.N_sess_tot + 8126 * b.q_total) =
      43039 * b.q_total + 8126 * (b.q_total * b.q_total) +
        17608 * (b.q_total * min b.q_total S.N_dh) +
        14724 * (b.q_total * min b.q_total S.N_sess_tot) := by ring
  rw [hExp] at hMul
  rw [Nat.mul_assoc 11264 (b.q_total + 1)]
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left _ _)
  have hLog := sc_log_dh_le_prod S b.q_total
  generalize b.q_total * b.q_total = qq at hMul hQMd ⊢
  generalize b.q_total * min b.q_total S.N_dh = qmd at hMul hQMd ⊢
  generalize b.q_total * min b.q_total S.N_sess_tot = qms at hMul ⊢
  generalize b.q_total * max 1 (max hc1 hc2 + 32) = qmh at hMul ⊢
  generalize (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) = lg at hLog ⊢
  generalize min b.q_total S.N_dh = md at hmd ⊢
  generalize min b.q_total S.N_sess_tot = ms at hms ⊢
  omega

theorem fgKeyIndGapDhAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDhAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftKeyInd1Stage_totalCost_two_mul_le tlGapDhKeyInd rfl S
      (fgKeyIndGapDh2Prog S b.q_total) b.q_total) ?_)
  have hI := fg2_init_cost_le S b.q_total
  have hH := fg2_handle_cost_le_min S b.q_total
  have hF := fg2_finish_cost_le_min S b.q_total
  have hR64 := fgKeyIndGapDh2Prog_r64_le S b.q_total
  have hLog := sc_log_dh_le_prod S b.q_total
  have hbits : _root_.ReductionDsl.bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits] at hI
  have hC : (SignalPqxdh.LegacyCosted.keyIndCodec S).codecCost = 32 := rfl
  have hU : SignalPqxdh.LegacyCosted.pqGapDhIface.uCost = 1 := rfl
  rw [CostedReduction.totalCost, hC, hU]
  change 3 * ((fgKeyIndGapDh2Prog S b.q_total).init.cost +
      b.q_total * max 1 ((gdhHandle2 S b.q_total).cost + 32) +
      (gdhFinish2 S b.q_total).cost) +
    78 * (fgKeyIndGapDh2Prog S b.q_total).totalQueries (fun _ => 0)
      (sampR64W tlGapDhKeyInd.hsmp) b.q_total + 164 * b.q_total ≤ _
  have hSq : (min b.q_total S.N_dh) ^ 2 = min b.q_total S.N_dh * min b.q_total S.N_dh := by ring
  rw [hSq] at hF
  generalize (fgKeyIndGapDh2Prog S b.q_total).init.cost = cI at hI ⊢
  generalize (gdhHandle2 S b.q_total).cost = cH at hH ⊢
  generalize (gdhFinish2 S b.q_total).cost = cF at hF ⊢
  generalize (fgKeyIndGapDh2Prog S b.q_total).totalQueries (fun _ => 0)
    (sampR64W tlGapDhKeyInd.hsmp) b.q_total = r64 at hR64 ⊢
  have hMax : max 1 (cH + 32) ≤
      62032 + 28015 * b.q_total + 27165 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot := by omega
  have hMul := Nat.mul_le_mul_left b.q_total hMax
  have hExp : b.q_total * (62032 + 28015 * b.q_total + 27165 * min b.q_total S.N_dh +
      14742 * min b.q_total S.N_sess_tot) =
      62032 * b.q_total + 28015 * (b.q_total * b.q_total) +
        27165 * (b.q_total * min b.q_total S.N_dh) +
        14742 * (b.q_total * min b.q_total S.N_sess_tot) := by ring
  rw [hExp] at hMul
  rw [Nat.mul_assoc 2048 (b.q_total + 1)]
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left _ _)
  have hAssoc1 : 69 * b.q_total * min b.q_total S.N_dh =
      69 * (b.q_total * min b.q_total S.N_dh) := by ring
  have hAssoc2 : 66 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot =
      66 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  rw [hAssoc1, hAssoc2] at hF
  generalize b.q_total * b.q_total = qq at hMul hQMd ⊢
  generalize b.q_total * min b.q_total S.N_dh = qmd at hMul hQMd hF ⊢
  generalize b.q_total * min b.q_total S.N_sess_tot = qms at hMul ⊢
  generalize b.q_total * max 1 (cH + 32) = qmh at hMul ⊢
  generalize min b.q_total S.N_dh * min b.q_total S.N_dh = mdd at hF ⊢
  generalize min b.q_total S.N_dh * min b.q_total S.N_sess_tot = mds at hF ⊢
  generalize (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) = lg at hLog ⊢
  generalize min b.q_total S.N_dh = md at hF ⊢
  generalize min b.q_total S.N_sess_tot = ms at hF ⊢
  omega

theorem sigReductionAuthAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigReductionAuthAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hLift := liftAuth1Stage_totalCost_two_mul_le tlAuthEufCma rfl S
    (sigReductionAuthDslProg2 S b) b.q_total
  have hR64 : (sigReductionAuthDslProg2 S b).totalQueries (fun _ => 0)
      (sampR64W tlAuthEufCma.hsmp) b.q_total ≤ 4 * b.q_total :=
    sigReductionAuthProg2_r64_le S b.q_total
  have hCost := sigReductionAuthDslProg2_two_mul_totalCost_le_stepCostBudget S b
  change (liftAuth1Stage tlAuthEufCma S (sigReductionAuthDslProg2 S b)).totalCost b.q_total ≤ _
  omega

theorem shcrAuthAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrAuthAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth2Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (shcrAuthDslProg S b) b.q_total) ?_)
  have hR64 := shcrReductionAuthProg_r64_le S b.q_total
  have hPre := shcr_handlePre_cost_le_tight S b.q_total b.q_total
  have hPost := shcr_handlePost_cost_le_tight S b.q_total b.q_total
  have hRes := shcr_resume_cost_le S b.q_total b.q_total
  have hFin := shcr_finish_cost_le S b.q_total b.q_total
  have hIni := shcr_init_cost_le_tight S b.q_total b.q_total
  have hDef := shcr_chDone_cost_le S b.q_total b.q_total
  have hLog := sc_log_sum_le_prod S b.q_total
  dsimp only [shcrAuthDslProg] at hR64 ⊢
  have hRaw : (shcrReductionAuthProg S b.q_total b.q_total).totalCost b.q_total ≤
      10300 + 4 * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        136532 * b.q_total + 22000 * (b.q_total * b.q_total) +
        6000 * (b.q_total * min b.q_total S.N_dh) := by
    change (shcrReductionAuthProg S b.q_total b.q_total).init.cost +
        b.q_total * max 1 (max (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost
          (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost + 32) +
        max (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost
          (shcrReductionAuthProg S b.q_total b.q_total).resume.cost +
        (shcrReductionAuthProg S b.q_total b.q_total).finish.cost ≤ _
    generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePre.cost = hc1 at hPre ⊢
    generalize (shcrReductionAuthProg S b.q_total b.q_total).handlePost.cost = hc2 at hPost ⊢
    generalize (shcrReductionAuthProg S b.q_total b.q_total).resume.cost = hc3 at hRes ⊢
    generalize (shcrReductionAuthProg S b.q_total b.q_total).finish.cost = hc4 at hFin ⊢
    generalize (shcrReductionAuthProg S b.q_total b.q_total).init.cost = hc5 at hIni ⊢
    generalize (shcrReductionAuthProg S b.q_total b.q_total).chDone.cost = hc6 at hDef ⊢
    have hMax : max 1 (max hc1 hc2 + 32) ≤
        120032 + 22000 * b.q_total + 6000 * min b.q_total S.N_dh := by omega
    have hMul := Nat.mul_le_mul_left b.q_total hMax
    have hExp : b.q_total * (120032 + 22000 * b.q_total + 6000 * min b.q_total S.N_dh) =
        120032 * b.q_total + 22000 * (b.q_total * b.q_total) +
          6000 * (b.q_total * min b.q_total S.N_dh) := by ring
    rw [hExp] at hMul
    omega
  generalize (shcrReductionAuthProg S b.q_total b.q_total).totalCost b.q_total = tc at hRaw ⊢
  generalize (shcrReductionAuthProg S b.q_total b.q_total).totalQueries (fun _ => 0)
    (sampR64W tlAuthPrim.hsmp) b.q_total = rq at hR64 ⊢
  rw [Nat.mul_assoc 2048 (b.q_total + 1)]
  have hMdLe : min b.q_total S.N_dh ≤ b.q_total := Nat.min_le_left _ _
  generalize Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot = l0 at hLog hRaw ⊢
  generalize min b.q_total S.N_dh = md at hRaw hMdLe ⊢
  generalize b.q_total = q at hRaw hR64 hLog hMdLe ⊢
  rcases q with _ | _ | _ | m
  · simp at hRaw hR64 hMdLe ⊢; omega
  · simp at hRaw hR64 hMdLe ⊢; omega
  · have h2m : 2 * md = md + md := by ring
    simp [h2m] at hRaw hR64 hMdLe ⊢; omega
  · have hmm : m ≤ m * m := Nat.le_mul_self m
    have hq0 : m + 1 + 1 + 1 = m + 3 := rfl
    rw [hq0] at hRaw hR64 hLog hMdLe ⊢
    have hL : l0 ≤ (m + 3 + 1) * l0 := Nat.le_mul_of_pos_left l0 (by omega)
    have hR : (m + 3) * (m + 3) = 9 + 6 * m + m * m := by ring
    have hD : (m + 3) * md = 3 * md + m * md := by ring
    rw [hR, hD] at hRaw ⊢
    generalize (m + 3 + 1) * l0 = lg at hL hLog ⊢
    generalize m * m = mm at hRaw hmm ⊢
    generalize m * md = mmd at hRaw ⊢
    clear hPre hPost hRes hFin hIni hDef
    omega

theorem fgAuthGapDhAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine eleven_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_eleven_mul_le tlAuthGapDh rfl S
      (fgAuthGapDhDslProg S b) b.q_total) ?_)
  have hH := fg_handle_cost_le_clamped S b.q_total
  have hF := fg_finish_cost_le_clamped S b.q_total
  have hI := fg_init_cost_le_clamped S b.q_total
  have hLog := sc_log_dh_le_prod S b.q_total
  have hqq : b.q_total ≤ b.q_total * b.q_total := Nat.le_mul_self b.q_total
  dsimp only [fgAuthGapDhDslProg]
  change 23 * ((fgAuthGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((fgAuthGapDhProg S b.q_total).handle.cost + 32) +
      (fgAuthGapDhProg S b.q_total).finish.cost) ≤ _
  generalize (fgAuthGapDhProg S b.q_total).handle.cost = hc1 at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.cost = hc2 at hF ⊢
  generalize (fgAuthGapDhProg S b.q_total).init.cost = hc3 at hI ⊢
  have hMax : max 1 (hc1 + 32) ≤
      63032 + 25000 * b.q_total + 9000 * min b.q_total S.N_dh := by omega
  have hMul := Nat.mul_le_mul_left b.q_total hMax
  have hExp : b.q_total * (63032 + 25000 * b.q_total + 9000 * min b.q_total S.N_dh) =
      63032 * b.q_total + 25000 * (b.q_total * b.q_total) +
        9000 * (b.q_total * min b.q_total S.N_dh) := by ring
  rw [hExp] at hMul
  rw [Nat.mul_assoc 11264 (b.q_total + 1)]
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left _ _)
  generalize b.q_total * b.q_total = qq at hMul hqq hQMd hF ⊢
  generalize b.q_total * min b.q_total S.N_dh = qmd at hMul hQMd hF ⊢
  generalize b.q_total * max 1 (hc1 + 32) = qmh at hMul ⊢
  generalize min b.q_total S.N_dh * min b.q_total S.N_dh = mdd at hF ⊢
  generalize (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) = lg at hLog ⊢
  omega

theorem prfCkAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfCkAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (prfCkRedProg S b.q_total) b.q_total) ?_)
  have hR64 := prfCkRedProg_r64_le S b.q_total b.q_total
  have hp := apc_prfCkRedProg_totalCost_le_clamped S b.q_total b.q_total
  have hbSess : _root_.ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤ b.q_total + 1 := by
    simp only [_root_.ReductionDsl.bits]
    have := Nat.log_le_self 2 (min b.q_total S.N_sess_tot)
    have := Nat.min_le_left b.q_total S.N_sess_tot
    omega
  have h2 : (prfCkRedProg S b.q_total).totalCost b.q_total ≤
      186 + 20130 * b.q_total + 413 * min b.q_total S.N_dh +
        24511 * (b.q_total * b.q_total) +
        16000 * (b.q_total * min b.q_total S.N_dh) +
        1088 * (min b.q_total S.N_dh * min b.q_total S.N_dh) := by
    have h2' : (prfCkRedProg S b.q_total).totalCost b.q_total ≤
        71 + (b.q_total + 1) +
          b.q_total * (20032 + b.q_total * 15000 + min b.q_total S.N_dh * 16000) +
          (114 + min b.q_total S.N_dh * 413 + (min b.q_total S.N_dh) ^ 2 * 1088 +
            b.q_total * 97 + b.q_total ^ 2 * 9511) := by
      omega
    exact h2'.trans_eq (by ring)
  generalize (prfCkRedProg S b.q_total).totalCost b.q_total = tc at h2 ⊢
  generalize (prfCkRedProg S b.q_total).totalQueries (fun _ => 0)
    (sampR64W tlAuthPrim.hsmp) b.q_total = rq at hR64 ⊢
  omega

theorem prfMsgKeysAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfMsgKeysAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth1Stage_totalCost_two_mul_le tlPrfMk rfl S
      (prfMsgKeysRedProg S b.q_total) b.q_total) ?_)
  have hR64 := prfMsgKeysRedProg_r64_le S b.q_total b.q_total
  have hp := apc_prfMsgKeysRedProg_totalCost_le_clamped S b.q_total b.q_total
  have hbSess : _root_.ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤ b.q_total + 1 := by
    simp only [_root_.ReductionDsl.bits]
    have := Nat.log_le_self 2 (min b.q_total S.N_sess_tot)
    have := Nat.min_le_left b.q_total S.N_sess_tot
    omega
  have hbRecv : _root_.ReductionDsl.bits (min b.q_total S.N_recv_tot + 1) ≤ b.q_total + 2 := by
    simp only [_root_.ReductionDsl.bits]
    have := Nat.log_le_self 2 (min b.q_total S.N_recv_tot + 1)
    have := Nat.min_le_left b.q_total S.N_recv_tot
    omega
  have h2 : (prfMsgKeysRedProg S b.q_total).totalCost b.q_total ≤
      193 + 25131 * b.q_total + 413 * min b.q_total S.N_dh +
        29511 * (b.q_total * b.q_total) +
        35000 * (b.q_total * min b.q_total S.N_dh) +
        1088 * (min b.q_total S.N_dh * min b.q_total S.N_dh) := by
    have h2' : (prfMsgKeysRedProg S b.q_total).totalCost b.q_total ≤
        72 + (b.q_total + 1) + (b.q_total + 2) +
          b.q_total * (25032 + b.q_total * 20000 + min b.q_total S.N_dh * 35000) +
          (118 + min b.q_total S.N_dh * 413 + (min b.q_total S.N_dh) ^ 2 * 1088 +
            b.q_total * 97 + b.q_total ^ 2 * 9511) := by
      omega
    exact h2'.trans_eq (by ring)
  have hQMd : b.q_total * min b.q_total S.N_dh ≤ b.q_total * b.q_total :=
    Nat.mul_le_mul_left b.q_total (Nat.min_le_left _ _)
  generalize (prfMsgKeysRedProg S b.q_total).totalCost b.q_total = tc at h2 ⊢
  generalize (prfMsgKeysRedProg S b.q_total).totalQueries (fun _ => 0)
    (sampR64W tlPrfMk.hsmp) b.q_total = rq at hR64 ⊢
  generalize b.q_total * b.q_total = qq at h2 hQMd ⊢
  generalize b.q_total * min b.q_total S.N_dh = qmd at h2 hQMd ⊢
  generalize min b.q_total S.N_dh * min b.q_total S.N_dh = mdd at h2 ⊢
  generalize min b.q_total S.N_dh = md at h2 ⊢
  omega

theorem aeadCpaAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (aeadCpaAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine two_mul_clamped_le_stepCostBudget S b
    (le_trans (liftAuth2Stage_totalCost_two_mul_le tlAuthPrim rfl S
      (aeadCpaDslProg S b) b.q_total) ?_)
  have hR64 : (aeadCpaDslProg S b).totalQueries (fun _ => 0)
      (sampR64W tlAuthPrim.hsmp) b.q_total ≤ 4 * b.q_total :=
    aeadCpaRedProg_r64_le S b.q_total b.q_total
  have hp := aeadCpaRedProg_totalCost_poly_le_clamped S b.q_total b.q_total
  have hbSend : _root_.ReductionDsl.bits (min b.q_total S.N_send_tot) ≤ b.q_total + 1 := by
    simp only [_root_.ReductionDsl.bits]
    have := Nat.log_le_self 2 (min b.q_total S.N_send_tot)
    have := Nat.min_le_left b.q_total S.N_send_tot
    omega
  dsimp only [aeadCpaDslProg] at hR64 ⊢
  have h2 : (aeadCpaRedProg S b.q_total).totalCost b.q_total ≤
      1131 + 12130 * b.q_total + 413 * min b.q_total S.N_dh +
        14511 * (b.q_total * b.q_total) +
        1550 * (b.q_total * min b.q_total S.N_dh) +
        7500 * (b.q_total * min b.q_total S.N_sess_tot) +
        1088 * (min b.q_total S.N_dh * min b.q_total S.N_dh) := by
    have h2' : (aeadCpaRedProg S b.q_total).totalCost b.q_total ≤
        (81 + b.q_total) +
          b.q_total * (12032 + b.q_total * 5000 + min b.q_total S.N_dh * 1550 +
            min b.q_total S.N_sess_tot * 7500) +
          900 + (150 + min b.q_total S.N_dh * 413 + (min b.q_total S.N_dh) ^ 2 * 1088 +
            b.q_total * 97 + b.q_total ^ 2 * 9511) := by
      omega
    exact h2'.trans_eq (by ring)
  omega

theorem prfHmacAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (prfHmacAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  have hLift := liftAuth1Stage_totalCost_two_mul_le tlPrfHmac rfl S (prfHmacDslProg S b) b.q_total
  have hR64 : (prfHmacDslProg S b).totalQueries (fun _ => 0) (sampR64W tlPrfHmac.hsmp) b.q_total ≤
      4 * b.q_total := prfHmacRedProg_r64_le S b.q_total b.q_total
  have hCost : 2 * (prfHmacDslProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b :=
    prfHmacRedProg_totalCost_two_mul_security_le S b
  have hB : 65536 * (b.q_total + 1) * (b.q_total + 1) ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
    unfold _root_.SignalPqxdh.Security.stepCostBudget
    dsimp only
    have h216 : (2 : ℕ) ^ 16 = 65536 := rfl
    rw [h216]
    omega
  have hQ : 2000 * b.q_total ≤ 65536 * (b.q_total + 1) * (b.q_total + 1) := by
    have : 65536 * (b.q_total + 1) * (b.q_total + 1) =
        65536 + 131072 * b.q_total + 65536 * (b.q_total * b.q_total) := by ring
    omega
  change (liftAuth1Stage tlPrfHmac S (prfHmacDslProg S b)).totalCost b.q_total ≤ _
  omega

/-! ## Semantic evaluation lemmas -/

private theorem sigKeyIndAtomicProg_eval_eq (useRo : Bool) (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    (sigKeyIndAtomicProg useRo S b).eval adv pk = (sigKeyIndDslProg useRo S b).eval adv pk := by
  have h := liftKeyInd1Stage_eval tlEufCmaKeyInd S (sigKeyIndDslProg useRo S b)
    (sigKeyIndProg_init_unsupported useRo S b.q_total)
    (sigKeyIndProg_handle_unsupported useRo S b.q_total)
    (sigKeyIndProg_finish_unsupported useRo S b.q_total) adv pk
  have hId : embedVal (.prod (SignalPqxdh.LegacyCosted.B 1569) (SignalPqxdh.LegacyCosted.B 64)) = id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

private theorem fgKeyIndGapDhAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyIndGapDhAtomicProg S b).eval adv (U, V) =
      (fgKeyIndGapDh2Prog S b.q_total).eval adv (U, V) := by
  have h := liftKeyInd1Stage_eval tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)
    (fgKeyIndGapDh2Prog_init_unsupported S b.q_total)
    (gdhHandle2_unsupported S b.q_total)
    (gdhFinish2_unsupported S b.q_total) adv (U, V)
  have hId : embedVal (SignalPqxdh.LegacyCosted.B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem sigReductionAuthAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (pk : Bytes) :
    (sigReductionAuthAtomicProg S b).eval adv pk =
      (sigReductionAuthDslProg2 S b).eval adv pk := by
  have h := liftAuth1Stage_eval tlAuthEufCma S (fun _ => rfl) (sigReductionAuthDslProg2 S b) adv pk
  have hId : embedVal (.prod (SignalPqxdh.LegacyCosted.B 1569) (SignalPqxdh.LegacyCosted.B 64)) = id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

private theorem fgAuthGapDhAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (U V : Bytes) :
    (fgAuthGapDhAtomicProg S b).eval adv (U, V) =
      (fgAuthGapDhDslProg S b).eval adv (U, V) := by
  have h := liftAuth1Stage_eval tlAuthGapDh S (fun _ => rfl) (fgAuthGapDhDslProg S b) adv (U, V)
  have hId : embedVal (SignalPqxdh.LegacyCosted.B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfCkAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) (mkSeed ck1 : Bytes) :
    (prfCkAtomicProg S b).eval adv (mkSeed, ck1) =
      (prfCkRedProg S b.q_total).eval adv (mkSeed, ck1) := by
  have h := liftAuth1Stage_eval tlAuthPrim S (fun _ => rfl) (prfCkRedProg S b.q_total)
    adv (mkSeed, ck1)
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfMsgKeysAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfMsgKeysAtomicProg S b).eval adv () = (prfMsgKeysRedProg S b.q_total).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfMk S (fun _ => rfl) (prfMsgKeysRedProg S b.q_total) adv ()
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

private theorem prfHmacAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + authSpec S) Bool) :
    (prfHmacAtomicProg S b).eval adv () = (prfHmacDslProg S b).eval adv () := by
  have h := liftAuth1Stage_eval tlPrfHmac S (fun _ => rfl) (prfHmacDslProg S b) adv ()
  have hId : embedVal .bool = id := rfl
  rw [hId, id_map] at h
  exact h

/-! ## Reduction bundles and resource bounds -/

private theorem h_size_le_budget {sz C₀ C₁ : ℕ} (S : Setup) (b : QueryBudget)
    (h₀ : C₀ ≤ 2 ^ 22) (h₁ : C₁ ≤ 2 ^ 12)
    (hSz : sz ≤ C₀ + C₁ * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    sz ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have h₀' : C₀ ≤ _root_.ReductionDsl.reductionSizeBudget := Nat.le_trans h₀ (by decide)
  have h₁' : C₁ * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    Nat.mul_le_mul_right _ h₁
  omega

private theorem h_bits_mono {x y : ℕ} (h : x ≤ y) :
    _root_.ReductionDsl.bits x ≤ _root_.ReductionDsl.bits y := by
  unfold _root_.ReductionDsl.bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem h_bits_params_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    _root_.ReductionDsl.bits b.q_total ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_dh) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_sess_tot) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ∧
    _root_.ReductionDsl.bits (min b.q_total S.N_send_tot) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hq1 : b.q_total + 1 ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
    unfold _root_.SignalPqxdh.Security.stepCostBudget
    dsimp only
    have hpos : 0 < b.q_total + 1 := Nat.succ_pos b.q_total
    have hmul : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
      Nat.le_mul_of_pos_right _ hpos
    omega
  have hq : b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by omega
  exact ⟨h_bits_mono hq,
    h_bits_mono ((Nat.min_le_left _ _).trans hq),
    h_bits_mono ((Nat.min_le_left _ _).trans hq),
    h_bits_mono ((Nat.min_le_left _ _).trans hq)⟩

private theorem h_bits_le_of_le_four_mul_sq {x N : ℕ} (h : x ≤ 4 * (N * N)) :
    _root_.ReductionDsl.bits x ≤ 2 * _root_.ReductionDsl.bits N + 3 := by
  have h1 := h_bits_mono h
  have h2 := _root_.ReductionDsl.bits_mul 4 (N * N)
  have h3 := _root_.ReductionDsl.bits_mul N N
  have h4 : _root_.ReductionDsl.bits 4 = 3 := by decide
  omega

theorem sigKeyIndAtomicProg_size_le_budget (useRo : Bool) (S : Setup) (b : QueryBudget) :
    (sigKeyIndAtomicProg useRo S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftKeyInd1Stage_size_le tlEufCmaKeyInd tlEufCmaKeyInd_sizeLe S
    (sigKeyIndDslProg useRo S b)
  have hLit : red1LitSize (sigKeyIndDslProg useRo S b) ≤ 20000 :=
    ki_sigKeyIndProg_litSize_le useRo S b.q_total
  have hP := ki_sigKeyIndProg_size_le_clamped useRo S b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 155000) (C₁ := 1020) S b (by decide) (by decide) ?_
  change (liftKeyInd1Stage tlEufCmaKeyInd S (sigKeyIndDslProg useRo S b)).size ≤ _
  dsimp only [sigKeyIndDslProg] at hL hLit ⊢
  omega

theorem shcrKeyIndAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (shcrKeyIndAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftKeyInd2Stage_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe S (shcrKeyIndDslProg S b)
  have hLit : red2LitSize (shcrKeyIndDslProg S b) ≤ 20000 :=
    ki_shcrKeyIndProg_litSize_le S b.q_total (keyIndLoopBound b)
  have hP := ki_shcrKeyIndProg_size_le_clamped S b.q_total (keyIndLoopBound b)
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  have hk : _root_.ReductionDsl.bits (keyIndLoopBound b) ≤
      _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    h_bits_mono (keyIndLoopBound_le_security_stepCostBudget S b)
  refine h_size_le_budget (C₀ := 295000) (C₁ := 2020) S b (by decide) (by decide) ?_
  change (liftKeyInd2Stage tlPrimKeyInd S (shcrKeyIndDslProg S b)).size ≤ _
  dsimp only [shcrKeyIndDslProg] at hL hLit ⊢
  omega

theorem fgKeyIndGapDhAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDhAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftKeyInd1Stage_size_le tlGapDhKeyInd tlGapDhKeyInd_sizeLe S
    (fgKeyIndGapDh2Prog S b.q_total)
  have hLit : red1LitSize (fgKeyIndGapDh2Prog S b.q_total) ≤ 20000 :=
    ki_fgKeyIndGapDh2Prog_litSize_le S b.q_total
  have hP := fgKeyIndGapDh2Prog_size_le_stepCostBudget S b
  exact h_size_le_budget (C₀ := 310000) (C₁ := 2900) S b (by decide) (by decide)
    (by change (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).size ≤ _; omega)

theorem sigReductionAuthAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (sigReductionAuthAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthEufCma tlAuthEufCma_sizeLe S (sigReductionAuthDslProg2 S b)
  have hLit : red1LitSize (sigReductionAuthDslProg2 S b) ≤ 20000 :=
    ah_sigReductionAuthProg2_litSize_le S b.q_total
  have hP := sigReductionAuthDslProg2_size_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 150000) (C₁ := 900) S b (by decide) (by decide) ?_
  change (liftAuth1Stage tlAuthEufCma S (sigReductionAuthDslProg2 S b)).size ≤ _
  dsimp only [sigReductionAuthDslProg2] at hL hLit hP ⊢
  omega

theorem shcrAuthAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (shcrAuthAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth2Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S (shcrAuthDslProg S b)
  have hLit : red2LitSize (shcrAuthDslProg S b) ≤ 20000 :=
    ah_shcrReductionAuthProg_litSize_le S b.q_total b.q_total
  have hP := ah_shcrReductionAuthProg_size_le_clamped S b.q_total b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 245000) (C₁ := 1800) S b (by decide) (by decide) ?_
  change (liftAuth2Stage tlAuthPrim S (shcrAuthDslProg S b)).size ≤ _
  dsimp only [shcrAuthDslProg] at hL hLit ⊢
  omega

theorem fgAuthGapDhAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthGapDh tlAuthGapDh_sizeLe S (fgAuthGapDhDslProg S b)
  have hLit : red1LitSize (fgAuthGapDhDslProg S b) ≤ 20000 :=
    ah_fgAuthGapDhProg_litSize_le S b.q_total
  have hP := fgAuthGapDhDslProg_size_le_clamped S b
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 230000) (C₁ := 1900) S b (by decide) (by decide) ?_
  change (liftAuth1Stage tlAuthGapDh S (fgAuthGapDhDslProg S b)).size ≤ _
  dsimp only [fgAuthGapDhDslProg] at hL hLit hP ⊢
  omega

theorem prfCkAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfCkAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S (prfCkRedProg S b.q_total)
  have hLit : red1LitSize (prfCkRedProg S b.q_total) ≤ 20000 :=
    ap_prfCkRedProg_litSize_le S b.q_total
  have hP := ap_prfCkRedProg_size_le_clamped S b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  exact h_size_le_budget (C₀ := 580000) (C₁ := 2600) S b (by decide) (by decide)
    (by change (liftAuth1Stage tlAuthPrim S (prfCkRedProg S b.q_total)).size ≤ _; omega)

theorem prfMsgKeysAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfMsgKeysAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlPrfMk tlPrfMk_sizeLe S (prfMsgKeysRedProg S b.q_total)
  have hLit : red1LitSize (prfMsgKeysRedProg S b.q_total) ≤ 20000 :=
    ap_prfMsgKeysRedProg_litSize_le S b.q_total
  have hP := ap_prfMsgKeysRedProg_size_le_clamped S b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  exact h_size_le_budget (C₀ := 1010000) (C₁ := 3600) S b (by decide) (by decide)
    (by change (liftAuth1Stage tlPrfMk S (prfMsgKeysRedProg S b.q_total)).size ≤ _; omega)

theorem aeadCpaAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (aeadCpaAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth2Stage_size_le tlAuthPrim tlAuthPrim_sizeLe S (aeadCpaDslProg S b)
  have hLit : red2LitSize (aeadCpaDslProg S b) ≤ 20000 :=
    ap_aeadCpaRedProg_litSize_le S b.q_total
  have hP := ap_aeadCpaRedProg_size_le_clamped S b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 580000) (C₁ := 4050) S b (by decide) (by decide) ?_
  change (liftAuth2Stage tlAuthPrim S (aeadCpaDslProg S b)).size ≤ _
  dsimp only [aeadCpaDslProg] at hL hLit ⊢
  omega

theorem prfHmacAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (prfHmacAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hL := liftAuth1Stage_size_le tlPrfHmac tlPrfHmac_sizeLe S (prfHmacDslProg S b)
  have hLit : red1LitSize (prfHmacDslProg S b) ≤ 20000 :=
    hm_prfHmacRedProg_litSize_le S b.q_total
  have hP := hm_prfHmacRedProg_size_le_clamped S b.q_total
  obtain ⟨hq, _, _, _⟩ := h_bits_params_le_stepCostBudget S b
  refine h_size_le_budget (C₀ := 380000) (C₁ := 1300) S b (by decide) (by decide) ?_
  change (liftAuth1Stage tlPrfHmac S (prfHmacDslProg S b)).size ≤ _
  dsimp only [prfHmacDslProg] at hL hLit ⊢
  omega

theorem gredBlockBounded_of_cost {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn out : Ty pqAtomicSig}
    (hqCost : ∀ g, 1 ≤ I.qCost g) (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : CostedReduction pqAtomicOps I G C rIn .unit .bool out)
    (hsmp : I.smp = pqAtomicSamplers)
    (hCost : R.totalCost b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    GRedBlockBounded S b ℓ R :=
  gredBlockBounded_atomic_of_totalCost_le (hsmp ▸ pqAtomicSamplers_sizeHonest) hqCost
    (hsmp ▸ one_le_pqAtomicSamplers_sCost) S b ℓ R hCost hSize

theorem gred2BlockBounded_of_cost {ι κ : Type} {T : OracleSpec ι}
    {I : Iface pqAtomicSig T} {G : OracleSpec κ} {C : GameCodec pqAtomicSig G}
    {rIn ch rIn2 out : Ty pqAtomicSig}
    (hqCost : ∀ g, 1 ≤ I.qCost g) (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (R : TwoStageCostedReduction pqAtomicOps I G C rIn .unit .bool ch rIn2 out)
    (hsmp : I.smp = pqAtomicSamplers)
    (hCost : R.totalCost b.q_total ≤ _root_.SignalPqxdh.Security.stepCostBudget S b)
    (hSize : R.size ≤ _root_.ReductionDsl.reductionSizeBudget +
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b)) :
    GRed2BlockBounded S b ℓ R :=
  gred2BlockBounded_atomic_of_totalCost_le (hsmp ▸ pqAtomicSamplers_sizeHonest) hqCost
    (hsmp ▸ one_le_pqAtomicSamplers_sCost) S b ℓ R hCost hSize

/-- Two-key `KeyInd` costed reduction family over `pqAtomicOps`. -/
def pqxdhKeyIndCostedSims (S : Setup) : KeyInd2KeyCostedReductionFamily S where
  sig  b := sigKeyIndAtomicProg true S b
  shcr b := shcrKeyIndAtomicProg S b
  gdh  b := fgKeyIndGapDhAtomicProg S b

abbrev keyIndCostedSims (S : Setup) : KeyInd2KeyCostedReductionFamily S := pqxdhKeyIndCostedSims S

/-- Syntactic step-cost, query, and block-size bounds for `pqxdhKeyIndCostedSims S`. -/
theorem pqxdhKeyIndCostedSims_costedBounds (S : Setup) :
    KeyInd2KeyCostedReductionBounds S (pqxdhKeyIndCostedSims S) where
  ops_sizeHonest  := pqOpsSizeHonest
  samp_sizeHonest := pqSampSizeHonest
  sig_cost        := fun b => sigKeyIndAtomicProg_totalCost_le_stepCostBudget true S b
  shcr_cost       := fun b => shcrKeyIndAtomicProg_totalCost_le_stepCostBudget S b
  gdh_cost        := fun b => fgKeyIndGapDhAtomicProg_totalCost_le_stepCostBudget S b
  sig_q_prim      := fun b => by
    dsimp only [pqxdhKeyIndCostedSims, sigKeyIndAtomicProg]
    refine le_trans (liftKeyInd1Stage_totalQueries_le tlEufCmaKeyInd S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      chalIfacePrimQueryWeight tlEufCmaKeyInd_primW (sigKeyIndDslProg true S b) b.q_total) ?_
    dsimp only [sigKeyIndDslProg]
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.eufCmaSignOracle).Tag → ℕ) =
        KeyInd.sigPrimW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = KeyInd.sigWS from rfl]
    have h := sigKeyIndProg_totalPrimQueries_le true S b b.q_total
    unfold primQueryBudget
    nlinarith
  shcr_q_prim     := fun b => by
    dsimp only [pqxdhKeyIndCostedSims, shcrKeyIndAtomicProg]
    refine le_trans (liftKeyInd2Stage_totalQueries_le tlPrimKeyInd S
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      primIfacePrimQueryWeight tlPrimKeyInd_primW (shcrKeyIndDslProg S b) b.q_total) ?_
    rw [show SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight = KeyInd.primW from rfl,
      show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = KeyInd.primWS from rfl]
    exact shcrKeyIndDslProg_totalPrimQueries_le S b
  gdh_q_ddh       := fun b => by
    dsimp only [pqxdhKeyIndCostedSims, fgKeyIndGapDhAtomicProg]
    refine le_trans (liftKeyInd1Stage_totalQueries_le tlGapDhKeyInd S
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      chalIfaceChalQueryWeight tlGapDhKeyInd_chalW (fgKeyIndGapDh2Prog S b.q_total) b.q_total) ?_
    rw [show (SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.gapDhDdhOracle).Tag → ℕ) =
        KeyIndGapDh.wDdhGdh by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = KeyIndGapDh.wsZero from rfl]
    exact fgKeyIndGapDh2Prog_totalChalQueries_le S b
  gdh_q_prim      := fun b => by
    dsimp only [pqxdhKeyIndCostedSims, fgKeyIndGapDhAtomicProg]
    refine le_trans (liftKeyInd1Stage_totalQueries_le tlGapDhKeyInd S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      chalIfacePrimQueryWeight tlGapDhKeyInd_primW (fgKeyIndGapDh2Prog S b.q_total) b.q_total) ?_
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.gapDhDdhOracle).Tag → ℕ) =
        KeyIndGapDh.wPrimGdh by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = KeyIndGapDh.wsZero from rfl]
    exact fgKeyIndGapDh2Prog_totalPrimQueries_le S b
  sig_blocks      := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqChalIface_qCost one_le_eufCmaSignOracle_qCost)
      S b ℓ (sigKeyIndAtomicProg true S b) rfl
      (sigKeyIndAtomicProg_totalCost_le_stepCostBudget true S b)
      (sigKeyIndAtomicProg_size_le_budget true S b)
  shcr_blocks     := fun b ℓ =>
    gred2BlockBounded_of_cost one_le_pqPrimIface_qCost
      S b ℓ (shcrKeyIndAtomicProg S b) rfl
      (shcrKeyIndAtomicProg_totalCost_le_stepCostBudget S b)
      (shcrKeyIndAtomicProg_size_le_budget S b)
  gdh_blocks      := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqChalIface_qCost one_le_gapDhDdhOracle_qCost)
      S b ℓ (fgKeyIndGapDhAtomicProg S b) rfl
      (fgKeyIndGapDhAtomicProg_totalCost_le_stepCostBudget S b)
      (fgKeyIndGapDhAtomicProg_size_le_budget S b)

/-- Semantic query bounds for `(pqxdhKeyIndCostedSims S).eval`. -/
theorem pqxdhKeyIndCostedSims_simBounds (S : Setup) :
    KeyInd2KeyReductionQueryBounds S (pqxdhKeyIndCostedSims S).eval where
  sig_bounded  := fun b A => by
    have hRun : ((pqxdhKeyIndCostedSims S).eval.sig b A).run =
        (sigKeyIndDslAdv true S b A).run := by
      funext pk
      exact sigKeyIndAtomicProg_eval_eq true S b (fun _ => A.1.run) pk
    refine ⟨?_, fun pk => ?_⟩
    · rw [hRun]
      exact (sigKeyIndDslAdv_bounded true S b A).1
    · rw [hRun]
      exact ((sigKeyIndDslAdv_bounded true S b A).2 pk).mono
        (sigKeyIndDslAdv_q_prim_le true S b A)
  shcr_bounded := fun b A => by
    refine kemShCrAdv_bounded_of_state_retract (A := shcrKeyIndDslAdv S b A) rfl
      (embedMid (π := (shcrKeyIndDslProg S b).π) (σ := (shcrKeyIndDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (projMid (π := (shcrKeyIndDslProg S b).π) (σ := (shcrKeyIndDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (fun pk sk => ?_) (fun st' ss ct => ?_) (shcrKeyIndDslAdv_bounded S b A)
    · exact liftKeyInd2Stage_eval1 tlPrimKeyInd S (shcrKeyIndDslProg S b)
        (shcrKeyIndProg_init_unsupported S b.q_total (keyIndLoopBound b))
        (shcrKeyIndProg_handlePre_unsupported S b.q_total (keyIndLoopBound b))
        (shcrKeyIndProg_chDone_unsupported S b.q_total (keyIndLoopBound b))
        (fun _ => A.1.run) (pk, sk) b.q_total false
    · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
      have hRet := embedMid_projMid
        (π := (shcrKeyIndDslProg S b).π) (σ := (shcrKeyIndDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568) st'
      have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S (shcrKeyIndDslProg S b)
        (shcrKeyIndProg_resume_unsupported S b.q_total (keyIndLoopBound b))
        (shcrKeyIndProg_handlePost_unsupported S b.q_total (keyIndLoopBound b))
        (shcrKeyIndProg_finish_unsupported S b.q_total (keyIndLoopBound b))
        (projMid (π := (shcrKeyIndDslProg S b).π) (σ := (shcrKeyIndDslProg S b).σ)
          (ch := SignalPqxdh.LegacyCosted.B 1568) st') (ss, ct) b.q_total false
      rw [hRet, hId, id_map] at h
      exact h
  gdh_bounded  := fun b A => by
    have hRun : ∀ U V, ((pqxdhKeyIndCostedSims S).eval.gdh b A).run U V =
        (fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V) :=
      fun U V => fgKeyIndGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V
    have hAg : ∀ u : Unit,
        (A.1.run).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
      intro _
      convert A.2.2.2.2.1 using 1
      funext q; cases q <;> simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
    refine ⟨fun U V => ?_, fun U V => ?_⟩
    · rw [hRun U V]
      exact fgKeyIndGapDh2Prog_chalBounded_gdhQueryBudget S b A U V
    · rw [hRun U V]
      exact (fgKeyIndGapDh2Prog_primBounded S b.q_total b.q_total
        (fun _ => A.1.run) hAg U V).mono (fgKeyIndGapDh2Prog_totalPrimQueries_le S b)

/-- Two-key `Auth` costed reduction family over `pqAtomicOps`. -/
def pqxdhAuthCostedSims (S : Setup) : AuthCostedReductionFamily S :=
  AuthCostedReductionFamily.mk'
    (fun b => sigReductionAuthAtomicProg S b)
    (fun b => shcrAuthAtomicProg S b)
    (fun b => fgAuthGapDhAtomicProg S b)
    (fun b => prfCkAtomicProg S b)
    (fun b => prfMsgKeysAtomicProg S b)
    (fun b => aeadCpaAtomicProg S b)
    (fun b => prfHmacAtomicProg S b)

abbrev authCostedSims (S : Setup) : AuthCostedReductionFamily S := pqxdhAuthCostedSims S

/-- Syntactic step-cost, query, and block-size bounds for `pqxdhAuthCostedSims S`. -/
theorem pqxdhAuthCostedSims_costedBounds (S : Setup) :
    AuthCostedReductionBounds S (pqxdhAuthCostedSims S) where
  ops_sizeHonest  := pqOpsSizeHonest
  samp_sizeHonest := pqSampSizeHonest
  sig_cost        := fun b => sigReductionAuthAtomicProg_totalCost_le_stepCostBudget S b
  shcr_cost       := fun b => shcrAuthAtomicProg_totalCost_le_stepCostBudget S b
  gdh_cost        := fun b => fgAuthGapDhAtomicProg_totalCost_le_stepCostBudget S b
  ck_cost         := fun b => prfCkAtomicProg_totalCost_le_stepCostBudget S b
  mk_cost         := fun b => prfMsgKeysAtomicProg_totalCost_le_stepCostBudget S b
  cpa_cost        := fun b => aeadCpaAtomicProg_totalCost_le_stepCostBudget S b
  int_cost        := fun b => prfHmacAtomicProg_totalCost_le_stepCostBudget S b
  sig_q_prim      := fun b => by
    dsimp only [pqxdhAuthCostedSims, sigReductionAuthAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlAuthEufCma S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authChalIfacePrimQueryWeight tlAuthEufCma_primW (sigReductionAuthDslProg2 S b) b.q_total) ?_
    dsimp only [sigReductionAuthDslProg2]
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.eufCmaSignOracle).Tag → ℕ) =
        AuthHs.sigPrimW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthHs.sigWS from rfl]
    exact sigReductionAuthProg2_primQueries_le_budget S b b.q_total
  shcr_q_prim     := fun b => by
    dsimp only [pqxdhAuthCostedSims, shcrAuthAtomicProg]
    refine le_trans (liftAuth2Stage_totalQueries_le tlAuthPrim S
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authPrimIfacePrimQueryWeight tlAuthPrim_primW (shcrAuthDslProg S b) b.q_total) ?_
    dsimp only [shcrAuthDslProg]
    rw [show SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight = AuthHs.primW from rfl,
      show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthHs.primWS from rfl]
    exact shcrReductionAuthProg_totalQueries_le S b
  gdh_q_ddh       := fun b => by
    dsimp only [pqxdhAuthCostedSims, fgAuthGapDhAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlAuthGapDh S
      SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      chalIfaceChalQueryWeight tlAuthGapDh_chalW (fgAuthGapDhDslProg S b) b.q_total) ?_
    dsimp only [fgAuthGapDhDslProg]
    rw [show (SignalPqxdh.LegacyCosted.chalIfaceChalQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.gapDhDdhOracle).Tag → ℕ) =
        AuthHs.gdhChalW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthHs.gdhWS from rfl]
    exact fgAuthGapDhProg_totalChalQueries_le S b
  gdh_q_prim      := fun b => by
    dsimp only [pqxdhAuthCostedSims, fgAuthGapDhAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlAuthGapDh S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authChalIfacePrimQueryWeight tlAuthGapDh_primW (fgAuthGapDhDslProg S b) b.q_total) ?_
    dsimp only [fgAuthGapDhDslProg]
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.gapDhDdhOracle).Tag → ℕ) =
        AuthHs.gdhPrimW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthHs.gdhWS from rfl]
    exact fgAuthGapDhProg_totalPrimQueries_le S b
  ck_q_prim       := fun b => by
    dsimp only [pqxdhAuthCostedSims, prfCkAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlAuthPrim S
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authPrimIfacePrimQueryWeight tlAuthPrim_primW (prfCkRedProg S b.q_total) b.q_total) ?_
    rw [show SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight = AuthPrf.primW from rfl,
      show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthPrf.primWS from rfl]
    have h := prfCkRedProg_totalQueries_le S b.q_total b.q_total
    unfold primQueryBudget
    nlinarith
  mk_q_prim       := fun b => by
    dsimp only [pqxdhAuthCostedSims, prfMsgKeysAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlPrfMk S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authChalIfacePrimQueryWeight tlPrfMk_primW (prfMsgKeysRedProg S b.q_total) b.q_total) ?_
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.msgKeyPrfOracle).Tag → ℕ) =
        AuthPrf.mkPrimW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthPrf.mkWS from rfl]
    exact prfMsgKeysRedProg_totalPrimQueries_le_budget S b
  cpa_q_prim      := fun b => by
    dsimp only [pqxdhAuthCostedSims, aeadCpaAtomicProg]
    refine le_trans (liftAuth2Stage_totalQueries_le tlAuthPrim S
      SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authPrimIfacePrimQueryWeight tlAuthPrim_primW (aeadCpaDslProg S b) b.q_total) ?_
    dsimp only [aeadCpaDslProg]
    rw [show SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight = AuthAead.primW from rfl,
      show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthAead.primWS from rfl]
    exact aeadCpaRedProg_totalQueries_le S b
  int_q_prim      := fun b => by
    dsimp only [pqxdhAuthCostedSims, prfHmacAtomicProg]
    refine le_trans (liftAuth1Stage_totalQueries_le tlPrfHmac S
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
      SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
      authChalIfacePrimQueryWeight tlPrfHmac_primW (prfHmacDslProg S b) b.q_total) ?_
    dsimp only [prfHmacDslProg]
    rw [show (SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight :
        (SignalPqxdh.LegacyCosted.pqChalIface SignalPqxdh.LegacyCosted.hmacPrfOracle).Tag → ℕ) =
        AuthAead.chalPrimW by funext x; cases x <;> rfl]
    rw [show SignalPqxdh.LegacyCosted.samplerZeroQueryWeight = AuthAead.chalWS from rfl]
    exact prfHmacRedProg_totalQueries_prim_le S b
  sig_blocks      := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqAuthChalIface_qCost one_le_eufCmaSignOracle_qCost)
      S b ℓ (sigReductionAuthAtomicProg S b) rfl
      (sigReductionAuthAtomicProg_totalCost_le_stepCostBudget S b)
      (sigReductionAuthAtomicProg_size_le_budget S b)
  shcr_blocks     := fun b ℓ =>
    gred2BlockBounded_of_cost one_le_pqAuthPrimIface_qCost
      S b ℓ (shcrAuthAtomicProg S b) rfl
      (shcrAuthAtomicProg_totalCost_le_stepCostBudget S b)
      (shcrAuthAtomicProg_size_le_budget S b)
  gdh_blocks      := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqAuthChalIface_qCost one_le_gapDhDdhOracle_qCost)
      S b ℓ (fgAuthGapDhAtomicProg S b) rfl
      (fgAuthGapDhAtomicProg_totalCost_le_stepCostBudget S b)
      (fgAuthGapDhAtomicProg_size_le_budget S b)
  ck_blocks       := fun b ℓ =>
    gredBlockBounded_of_cost one_le_pqAuthPrimIface_qCost
      S b ℓ (prfCkAtomicProg S b) rfl
      (prfCkAtomicProg_totalCost_le_stepCostBudget S b)
      (prfCkAtomicProg_size_le_budget S b)
  mk_blocks       := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqAuthChalIface_qCost one_le_msgKeyPrfOracle_qCost)
      S b ℓ (prfMsgKeysAtomicProg S b) rfl
      (prfMsgKeysAtomicProg_totalCost_le_stepCostBudget S b)
      (prfMsgKeysAtomicProg_size_le_budget S b)
  cpa_blocks      := fun b ℓ =>
    gred2BlockBounded_of_cost one_le_pqAuthPrimIface_qCost
      S b ℓ (aeadCpaAtomicProg S b) rfl
      (aeadCpaAtomicProg_totalCost_le_stepCostBudget S b)
      (aeadCpaAtomicProg_size_le_budget S b)
  int_blocks      := fun b ℓ =>
    gredBlockBounded_of_cost (one_le_pqAuthChalIface_qCost one_le_hmacPrfOracle_qCost)
      S b ℓ (prfHmacAtomicProg S b) rfl
      (prfHmacAtomicProg_totalCost_le_stepCostBudget S b)
      (prfHmacAtomicProg_size_le_budget S b)

private def shcrAuthLegacyAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : KemShCrAdv where
  State := Mid (authSpec S) Bool (shcrAuthDslProg S b).π.denote (shcrAuthDslProg S b).σ.denote Bytes
  choosePk pk sk := (shcrAuthDslProg S b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct := (shcrAuthDslProg S b).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

private theorem shcrAuthLegacyAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : (shcrAuthLegacyAdv S b A).Bounded := by
  refine ⟨fun pk sk => ?_, fun st ss ct => ?_⟩
  · exact (AuthAead.queryBound_eval1 (shcrReductionAuthProg S b.q_total b.q_total)
      (fun q => isPrimQuery₀ q = true) AuthAead.primW AuthAead.primWS
      AuthAead.pqPrimIface_hw AuthAead.pqPrimIface_hU
      (fun _ => A.1.run) (pk, sk) b.q_total false).mono
      (shcrReductionAuthProg_totalQueries_le S b)
  · exact (AuthAead.queryBound_eval2 (shcrReductionAuthProg S b.q_total b.q_total)
      (fun q => isPrimQuery₀ q = true) AuthAead.primW AuthAead.primWS
      AuthAead.pqPrimIface_hw AuthAead.pqPrimIface_hU
      st (ss, ct) b.q_total false).mono
      (shcrReductionAuthProg_totalQueries_le S b)

private theorem cpa_choose_map_eq {S : Setup} {b : QueryBudget}
    (m1 : OracleComp PrimBaseSpec ((embedTy cpaChOutTy).denote ×
      Mid (authSpec S) Bool (embedTy (aeadCpaDslProg S b).π).denote
        (embedTy (aeadCpaDslProg S b).σ).denote (embedTy cpaChOutTy).denote))
    (m2 : OracleComp PrimBaseSpec (cpaChOutTy.denote ×
      Mid (authSpec S) Bool (aeadCpaDslProg S b).π.denote
        (aeadCpaDslProg S b).σ.denote cpaChOutTy.denote))
    (h : m1 = Prod.map (embedVal cpaChOutTy) (embedMid (ch := cpaChOutTy)) <$> m2) :
    (do let r ← m1; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) =
      (fun (ad, m0, m1, st) => (ad, m0, m1, embedMid (ch := cpaChOutTy) st)) <$>
        (do let r ← m2; pure (r.1.1, r.1.2.1, r.1.2.2, r.2)) := by
  subst h
  rw [bind_map_left, map_bind]
  refine _root_.bind_congr fun ⟨⟨ad, m0, m1⟩, st⟩ => ?_
  simp [embedVal]

/-- Semantic query bounds for `(pqxdhAuthCostedSims S).eval`. -/
theorem pqxdhAuthCostedSims_simBounds (S : Setup) :
    AuthReductionQueryBounds S (pqxdhAuthCostedSims S).eval where
  sig_bounded  := fun b A => by
    have hEq : (pqxdhAuthCostedSims S).eval.sig b A = sigReductionAuthDslAdv2 S b A :=
      congrArg (fun r =>
        ({ run := r, q_sig := 2 * S.N_spk_tot, q_prim := primQueryBudget S b } : SigEufCmaAdv))
        (funext fun pk => sigReductionAuthAtomicProg_eval_eq S b (fun _ => A.1.run) pk)
    rw [hEq]
    exact sigReductionAuthDslAdv2_bounded S b A
  shcr_bounded := fun b A => by
    refine kemShCrAdv_bounded_of_state_retract (A := shcrAuthLegacyAdv S b A) rfl
      (embedMid (π := (shcrAuthDslProg S b).π) (σ := (shcrAuthDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (projMid (π := (shcrAuthDslProg S b).π) (σ := (shcrAuthDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568))
      (fun pk sk => ?_) (fun st' ss ct => ?_) (shcrAuthLegacyAdv_bounded S b A)
    · exact liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl) (shcrAuthDslProg S b)
        (fun _ => A.1.run) (pk, sk) b.q_total false
    · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
      have hRet := embedMid_projMid
        (π := (shcrAuthDslProg S b).π) (σ := (shcrAuthDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568) st'
      have h := liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (shcrAuthDslProg S b)
        (projMid (π := (shcrAuthDslProg S b).π) (σ := (shcrAuthDslProg S b).σ)
          (ch := SignalPqxdh.LegacyCosted.B 1568) st') (ss, ct) b.q_total false
      rw [hRet, hId, id_map] at h
      exact h
  gdh_bounded  := fun b A => by
    have hRun : ((pqxdhAuthCostedSims S).eval.gdh b A).run =
        (fgAuthGapDhDslAdv S b A).run := by
      funext U V
      exact fgAuthGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V
    refine ⟨fun U V => ?_, fun U V => ?_⟩
    · rw [hRun]
      exact ((fgAuthGapDhDslAdv_bounded S b A).1 U V).mono
        (fgAuthGapDhDslAdv_q_ddh_le S b A)
    · rw [hRun]
      exact (fgAuthGapDhDslAdv_bounded S b A).2 U V
  ck_bounded   := fun b A => by
    have hBound := prfCkReductionAuthFixed_bounded S b A
    have hEq := prfCkReductionAuthFixedDslAdv_eq S b A
    intro mkSeed ck1
    change ((prfCkAtomicProg S b).eval (fun _ => A.1.run) (mkSeed, ck1)).IsQueryBoundP
      (fun q => isPrimQuery₀ q = true) (primQueryBudget S b)
    rw [prfCkAtomicProg_eval_eq S b (fun _ => A.1.run) mkSeed ck1]
    change ((prfCkReductionAuthFixedDslAdv S b A).dist mkSeed ck1).IsQueryBoundP
      (fun q => isPrimQuery₀ q = true) (primQueryBudget S b)
    rw [hEq]
    exact (hBound mkSeed ck1).mono (prfCkReductionAuthFixed_prim_queries S b A)
  mk_bounded   := fun b A => by
    have hRun : ((pqxdhAuthCostedSims S).eval.mk b A).run = (prfMsgKeysDslAdv S b A).run :=
      prfMsgKeysAtomicProg_eval_eq S b (fun _ => A.1.run)
    refine ⟨?_, ?_⟩
    · rw [hRun]
      exact (prfMsgKeysDslAdv_bounded S b A).1
    · rw [hRun]
      exact (prfMsgKeysDslAdv_bounded S b A).2.mono (prfMsgKeysDslAdv_prim_queries S b A)
  cpa_bounded  := fun b A => by
    refine aeadIndCpaAdv_bounded_of_state_retract (A := aeadCpaDslAdv S b A.1) rfl
      (embedMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ) (ch := cpaChOutTy))
      (projMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ) (ch := cpaChOutTy))
      ?_ (fun st' c? => ?_) (aeadCpaDslAdv_bounded S b A.1)
    · exact cpa_choose_map_eq _ _ (liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl)
        (aeadCpaDslProg S b) (fun _ => A.1.run) () b.q_total false)
    · have hc : embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c? = c? := by cases c? <;> rfl
      have hId : embedVal .bool = id := rfl
      have hRet := embedMid_projMid
        (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ) (ch := cpaChOutTy) st'
      have h : (aeadCpaAtomicProg S b).eval2
          (embedMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ) (ch := cpaChOutTy)
            (projMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ)
              (ch := cpaChOutTy) st'))
          (embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c?) b.q_total false =
          embedVal .bool <$> (aeadCpaDslProg S b).eval2
            (projMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ)
              (ch := cpaChOutTy) st')
            c? b.q_total false :=
        liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (aeadCpaDslProg S b)
          (projMid (π := (aeadCpaDslProg S b).π) (σ := (aeadCpaDslProg S b).σ)
            (ch := cpaChOutTy) st') c? b.q_total false
      rw [hRet, hc, hId, id_map] at h
      exact h
  int_bounded  := fun b A => by
    have hEq : (pqxdhAuthCostedSims S).eval.int b A = prfHmacDslAdv S b A :=
      congrArg (fun r =>
        ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfHmacAdv))
        (prfHmacAtomicProg_eval_eq S b (fun _ => A.1.run))
    rw [hEq]
    exact prfHmacDslAdv_bounded S b A

/-! ## Advantage equalities with shallow simulators -/

theorem pqxdhKeyIndCostedSims_sig_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    SigEufCma P ((pqxdhKeyIndCostedSims S).eval.sig b A) =
      SigEufCma P ((pqxdhKeyIndSimulators S).sig b A) := by
  have hAdv : (pqxdhKeyIndCostedSims S).eval.sig b A =
      { run := fun pk => (sigKeyIndDslProg true S b).eval (fun _ => A.1.run) pk
        q_sig := 2 * S.N_spk_tot
        q_prim := primQueryBudget S b } :=
    congrArg (fun r =>
      ({ run := r, q_sig := 2 * S.N_spk_tot, q_prim := primQueryBudget S b } : SigEufCmaAdv))
      (funext fun pk => sigKeyIndAtomicProg_eval_eq true S b (fun _ => A.1.run) pk)
  rw [hAdv]
  exact sigKeyIndProg_sigEufCma_eq P true S b A

theorem pqxdhKeyIndCostedSims_shcr_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P ((pqxdhKeyIndCostedSims S).eval.shcr b A) =
      KemShCr P ((pqxdhKeyIndSimulators S).shcr b A) := by
  refine Eq.trans (kemShCr_eq_of_state_map P (shcrKeyIndDslAdv S b A)
    ((pqxdhKeyIndCostedSims S).eval.shcr b A)
    (embedMid (ch := SignalPqxdh.LegacyCosted.B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_))
    (KemShCr_shcrKeyIndDslAdv P S b A)
  · exact liftKeyInd2Stage_eval1 tlPrimKeyInd S (shcrKeyIndDslProg S b)
      (shcrKeyIndProg_init_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyIndProg_handlePre_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyIndProg_chDone_unsupported S b.q_total (keyIndLoopBound b))
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
    have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S (shcrKeyIndDslProg S b)
      (shcrKeyIndProg_resume_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyIndProg_handlePost_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyIndProg_finish_unsupported S b.q_total (keyIndLoopBound b))
      st (ss, ct) b.q_total false
    rw [hId, id_map] at h
    exact h

theorem pqxdhKeyIndCostedSims_gdh_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDH P P.isValidDhTriple P.pow8 ((pqxdhKeyIndCostedSims S).eval.gdh b A) =
      GapDH P P.isValidDhTriple P.pow8 ((pqxdhKeyIndSimulators S).gdh b A) := by
  have hAdv : (pqxdhKeyIndCostedSims S).eval.gdh b A =
      { run := fun U V => (fgKeyIndGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
        q_ddh := gdhQueryBudget S b
        q_prim := primQueryBudget S b } :=
    congrArg (fun r =>
      ({ run := r, q_ddh := gdhQueryBudget S b, q_prim := primQueryBudget S b } : GapDhAdv))
      (funext fun U => funext fun V => fgKeyIndGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V)
  rw [hAdv]
  exact (fgKeyIndGapDh2Prog_gapDh_eq P P.isValidDhTriple P.pow8 S b A).trans
    (fgKeyIndGapDhProg_gapDh_eq P P.isValidDhTriple P.pow8 S b A)

theorem pqxdhAuthCostedSims_sig_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    SigEufCma P ((pqxdhAuthCostedSims S).eval.sig b A) =
      SigEufCma P ((pqxdhAuthSimulators S).sig b A) := by
  have hAdv : (pqxdhAuthCostedSims S).eval.sig b A = sigReductionAuthDslAdv2 S b A :=
    congrArg (fun r =>
      ({ run := r, q_sig := 2 * S.N_spk_tot, q_prim := primQueryBudget S b } : SigEufCmaAdv))
      (funext fun pk => sigReductionAuthAtomicProg_eval_eq S b (fun _ => A.1.run) pk)
  rw [hAdv]
  exact sigReductionAuthProg2_sigEufCma_eq P S b A

theorem pqxdhAuthCostedSims_shcr_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    KemShCr P ((pqxdhAuthCostedSims S).eval.shcr b A) =
      KemShCr P ((pqxdhAuthSimulators S).shcr b A) := by
  refine Eq.trans (kemShCr_eq_of_state_map P (shcrAuthDslAdv S b A.1)
    ((pqxdhAuthCostedSims S).eval.shcr b A)
    (embedMid (ch := SignalPqxdh.LegacyCosted.B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_))
    (shcrAuthDslAdv_kemShCr_eq P S b A)
  · exact liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl) (shcrAuthDslProg S b)
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
    have h := liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (shcrAuthDslProg S b)
      st (ss, ct) b.q_total false
    rw [hId, id_map] at h
    exact h

theorem pqxdhAuthCostedSims_gdh_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    GapDH P P.isValidDhTriple P.pow8 ((pqxdhAuthCostedSims S).eval.gdh b A) =
      GapDH P P.isValidDhTriple P.pow8 ((pqxdhAuthSimulators S).gdh b A) := by
  have hAdv : (pqxdhAuthCostedSims S).eval.gdh b A =
      { run := fun U V => (fgAuthGapDhDslProg S b).eval (fun _ => A.1.run) (U, V)
        q_ddh := 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot
        q_prim := primQueryBudget S b } :=
    congrArg (fun r =>
      ({ run := r, q_ddh := 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot, q_prim := primQueryBudget S b } : GapDhAdv))
      (funext fun U => funext fun V => fgAuthGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V)
  rw [hAdv]
  exact fgAuthGapDhProg_gapDh_eq P P.isValidDhTriple P.pow8 S b A

theorem pqxdhAuthCostedSims_ck_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfChainKey P ((pqxdhAuthCostedSims S).eval.ck b A) =
      PrfChainKey P ((pqxdhAuthSimulators S).ck b A) := by
  have hAdv : (pqxdhAuthCostedSims S).eval.ck b A =
      { dist := fun mkSeedChal ck1_1Chal =>
          (prfCkRedProg S b.q_total).eval (fun _ => A.1.run) (mkSeedChal, ck1_1Chal)
        q_prf := 1
        q_prim := primQueryBudget S b } :=
    congrArg (fun r =>
      ({ dist := r, q_prf := 1, q_prim := primQueryBudget S b } : PrfCkAdv))
      (funext fun mkSeed => funext fun ck1 => prfCkAtomicProg_eval_eq S b (fun _ => A.1.run) mkSeed ck1)
  rw [hAdv]
  exact prfCkRedProg_prfCk_eq P S b A

theorem pqxdhAuthCostedSims_mk_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfMsgKeys P ((pqxdhAuthCostedSims S).eval.mk b A) =
      PrfMsgKeys P ((pqxdhAuthSimulators S).mk b A) := by
  have hAdv : (pqxdhAuthCostedSims S).eval.mk b A =
      { run := (prfMsgKeysRedProg S b.q_total).eval (fun _ => A.1.run) ()
        q_prf := S.N_recv_tot + 1
        q_prim := primQueryBudget S b } :=
    congrArg (fun r =>
      ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfMsgKeysAdv))
      (prfMsgKeysAtomicProg_eval_eq S b (fun _ => A.1.run))
  rw [hAdv]
  exact prfMsgKeysRedProg_prfMsgKeys_eq P S b A

theorem pqxdhAuthCostedSims_cpa_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    AeadIndCpa P ((pqxdhAuthCostedSims S).eval.cpa b A) =
      AeadIndCpa P ((pqxdhAuthSimulators S).cpa b A) := by
  refine Eq.trans (aeadIndCpa_eq_of_state_map P (aeadCpaDslAdv S b A.1)
    ((pqxdhAuthCostedSims S).eval.cpa b A) (embedMid (ch := cpaChOutTy))
    ?_ (fun st c? => ?_))
    (aeadCpaDslAdv_aeadIndCpa_eq P S b A)
  · exact cpa_choose_map_eq _ _ (liftAuth2Stage_eval1 tlAuthPrim S (fun _ => rfl)
      (aeadCpaDslProg S b) (fun _ => A.1.run) () b.q_total false)
  · have hc : embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c? = c? := by cases c? <;> rfl
    have hId : embedVal .bool = id := rfl
    have h : (aeadCpaAtomicProg S b).eval2 (embedMid (ch := cpaChOutTy) st)
        (embedVal (.opt (SignalPqxdh.LegacyCosted.B 32)) c?) b.q_total false =
        embedVal .bool <$> (aeadCpaDslProg S b).eval2 st c? b.q_total false :=
      liftAuth2Stage_eval2 tlAuthPrim S (fun _ => rfl) (aeadCpaDslProg S b)
        st c? b.q_total false
    rw [hc, hId, id_map] at h
    exact h

theorem pqxdhAuthCostedSims_int_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmac P ((pqxdhAuthCostedSims S).eval.int b A) =
      PrfHmac P ((pqxdhAuthSimulators S).int b A) := by
  have hAdv : (pqxdhAuthCostedSims S).eval.int b A = prfHmacDslAdv S b A :=
    congrArg (fun r =>
      ({ run := r, q_prf := S.N_recv_tot + 1, q_prim := primQueryBudget S b } : PrfHmacAdv))
      (prfHmacAtomicProg_eval_eq S b (fun _ => A.1.run))
  rw [hAdv]
  exact prfHmacRedProg_prfHmac_eq S P b A

/-- Combined `PqxdhReds S` bundle for `KeyInd` and `Auth`. -/
def pqxdhReds (S : Setup) : PqxdhReds S where
  keyInd := pqxdhKeyIndCostedSims S
  auth   := pqxdhAuthCostedSims S

/-- Combined syntactic and semantic bounds for `pqxdhReds S`. -/
theorem pqxdhReds_bounds (S : Setup) : PqxdhBounds S (pqxdhReds S) :=
  ⟨pqxdhKeyIndCostedSims_costedBounds S,
   pqxdhKeyIndCostedSims_simBounds S,
   pqxdhAuthCostedSims_costedBounds S,
   pqxdhAuthCostedSims_simBounds S⟩

end Proofs.SignalPqxdh.Security

namespace SignalPqxdh.Security

export _root_.Proofs.SignalPqxdh.Security (pqOpsSizeHonest pqSampSizeHonest pqxdhKeyIndCostedSims keyIndCostedSims pqxdhKeyIndCostedSims_costedBounds pqxdhKeyIndCostedSims_simBounds pqxdhAuthCostedSims authCostedSims pqxdhAuthCostedSims_costedBounds pqxdhAuthCostedSims_simBounds pqxdhReds pqxdhReds_bounds)

end SignalPqxdh.Security

namespace SignalPqxdh

export _root_.Proofs.SignalPqxdh.Security (pqOpsSizeHonest pqSampSizeHonest pqxdhKeyIndCostedSims keyIndCostedSims pqxdhKeyIndCostedSims_costedBounds pqxdhKeyIndCostedSims_simBounds pqxdhAuthCostedSims authCostedSims pqxdhAuthCostedSims_costedBounds pqxdhAuthCostedSims_simBounds pqxdhReds pqxdhReds_bounds)

end SignalPqxdh

namespace SignalPqxdh.Costed

export _root_.Proofs.SignalPqxdh.Security (pqOpsSizeHonest pqSampSizeHonest pqxdhKeyIndCostedSims keyIndCostedSims pqxdhKeyIndCostedSims_costedBounds pqxdhKeyIndCostedSims_simBounds pqxdhAuthCostedSims authCostedSims pqxdhAuthCostedSims_costedBounds pqxdhAuthCostedSims_simBounds pqxdhReds pqxdhReds_bounds)

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

export _root_.Proofs.SignalPqxdh.Security (pqOpsSizeHonest pqSampSizeHonest pqxdhKeyIndCostedSims keyIndCostedSims pqxdhKeyIndCostedSims_costedBounds pqxdhKeyIndCostedSims_simBounds pqxdhAuthCostedSims authCostedSims pqxdhAuthCostedSims_costedBounds pqxdhAuthCostedSims_simBounds pqxdhReds pqxdhReds_bounds)

end SignalPqxdh.Security.Costed
