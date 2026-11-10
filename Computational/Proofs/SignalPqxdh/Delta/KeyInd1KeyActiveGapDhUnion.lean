/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhEval -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Active Creation-Order `GapDhWithSign` Averaging and Union Bound

Proves the four-way flat-index averaging identity for `fgKeyInd1KeyGapDhActiveAdv4`, the active
creation-order union bound for `badKeyIndFgAny4`, and `ki1KeyActiveGapDh_of_four_legs` concluding
`KI1KeyActiveG3BoundStmt` for `(pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh`.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory (measure_ne_top)
open OracleSpec OracleComp
open SignalPqxdh (
  Setup Bytes KeyIndState KeyIndInitiatorEntry KeyIndAdversary
  QueryBudget BoundedAdv Primitives CryptoWellFormedPrimitivesδ KemDeltaCorrectReal
  GapDhWithSignAdv GapDhWithSign gapDhWithSignExp GapDhWithSignReal
  sampleScalar32 activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount
)
open SignalPqxdh.Security (kemDecapsFailureTermReal keyInd1KeyAllTestedClean opkSlotFlatIdx)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open SignalPqxdh.Security.FgGapDh (initSessionSlotIdx)
open SignalPqxdh.Security.FgGapDh1Key (unifGdhSign)
open Proofs.SignalPqxdh.Security (
  keyInd1KeyAdvG3 keyIndAdvG3_1Key keyInd1KeyExpG3 keyIndExpG3_1Key
  pqxdhKeyInd1KeyShCrImpl pqxdhKeyIndShCrImpl1Key
  runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
  finalizeKeyIndG3 badKeyIndFgAny4
  keyIndAdvG3_1Key_le_prob_badKeyIndFgAny4_add_corr_1Key
  mul_toReal_sampleIndexRange_bind_eq_sum sum_range_mul_div_mod
)
open Proofs.SignalPqxdh.Security.FgGapDh (
  KeyIndFgCutoffState spkBundleFlatIdxVal
  badKeyIndFgDh1At badKeyIndFgDh3At badKeyIndFgAny prob_or_le_add_fg
  toReal_any_double_range_le_sum2 evalDist_bind_true_mono_of_support
)
open Proofs.SignalPqxdh.Security.FgGapDh.Ik (badKeyIndFgDh2At)
open Proofs.SignalPqxdh.Security.FgGapDh.Opk (badKeyIndFgDh4At)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (
  runKeyIndFgSim1Key gapDhWithSignFullImpl simulateQ_gapDhWithSignFullImpl_unifGdhSign
)
open Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveG3BoundStmt prob_hasBadKemCorrRecords_1Key_le)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (fgActiveTotalIndexCount pqxdhKeyInd1KeyActiveCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (
  fgKeyInd1KeyGapDhActiveAdvAt fgKeyInd1KeyGapDhActiveAdvAtIk fgKeyInd1KeyGapDhActiveAdvAtOpk
  fgKeyInd1KeyGapDhActiveRunAtFlat fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveAdv4
  fgKeyInd1KeyGapDhActiveAdvAtFlat_dh1 fgKeyInd1KeyGapDhActiveAdvAtFlat_dh3
  fgKeyInd1KeyGapDhActiveAdvAtFlat_dh2 fgKeyInd1KeyGapDhActiveAdvAtFlat_dh4
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre (
  prinSlotAtOrd spkSlotAtOrd opkSlotAtOrd sessSlotAtOrd
  isOpkInitSession opkSessions sessOpkSlotAtOrd
  badKeyIndFgDh1OrdAt badKeyIndFgDh3OrdAt badKeyIndFgDh2OrdAt badKeyIndFgDh4OrdAt
  prinSlotAtOrd_eq spkSlotAtOrd_eq opkSlotAtOrd_eq sessSlotAtOrd_eq sessOpkSlotAtOrd_eq
  ordLookup_exists_of_mem
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhEval (
  gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_eq
)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhUnion

public section
/-! ## Flat-index averaging decomposition -/

theorem keyInd1KeyAdvG3_eq_keyIndAdvG3_1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    keyInd1KeyAdvG3 S P A = keyIndAdvG3_1Key S P A := by
  have hImpl : pqxdhKeyInd1KeyShCrImpl false S P = pqxdhKeyIndShCrImpl1Key false S P := by
    funext q; cases q <;> rfl
  have hRun : runKeyInd1KeyShCrSim S P A = runKeyIndShCrSim1Key S P A := by
    unfold runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
    rw [hImpl]
  unfold keyInd1KeyAdvG3 keyIndAdvG3_1Key keyInd1KeyExpG3 keyIndExpG3_1Key
    finalizeKeyIndG3 keyInd1KeyAllTestedClean
  rw [hRun]

private theorem evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A)] =
    𝒟[sampleIndexRange (fgActiveTotalIndexCount S b.q_on) >>= fun idx =>
        gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A)] := by
  have hStep1 :
      gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) := by
    unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdv4
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhWithSignFullImpl P u ddh)
        (unifGdhSign (sampleIndexRange (fgActiveTotalIndexCount S b.q_on)) >>= fun idx =>
          fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] =
      𝒟[do
        let u ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let v ← sampleScalar32
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (sampleIndexRange (fgActiveTotalIndexCount S b.q_on)) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (sampleIndexRange (fgActiveTotalIndexCount S b.q_on))]
  rfl

/-- Decomposes `GapDhWithSignReal` of `fgKeyInd1KeyGapDhActiveAdv4` into the four active
    creation-order sub-rectangles (`DH1`, `DH3`, `DH2`, `DH4`). -/
theorem sum_gapDhWithSign_fgKeyInd1KeyGapDhActiveAdv4_eq
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    let n_id := activeIdCount S b.q_on
    let n_spk := activeSpkCount S b.q_on
    let n_opk := activeOpkCount S b.q_on
    let n_send := activeSendCount S b.q_on
    let n_send_opk := activeSendOpkCount S b.q_on
    (∑ p ∈ Finset.range n_id, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt true p spk S b A)) +
    (∑ s ∈ Finset.range n_send, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt false s spk S b A)) +
    (∑ s ∈ Finset.range n_send, ∑ p ∈ Finset.range n_id,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtIk s p S b A)) +
    (∑ sOpk ∈ Finset.range n_send_opk, ∑ opk ∈ Finset.range n_opk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpk opk S b A)) =
    (fgActiveTotalIndexCount S b.q_on : ℝ) *
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdv4 S b A) := by
  dsimp only
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  have hExp := evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdv4_eq
    P P.isValidDhTriple P.pow8 S b A
  have hSum := mul_toReal_sampleIndexRange_bind_eq_sum (fgActiveTotalIndexCount S b.q_on)
    (fun idx => gapDhWithSignExp P P.isValidDhTriple P.pow8
      (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A))
  have hRhs :
      (fgActiveTotalIndexCount S b.q_on : ℝ) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A) =
      ∑ idx ∈ Finset.range (fgActiveTotalIndexCount S b.q_on),
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A) := by
    unfold GapDhWithSignReal GapDhWithSign
    rw [hExp]
    exact hSum
  rw [hRhs]
  have hTotEq : fgActiveTotalIndexCount S b.q_on =
      n_id * n_spk + n_send * n_spk + n_send * n_id + n_send_opk * n_opk := rfl
  rw [hTotEq, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (n_id * n_spk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat x S b A) =
      ∑ p ∈ Finset.range n_id, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt true p spk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [fgKeyInd1KeyGapDhActiveAdvAtFlat_dh1 S b A x (Finset.mem_range.mp hx)]
  have h2 : ∑ x ∈ Finset.range (n_send * n_spk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat (n_id * n_spk + x) S b A) =
      ∑ s ∈ Finset.range n_send, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt false s spk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send * n_spk := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh3 S b A (n_id * n_spk + x)
      (by dsimp only [n_id, n_spk]; omega)
      (by dsimp only [n_id, n_spk, n_send] at hxLt ⊢; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  have h3 : ∑ x ∈ Finset.range (n_send * n_id),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat (n_id * n_spk + n_send * n_spk + x) S b A) =
      ∑ s ∈ Finset.range n_send, ∑ p ∈ Finset.range n_id,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtIk s p S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send * n_id := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh2 S b A
      (n_id * n_spk + n_send * n_spk + x)
      (by dsimp only [n_id, n_spk, n_send]; omega)
      (by dsimp only [n_id, n_spk, n_send] at hxLt ⊢; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  have h4 : ∑ x ∈ Finset.range (n_send_opk * n_opk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat
          (n_id * n_spk + n_send * n_spk + n_send * n_id + x) S b A) =
      ∑ sOpk ∈ Finset.range n_send_opk, ∑ opk ∈ Finset.range n_opk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpk opk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send_opk * n_opk := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh4 S b A
      (n_id * n_spk + n_send * n_spk + n_send * n_id + x)
      (by dsimp only [n_id, n_spk, n_send]; omega)
      (by rw [hTotEq]; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  rw [h1, h2, h3, h4]

/-! ## Creation-order witness extraction and union bound -/

private theorem isOpkInitSession_of_initSessionSlotIdx_lt {S : Setup}
    {s : KeyIndInitiatorEntry S} (hLt : initSessionSlotIdx s.sid < S.N_send_opk_tot) :
    isOpkInitSession s = true := by
  unfold isOpkInitSession
  cases hSid : s.sid with
  | sendOPK u i => rfl
  | sendNoOPK u i =>
    exfalso
    rw [hSid] at hLt
    dsimp [initSessionSlotIdx] at hLt
    omega
  | recvOPK u e j =>
    exfalso
    rw [hSid] at hLt
    dsimp [initSessionSlotIdx, Setup.N_send_tot] at hLt
    omega
  | recvNoOPK u e =>
    exfalso
    rw [hSid] at hLt
    dsimp [initSessionSlotIdx, Setup.N_send_tot] at hLt
    omega

private theorem exists_prinOrd_of_find {S : Setup} {st : KeyIndState S} {uIdx : Nat}
    {kv : Nat × SignalPqxdh.PrincipalEntry}
    (hFind : st.principals.find? (fun (u, _) => u == uIdx) = some kv) :
    ∃ pOrd < st.principals.length, prinSlotAtOrd S st pOrd = uIdx := by
  have hMem : kv ∈ st.principals := List.mem_of_find?_eq_some hFind
  have hEq : kv.1 = uIdx := by simpa using List.find?_some hFind
  obtain ⟨pOrd, hOrdLt, hOrdEq⟩ :=
    ordLookup_exists_of_mem (proj := Prod.fst) (dflt := S.N_id) hMem
  refine ⟨pOrd, hOrdLt, ?_⟩
  rw [prinSlotAtOrd_eq, hOrdEq, hEq]

private theorem exists_spkOrd_of_find {S : Setup} {st : KeyIndState S} {bIdx : Nat}
    {kv : (Nat × Nat) × SignalPqxdh.SpkBundleEntry}
    (hFind : st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) = some kv) :
    ∃ spkOrd < st.spkBundles.length, spkSlotAtOrd S st spkOrd = bIdx := by
  have hMem : kv ∈ st.spkBundles := List.mem_of_find?_eq_some hFind
  have hEq : spkBundleFlatIdxVal S kv.1 = bIdx := by simpa using List.find?_some hFind
  obtain ⟨spkOrd, hOrdLt, hOrdEq⟩ :=
    ordLookup_exists_of_mem (proj := fun kv => spkBundleFlatIdxVal S kv.1)
      (dflt := S.N_spk_tot) hMem
  refine ⟨spkOrd, hOrdLt, ?_⟩
  rw [spkSlotAtOrd_eq, hOrdEq, hEq]

private theorem exists_opkOrd_of_find {S : Setup} {st : KeyIndState S} {oIdx : Nat}
    {kv : (Nat × Nat × Nat) × SignalPqxdh.OpkEntry}
    (hFind : st.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) = some kv) :
    ∃ opkOrd < st.opkEntries.length, opkSlotAtOrd S st opkOrd = oIdx := by
  have hMem : kv ∈ st.opkEntries := List.mem_of_find?_eq_some hFind
  have hEq : opkSlotFlatIdx S kv.1 = oIdx := by simpa using List.find?_some hFind
  obtain ⟨opkOrd, hOrdLt, hOrdEq⟩ :=
    ordLookup_exists_of_mem (proj := fun kv => opkSlotFlatIdx S kv.1)
      (dflt := S.N_opk_tot) hMem
  refine ⟨opkOrd, hOrdLt, ?_⟩
  rw [opkSlotAtOrd_eq, hOrdEq, hEq]

private theorem exists_sessOrd_of_find {S : Setup} {st : KeyIndState S} {sIdx : Nat}
    {s : KeyIndInitiatorEntry S}
    (hFind : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) = some s) :
    ∃ sOrd < st.sessions.length, sessSlotAtOrd S st sOrd = sIdx := by
  have hMem : s ∈ st.sessions := List.mem_of_find?_eq_some hFind
  have hEq : initSessionSlotIdx s.sid = sIdx := by simpa using List.find?_some hFind
  obtain ⟨sOrd, hOrdLt, hOrdEq⟩ :=
    ordLookup_exists_of_mem (proj := fun s => initSessionSlotIdx s.sid)
      (dflt := S.N_send_tot) hMem
  refine ⟨sOrd, hOrdLt, ?_⟩
  rw [sessSlotAtOrd_eq, hOrdEq, hEq]

private theorem exists_sessOpkOrd_of_find {S : Setup} {st : KeyIndState S} {sIdx : Nat}
    (hsIdx : sIdx < S.N_send_opk_tot) {s : KeyIndInitiatorEntry S}
    (hFind : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) = some s) :
    ∃ sOpkOrd < (opkSessions st).length, sessOpkSlotAtOrd S st sOpkOrd = sIdx := by
  have hMem : s ∈ st.sessions := List.mem_of_find?_eq_some hFind
  have hEq : initSessionSlotIdx s.sid = sIdx := by simpa using List.find?_some hFind
  have hOpk : isOpkInitSession s = true :=
    isOpkInitSession_of_initSessionSlotIdx_lt (hEq ▸ hsIdx)
  have hMemOpk : s ∈ opkSessions st := List.mem_filter.mpr ⟨hMem, hOpk⟩
  obtain ⟨sOpkOrd, hOrdLt, hOrdEq⟩ :=
    ordLookup_exists_of_mem (proj := fun s => initSessionSlotIdx s.sid)
      (dflt := S.N_send_tot) hMemOpk
  refine ⟨sOpkOrd, hOrdLt, ?_⟩
  rw [sessOpkSlotAtOrd_eq, hOrdEq, hEq]

theorem badKeyIndFgAny4_imp_exists_ord {S : Setup} (P : Primitives) (maxLen : Nat)
    (n_id n_spk n_opk n_send n_send_opk : Nat) (st : KeyIndState S) (advRoLog : List Bytes)
    (hPrin : st.principals.length ≤ n_id)
    (hSpk : st.spkBundles.length ≤ n_spk)
    (hOpk : st.opkEntries.length ≤ n_opk)
    (hSess : st.sessions.length ≤ n_send)
    (hSessOpk : (opkSessions st).length ≤ n_send_opk)
    (hBad : badKeyIndFgAny4 P maxLen st advRoLog = true) :
    (∃ pOrd < n_id, ∃ spkOrd < n_spk,
        badKeyIndFgDh1OrdAt P maxLen pOrd spkOrd st advRoLog = true) ∨
    (∃ sOrd < n_send, ∃ spkOrd < n_spk,
        badKeyIndFgDh3OrdAt P maxLen sOrd spkOrd st advRoLog = true) ∨
    (∃ sOrd < n_send, ∃ pOrd < n_id,
        badKeyIndFgDh2OrdAt P maxLen sOrd pOrd st advRoLog = true) ∨
    (∃ sOpkOrd < n_send_opk, ∃ opkOrd < n_opk,
        badKeyIndFgDh4OrdAt P maxLen sOpkOrd opkOrd st advRoLog = true) := by
  unfold badKeyIndFgAny4 badKeyIndFgAny at hBad
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at hBad
  rcases hBad with ((⟨uIdx, _, bIdx, _, h1⟩ | ⟨sIdx, _, bIdx, _, h3⟩) |
      ⟨sIdx, _, kIdx, _, h2⟩) | ⟨sIdx, hsIdx, oIdx, _, h4⟩
  · have h1' := h1
    unfold badKeyIndFgDh1At at h1'
    cases hFP : st.principals.find? (fun (u, _) => u == uIdx) with
    | none => simp [hFP] at h1'
    | some kvP =>
      cases hFB : st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => simp [hFP, hFB] at h1'
      | some kvB =>
        obtain ⟨pOrd, hpLt, hpEq⟩ := exists_prinOrd_of_find hFP
        obtain ⟨spkOrd, hspkLt, hspkEq⟩ := exists_spkOrd_of_find hFB
        left
        refine ⟨pOrd, Nat.lt_of_lt_of_le hpLt hPrin, spkOrd, Nat.lt_of_lt_of_le hspkLt hSpk, ?_⟩
        unfold badKeyIndFgDh1OrdAt
        rwa [hpEq, hspkEq]
  · have h3' := h3
    unfold badKeyIndFgDh3At at h3'
    cases hFS : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => simp [hFS] at h3'
    | some s =>
      cases hFB : st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => simp [hFS, hFB] at h3'
      | some kvB =>
        obtain ⟨sOrd, hsLt, hsEq⟩ := exists_sessOrd_of_find hFS
        obtain ⟨spkOrd, hspkLt, hspkEq⟩ := exists_spkOrd_of_find hFB
        right; left
        refine ⟨sOrd, Nat.lt_of_lt_of_le hsLt hSess, spkOrd, Nat.lt_of_lt_of_le hspkLt hSpk, ?_⟩
        unfold badKeyIndFgDh3OrdAt
        rwa [hsEq, hspkEq]
  · have h2' := h2
    unfold badKeyIndFgDh2At at h2'
    cases hFS : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => simp [hFS] at h2'
    | some s =>
      cases hFP : st.principals.find? (fun (u, _) => u == kIdx) with
      | none => simp [hFS, hFP] at h2'
      | some kvP =>
        obtain ⟨sOrd, hsLt, hsEq⟩ := exists_sessOrd_of_find hFS
        obtain ⟨pOrd, hpLt, hpEq⟩ := exists_prinOrd_of_find hFP
        right; right; left
        refine ⟨sOrd, Nat.lt_of_lt_of_le hsLt hSess, pOrd, Nat.lt_of_lt_of_le hpLt hPrin, ?_⟩
        unfold badKeyIndFgDh2OrdAt
        rwa [hsEq, hpEq]
  · have h4' := h4
    unfold badKeyIndFgDh4At at h4'
    cases hFS : st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => simp [hFS] at h4'
    | some s =>
      cases hFO : st.opkEntries.find? (fun (k, _) => opkSlotFlatIdx S k == oIdx) with
      | none => simp [hFS, hFO] at h4'
      | some kvO =>
        obtain ⟨sOpkOrd, hsLt, hsEq⟩ := exists_sessOpkOrd_of_find hsIdx hFS
        obtain ⟨opkOrd, hoLt, hoEq⟩ := exists_opkOrd_of_find hFO
        right; right; right
        refine ⟨sOpkOrd, Nat.lt_of_lt_of_le hsLt hSessOpk,
          opkOrd, Nat.lt_of_lt_of_le hoLt hOpk, ?_⟩
        unfold badKeyIndFgDh4OrdAt
        rwa [hsEq, hoEq]

private def badKeyIndFgOrdAny4 {S : Setup} (P : Primitives)
    (maxLen n_id n_spk n_opk n_send n_send_opk : Nat)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  (((List.range n_id).any (fun pOrd =>
      (List.range n_spk).any (fun spkOrd =>
        badKeyIndFgDh1OrdAt P maxLen pOrd spkOrd st advRoLog))) ||
    ((List.range n_send).any (fun sOrd =>
      (List.range n_spk).any (fun spkOrd =>
        badKeyIndFgDh3OrdAt P maxLen sOrd spkOrd st advRoLog)))) ||
  ((List.range n_send).any (fun sOrd =>
    (List.range n_id).any (fun pOrd =>
      badKeyIndFgDh2OrdAt P maxLen sOrd pOrd st advRoLog))) ||
  ((List.range n_send_opk).any (fun sOpkOrd =>
    (List.range n_opk).any (fun opkOrd =>
      badKeyIndFgDh4OrdAt P maxLen sOpkOrd opkOrd st advRoLog)))

/-- Active creation-order union bound for `badKeyIndFgAny4` on `runKeyIndFgSim1Key S P A.1` given
    the five active-count list-length bounds on `support (runKeyIndFgSim1Key S P A.1)`. -/
theorem prob_badKeyIndFgAny4_1Key_le_sum_ord_of_lengths
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hLen : ∀ x ∈ support (runKeyIndFgSim1Key S P A.1),
      x.2.2.base.principals.length ≤ activeIdCount S b.q_on ∧
      x.2.2.base.spkBundles.length ≤ activeSpkCount S b.q_on ∧
      x.2.2.base.opkEntries.length ≤ activeOpkCount S b.q_on ∧
      x.2.2.base.sessions.length ≤ activeSendCount S b.q_on ∧
      (opkSessions x.2.2.base).length ≤ activeSendOpkCount S b.q_on) :
    let n_id := activeIdCount S b.q_on
    let n_spk := activeSpkCount S b.q_on
    let n_opk := activeOpkCount S b.q_on
    let n_send := activeSendCount S b.q_on
    let n_send_opk := activeSendOpkCount S b.q_on
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      (∑ pOrd ∈ Finset.range n_id, ∑ spkOrd ∈ Finset.range n_spk,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal) +
      (∑ sOrd ∈ Finset.range n_send, ∑ spkOrd ∈ Finset.range n_spk,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal) +
      (∑ sOrd ∈ Finset.range n_send, ∑ pOrd ∈ Finset.range n_id,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal) +
      (∑ sOpkOrd ∈ Finset.range n_send_opk, ∑ opkOrd ∈ Finset.range n_opk,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal) := by
  dsimp only
  let mx := runKeyIndFgSim1Key S P A.1
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  have hMonoEnn :
      𝒟[mx >>= fun x => pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true} ≤
      𝒟[mx >>= fun x =>
        pure (badKeyIndFgOrdAny4 P b.q_ro n_id n_spk n_opk n_send n_send_opk
          x.2.2.base x.2.2.advRoLog)] {true} := by
    refine evalDist_bind_true_mono_of_support mx _ _ (fun x hx => ?_)
    cases hBad : badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog
    · simp
    · obtain ⟨hPrin, hSpk, hOpk, hSess, hSessOpk⟩ := hLen x hx
      have hEx := badKeyIndFgAny4_imp_exists_ord P b.q_ro n_id n_spk n_opk n_send n_send_opk
        x.2.2.base x.2.2.advRoLog hPrin hSpk hOpk hSess hSessOpk hBad
      have hOrd : badKeyIndFgOrdAny4 P b.q_ro n_id n_spk n_opk n_send n_send_opk
          x.2.2.base x.2.2.advRoLog = true := by
        unfold badKeyIndFgOrdAny4
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
        rcases hEx with h1 | h3 | h2 | h4
        · exact Or.inl (Or.inl (Or.inl h1))
        · exact Or.inl (Or.inl (Or.inr h3))
        · exact Or.inl (Or.inr h2)
        · exact Or.inr h4
      rw [hOrd]
  have hMono :
      (𝒟[mx >>= fun x => pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)]
        {true}).toReal ≤
      (𝒟[mx >>= fun x =>
        pure (badKeyIndFgOrdAny4 P b.q_ro n_id n_spk n_opk n_send n_send_opk
          x.2.2.base x.2.2.advRoLog)] {true}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hMonoEnn
  unfold badKeyIndFgOrdAny4 at hMono
  have hOr1 := prob_or_le_add_fg mx
    (fun x =>
      (((List.range n_id).any (fun pOrd =>
          (List.range n_spk).any (fun spkOrd =>
            badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog))) ||
        ((List.range n_send).any (fun sOrd =>
          (List.range n_spk).any (fun spkOrd =>
            badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)))) ||
      ((List.range n_send).any (fun sOrd =>
        (List.range n_id).any (fun pOrd =>
          badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog))))
    (fun x =>
      (List.range n_send_opk).any (fun sOpkOrd =>
        (List.range n_opk).any (fun opkOrd =>
          badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)))
  have hOr2 := prob_or_le_add_fg mx
    (fun x =>
      ((List.range n_id).any (fun pOrd =>
        (List.range n_spk).any (fun spkOrd =>
          badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog))) ||
      ((List.range n_send).any (fun sOrd =>
        (List.range n_spk).any (fun spkOrd =>
          badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog))))
    (fun x =>
      (List.range n_send).any (fun sOrd =>
        (List.range n_id).any (fun pOrd =>
          badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)))
  have hOr3 := prob_or_le_add_fg mx
    (fun x =>
      (List.range n_id).any (fun pOrd =>
        (List.range n_spk).any (fun spkOrd =>
          badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)))
    (fun x =>
      (List.range n_send).any (fun sOrd =>
        (List.range n_spk).any (fun spkOrd =>
          badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)))
  have h1 := toReal_any_double_range_le_sum2 mx n_id n_spk
    (fun pOrd spkOrd x => badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)
  have h3 := toReal_any_double_range_le_sum2 mx n_send n_spk
    (fun sOrd spkOrd x => badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)
  have h2 := toReal_any_double_range_le_sum2 mx n_send n_id
    (fun sOrd pOrd x => badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)
  have h4 := toReal_any_double_range_le_sum2 mx n_send_opk n_opk
    (fun sOpkOrd opkOrd x =>
      badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)
  linarith

/-! ## `KI1KeyActiveG3BoundStmt` combiners -/

theorem prob_badKeyIndFgAny4_1Key_le_gapDhWithSign_active_of_four_legs
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (hLen : ∀ x ∈ support (runKeyIndFgSim1Key S P A.1),
      x.2.2.base.principals.length ≤ activeIdCount S b.q_on ∧
      x.2.2.base.spkBundles.length ≤ activeSpkCount S b.q_on ∧
      x.2.2.base.opkEntries.length ≤ activeOpkCount S b.q_on ∧
      x.2.2.base.sessions.length ≤ activeSendCount S b.q_on ∧
      (opkSessions x.2.2.base).length ≤ activeSendOpkCount S b.q_on)
    (hDh1 : ∀ pOrd < activeIdCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
      (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A))
    (hDh3 : ∀ sOrd < activeSendCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
      (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A))
    (hDh2 : ∀ sOrd < activeSendCount S b.q_on, ∀ pOrd < activeIdCount S b.q_on,
      (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A))
    (hDh4 : ∀ sOpkOrd < activeSendOpkCount S b.q_on, ∀ opkOrd < activeOpkCount S b.q_on,
      (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A)) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      (fgActiveTotalIndexCount S b.q_on : ℝ) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdv4 S b A) := by
  have hUnion := prob_badKeyIndFgAny4_1Key_le_sum_ord_of_lengths S P b A hLen
  dsimp only at hUnion
  have hS1 :
      (∑ pOrd ∈ Finset.range (activeIdCount S b.q_on),
        ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
            pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
              {true}).toReal) ≤
      ∑ pOrd ∈ Finset.range (activeIdCount S b.q_on),
        ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A) :=
    Finset.sum_le_sum fun pOrd hp => Finset.sum_le_sum fun spkOrd hs =>
      hDh1 pOrd (Finset.mem_range.mp hp) spkOrd (Finset.mem_range.mp hs)
  have hS3 :
      (∑ sOrd ∈ Finset.range (activeSendCount S b.q_on),
        ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
            pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
              {true}).toReal) ≤
      ∑ sOrd ∈ Finset.range (activeSendCount S b.q_on),
        ∑ spkOrd ∈ Finset.range (activeSpkCount S b.q_on),
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A) :=
    Finset.sum_le_sum fun sOrd hs => Finset.sum_le_sum fun spkOrd hspk =>
      hDh3 sOrd (Finset.mem_range.mp hs) spkOrd (Finset.mem_range.mp hspk)
  have hS2 :
      (∑ sOrd ∈ Finset.range (activeSendCount S b.q_on),
        ∑ pOrd ∈ Finset.range (activeIdCount S b.q_on),
          (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
            pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
              {true}).toReal) ≤
      ∑ sOrd ∈ Finset.range (activeSendCount S b.q_on),
        ∑ pOrd ∈ Finset.range (activeIdCount S b.q_on),
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A) :=
    Finset.sum_le_sum fun sOrd hs => Finset.sum_le_sum fun pOrd hp =>
      hDh2 sOrd (Finset.mem_range.mp hs) pOrd (Finset.mem_range.mp hp)
  have hS4 :
      (∑ sOpkOrd ∈ Finset.range (activeSendOpkCount S b.q_on),
        ∑ opkOrd ∈ Finset.range (activeOpkCount S b.q_on),
          (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
            pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
              {true}).toReal) ≤
      ∑ sOpkOrd ∈ Finset.range (activeSendOpkCount S b.q_on),
        ∑ opkOrd ∈ Finset.range (activeOpkCount S b.q_on),
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A) :=
    Finset.sum_le_sum fun sOpkOrd hs => Finset.sum_le_sum fun opkOrd ho =>
      hDh4 sOpkOrd (Finset.mem_range.mp hs) opkOrd (Finset.mem_range.mp ho)
  have hAvg := sum_gapDhWithSign_fgKeyInd1KeyGapDhActiveAdv4_eq S P b A
  dsimp only at hAvg
  linarith

theorem ki1KeyActiveGapDhShallow_of_four_legs (S : Setup)
    (hLen : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ x ∈ support (runKeyIndFgSim1Key S P A.1),
        x.2.2.base.principals.length ≤ activeIdCount S b.q_on ∧
        x.2.2.base.spkBundles.length ≤ activeSpkCount S b.q_on ∧
        x.2.2.base.opkEntries.length ≤ activeOpkCount S b.q_on ∧
        x.2.2.base.sessions.length ≤ activeSendCount S b.q_on ∧
        (opkSessions x.2.2.base).length ≤ activeSendOpkCount S b.q_on)
    (hDh1 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ pOrd < activeIdCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A))
    (hDh3 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOrd < activeSendCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A))
    (hDh2 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOrd < activeSendCount S b.q_on, ∀ pOrd < activeIdCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A))
    (hDh4 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOpkOrd < activeSendOpkCount S b.q_on, ∀ opkOrd < activeOpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A)) :
    KI1KeyActiveG3BoundStmt S (fgKeyInd1KeyGapDhActiveAdv4 S) := by
  intro P hP δ hδ b A
  dsimp only
  rw [keyInd1KeyAdvG3_eq_keyIndAdvG3_1Key]
  have hC := keyIndAdvG3_1Key_le_prob_badKeyIndFgAny4_add_corr_1Key S P hP b A
  have hG := prob_badKeyIndFgAny4_1Key_le_gapDhWithSign_active_of_four_legs S P b A
    (hLen P hP b A) (hDh1 P hP b A) (hDh3 P hP b A) (hDh2 P hP b A) (hDh4 P hP b A)
  have hCorr := prob_hasBadKemCorrRecords_1Key_le S P δ hδ A.1
  have hTot :
      (fgActiveTotalIndexCount S b.q_on : ℝ) =
      (activeSpkCount S b.q_on : ℝ) *
        ((activeIdCount S b.q_on : ℝ) + (activeSendCount S b.q_on : ℝ)) +
      (activeIdCount S b.q_on : ℝ) * (activeSendCount S b.q_on : ℝ) +
      (activeOpkCount S b.q_on : ℝ) * (activeSendOpkCount S b.q_on : ℝ) := by
    unfold fgActiveTotalIndexCount
    push_cast
    ring
  have hTerm :
      2 * ((S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ) = kemDecapsFailureTermReal S δ := by
    unfold kemDecapsFailureTermReal
    ring
  rw [hTot] at hG
  linarith

/-- Establishes `KI1KeyActiveG3BoundStmt` for `(pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh` from
    active support length bounds and the four per-ordinal `GapDhWithSign` leg bounds. -/
theorem ki1KeyActiveGapDh_of_four_legs (S : Setup)
    (hLen : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ x ∈ support (runKeyIndFgSim1Key S P A.1),
        x.2.2.base.principals.length ≤ activeIdCount S b.q_on ∧
        x.2.2.base.spkBundles.length ≤ activeSpkCount S b.q_on ∧
        x.2.2.base.opkEntries.length ≤ activeOpkCount S b.q_on ∧
        x.2.2.base.sessions.length ≤ activeSendCount S b.q_on ∧
        (opkSessions x.2.2.base).length ≤ activeSendOpkCount S b.q_on)
    (hDh1 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ pOrd < activeIdCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A))
    (hDh3 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOrd < activeSendCount S b.q_on, ∀ spkOrd < activeSpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A))
    (hDh2 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOrd < activeSendCount S b.q_on, ∀ pOrd < activeIdCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A))
    (hDh4 : ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
      ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      ∀ sOpkOrd < activeSendOpkCount S b.q_on, ∀ opkOrd < activeOpkCount S b.q_on,
        (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
          pure (badKeyIndFgDh4OrdAt P b.q_ro sOpkOrd opkOrd x.2.2.base x.2.2.advRoLog)]
            {true}).toReal ≤
          GapDhWithSignReal P P.isValidDhTriple P.pow8
            (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpkOrd opkOrd S b A)) :
    KI1KeyActiveG3BoundStmt S (pqxdhKeyInd1KeyActiveCostedSims S).eval.gdh := by
  intro P hP δ hδ b A
  have hShallow :=
    ki1KeyActiveGapDhShallow_of_four_legs S hLen hDh1 hDh3 hDh2 hDh4 P hP δ hδ b A
  dsimp only at hShallow ⊢
  rw [gapDhWithSignReal_fgKeyInd1KeyGapDhActiveAtomicProg_eq]
  exact hShallow

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhUnion
