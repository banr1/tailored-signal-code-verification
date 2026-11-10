/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementComposed
public import Computational.Specifications.Session.StatementSession
import Computational.Proofs.SpecLemmas.Session.StatementComposed
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Clamped Per-Session Costed Reduction Combinators

**Checked by Lean.** Defines epoch-cap clamping (`qepClamp qep q = min qep (q + 4)`) for per-session
costed reduction bundles and families so AST literal sizes satisfy `SessionCostedReductionFamilyBounded`
unconditionally, and proves monotonicity of `sessionAdvantageBound` from `qepClamp qep q` to `qep`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedHalt

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoGames (Party)
open CryptoGames.CKA (DHFun)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Adversary admissibleLastLeakGuesses)
open CryptoGames.SM.Construction (healEpoch)
open CryptoGames.LibsignalSession
  (Crypto PublicKey IdentityKey SignalMessageProtoCodec maxForwardJumps GhostState)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C spuriousStepTerm)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem Bytes)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_mono)
open CryptoVerification.LibsignalSession
  (GRedBounded ratchetCostBudget Fig8CostedReds fig8CostedBounds FsCostedReds fsCostedBounds)
open CryptoVerification.E2E
  (idsOf SpkLeakRedProg SpkLeakRedUProg SpkSwapPrgHybridProg SpkSwapPrfHybridProg
   SpkCostedReds spkCostedBounds spkHopBudget spkLeakRedUBudget spkSwapHybridCount refineConst
   SessionCostedReductions sessionCostedReductionsBounded
   SessionCostedReductionFamily SessionCostedReductionFamilyBounded
   hiddenSaltMixtureBound fig8MixShortAuthV1 fig8MixShortPrivV1
   uniformStartMixtureBound sessionAdvantageBound)

local instance {Pt : Type} [Zero Pt] : Inhabited Pt := ⟨0⟩

/-! ## Epoch-cap clamping and budget monotonicity -/

/-- Clamped epoch cap `min qep (q + 4)`, bounding reachable party epochs in `q` queries. -/
@[expose] def qepClamp (qep q : ℕ) : ℕ :=
  min qep (q + 4)

@[simp] theorem qepClamp_le_qep (qep q : ℕ) : qepClamp qep q ≤ qep :=
  Nat.min_le_left qep (q + 4)

@[simp] theorem qepClamp_le_add (qep q : ℕ) : qepClamp qep q ≤ q + 4 :=
  Nat.min_le_right qep (q + 4)

theorem qepClamp_eq_qep_of_le {qep q : ℕ} (h : qep ≤ q + 4) :
    qepClamp qep q = qep :=
  Nat.min_eq_left h

@[simp] theorem qepClamp_idem (qep q : ℕ) :
    qepClamp (qepClamp qep q) q = qepClamp qep q :=
  qepClamp_eq_qep_of_le (qepClamp_le_add qep q)

theorem qepClamp_le_ratchetCostBudget (qep q : ℕ) :
    qepClamp qep q ≤ ratchetCostBudget q (qepClamp qep q) := by
  have h1 : qepClamp qep q ≤ q + 4 := qepClamp_le_add qep q
  have h2 : maxForwardJumps = 25000 := rfl
  unfold ratchetCostBudget
  have hsq : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (Nat.succ_pos q)
  nlinarith

theorem qepClamp_succ_le_ratchetCostBudget (qep q : ℕ) :
    qepClamp qep q + 1 ≤ ratchetCostBudget q (qepClamp qep q + 1) := by
  have h1 : qepClamp qep q ≤ q + 4 := qepClamp_le_add qep q
  have h2 : maxForwardJumps = 25000 := rfl
  unfold ratchetCostBudget
  have hsq : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (Nat.succ_pos q)
  nlinarith

theorem bits_mono_le {a b : ℕ} (h : a ≤ b) :
    ReductionDsl.bits a ≤ ReductionDsl.bits b :=
  bits_mono h

theorem ratchetCostBudget_mono_qep {q qep₁ qep₂ : ℕ} (h : qep₁ ≤ qep₂) :
    ratchetCostBudget q qep₁ ≤ ratchetCostBudget q qep₂ := by
  unfold ratchetCostBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (bits_mono_le h) _)

theorem ratchetCostBudget_qepClamp_le (q qep : ℕ) :
    ratchetCostBudget q (qepClamp qep q) ≤ ratchetCostBudget q qep :=
  ratchetCostBudget_mono_qep (qepClamp_le_qep qep q)

theorem ratchetCostBudget_qepClamp_succ_le (q qep : ℕ) :
    ratchetCostBudget q (qepClamp qep q + 1) ≤ ratchetCostBudget q (qep + 1) :=
  ratchetCostBudget_mono_qep (Nat.add_le_add_right (qepClamp_le_qep qep q) 1)

theorem gRedBounded_mono_budget
    {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ιT : Type} {T : OracleSpec ιT} {I : ReductionDsl.Iface S T}
    {ιS : Type} {Src : OracleSpec ιS} {C : ReductionDsl.GameCodec S Src}
    {In ShallowIn Out ShallowOut : ReductionDsl.Ty S}
    {R : ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ} {q qOut B₁ B₂ : ℕ}
    (hB : B₁ ≤ B₂)
    (h : GRedBounded R wTag wSamp q qOut B₁) :
    GRedBounded R wTag wSamp q qOut B₂ :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds R wTag wSamp q qOut B₂
    (h.1.trans hB)
    (h.2.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (bits_mono_le hB)) _))
    h.2.2.1
    h.2.2.2.1
    h.2.2.2.2.1

/-! ## Clamped sub-bundle lifting -/

theorem spkCostedBounds_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {q qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    {R : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam}
    (h : spkCostedBounds q qep₁ R) :
    spkCostedBounds q qep₂ R :=
  Computational.Proofs.SpecLemmas.Session.StatementComposed.spkCostedBounds_mono_qep hqep h

theorem fsCostedBounds_mono_qep {Pt : Type} [DecidableEq Pt]
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey}
    {qR qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    {R : FsCostedReds C codec ℓ encT idOf}
    (h : fsCostedBounds qR qep₁ R) :
    fsCostedBounds qR qep₂ R :=
  Computational.Proofs.SpecLemmas.Session.StatementComposed.fsCostedBounds_mono_qep hqep h

/-- Clamps the epoch-indexed families of a `Fig8CostedReds` bundle above `qep_c` to parameter-free dummy reductions. -/
@[expose] def clampFig8CostedReds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    (qep_c : ℕ)
    (base dummy : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam) :
    Fig8CostedReds Dh encPt C codec ℓ encT idOf lam where
  challSim := base.challSim
  privRedB := fun i => if i < qep_c + 1 then base.privRedB i else dummy.privRedB i
  redCKAAuth := fun tL t => if t < qep_c + 2 then base.redCKAAuth tL t else dummy.redCKAAuth tL t
  redPRNGAuth := fun tL t => if t < qep_c + 2 then base.redPRNGAuth tL t else dummy.redPRNGAuth tL t
  redFSAuth := fun j tL t => if t < qep_c + 2 then base.redFSAuth j tL t else dummy.redFSAuth j tL t
  redCKAPriv := fun tL i => if i < qep_c + 1 then base.redCKAPriv tL i else dummy.redCKAPriv tL i
  redPRNGPriv := fun tL i => if i < qep_c + 1 then base.redPRNGPriv tL i else dummy.redPRNGPriv tL i
  redFSPriv := fun tL i => if i < qep_c + 1 then base.redFSPriv tL i else dummy.redFSPriv tL i
  redFSPrivCoin := fun tL i =>
    if i < qep_c + 1 then base.redFSPrivCoin tL i else dummy.redFSPrivCoin tL i

@[simp] theorem clampFig8CostedReds_challSim {Pt : Type} [DecidableEq Pt] [Zero Pt]
    [SampleableType Pt] {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    (qep_c : ℕ) (base dummy : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam) :
    (clampFig8CostedReds qep_c base dummy).challSim = base.challSim := rfl

theorem clampFig8CostedReds_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → List (BitVec 8)}
    {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {q qep_c qep : ℕ} (hqep : qep_c ≤ qep)
    {base dummy : Fig8CostedReds Dh encPt C codec ℓ encT idOf lam}
    (hbase : fig8CostedBounds q qep_c base)
    (hdummy : fig8CostedBounds q qep dummy) :
    fig8CostedBounds q qep (clampFig8CostedReds qep_c base dummy) := by
  rcases hbase with ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9,
    hb10, hb11, hb12, hb13, hb14, hb15, hb16⟩
  rcases hdummy with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16⟩
  have hB := ratchetCostBudget_mono_qep (q := q) hqep
  refine ⟨gRedBounded_mono_budget hB hb1,
    fun i hi => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb2 i h)
      · exact hd2 i hi,
    fun t ht tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb3 t h tL htL)
      · exact hd3 t ht tL htL,
    fun t ht tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb4 t h tL htL)
      · exact hd4 t ht tL htL,
    fun t ht tL htL j hj => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb5 t h tL htL j hj)
      · exact hd5 t ht tL htL j hj,
    fun i hi tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb6 i h tL htL)
      · exact hd6 i hi tL htL,
    fun i hi tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb7 i h tL htL)
      · exact hd7 i hi tL htL,
    fun i hi tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb8 i h tL htL)
      · exact hd8 i hi tL htL,
    fun i hi tL htL => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact gRedBounded_mono_budget hB (hb9 i h tL htL)
      · exact hd9 i hi tL htL,
    fun t ht tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb10 t h tL htL A hA
      · exact hd10 t ht tL htL A hA,
    fun i hi tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb11 i h tL htL A hA
      · exact hd11 i hi tL htL A hA,
    fun t ht tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb12 t h tL htL A hA
      · exact hd12 t ht tL htL A hA,
    fun i hi tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact OracleComp.IsQueryBoundP.mono (hb13 i h tL htL A hA) (by omega)
      · exact hd13 i hi tL htL A hA,
    fun t ht tL htL j hj A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb14 t h tL htL j hj A hA
      · exact hd14 t ht tL htL j hj A hA,
    fun i hi tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb15 i h tL htL A hA
      · exact hd15 i hi tL htL A hA,
    fun i hi tL htL A hA => by
      dsimp only [clampFig8CostedReds]; split_ifs with h
      · exact hb16 i h tL htL A hA
      · exact hd16 i hi tL htL A hA⟩

@[expose] def clampDFRed
    {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ιT : Type} {T : OracleSpec ιT} {I : ReductionDsl.Iface S T}
    {ιS : Type} {Src : OracleSpec ιS} {C : ReductionDsl.GameCodec S Src}
    {In ShallowIn Out ShallowOut : ReductionDsl.Ty S}
    (qep_c : ℕ)
    (base : Option ℕ → ℕ → ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut)
    (dummy : ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut)
    (tL : Option ℕ) (t : ℕ) :
    ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut :=
  if t < qep_c + 2 then base tL t else dummy

theorem clampDFRed_gRedBounded
    {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ιT : Type} {T : OracleSpec ιT} {I : ReductionDsl.Iface S T}
    {ιS : Type} {Src : OracleSpec ιS} {C : ReductionDsl.GameCodec S Src}
    {In ShallowIn Out ShallowOut : ReductionDsl.Ty S}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut qep_c qep : ℕ} (hqep : qep_c ≤ qep)
    {base : Option ℕ → ℕ → ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut}
    {dummy : ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut}
    (hbase : ∀ t < qep_c + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      GRedBounded (base tL t) wTag wSamp q qOut (ratchetCostBudget q qep_c))
    (hdummy : GRedBounded dummy wTag wSamp q qOut (ratchetCostBudget q qep)) :
    ∀ t < qep + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t,
      GRedBounded (clampDFRed qep_c base dummy tL t) wTag wSamp q qOut (ratchetCostBudget q qep) := by
  have hB := ratchetCostBudget_mono_qep (q := q) hqep
  intro t _ht tL htL
  unfold clampDFRed
  split_ifs with hlt
  · exact gRedBounded_mono_budget hB (hbase t hlt tL htL)
  · exact hdummy

@[expose] def clampDFFsRed
    {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ιT : Type} {T : OracleSpec ιT} {I : ReductionDsl.Iface S T}
    {ιS : Type} {Src : OracleSpec ιS} {C : ReductionDsl.GameCodec S Src}
    {In ShallowIn Out ShallowOut : ReductionDsl.Ty S}
    (qep_c : ℕ)
    (base : ℕ → Option ℕ → ℕ → ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut)
    (dummy : ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut)
    (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut :=
  if t < qep_c + 2 then base j tL t else dummy

theorem clampDFFsRed_gRedBounded
    {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S}
    {ιT : Type} {T : OracleSpec ιT} {I : ReductionDsl.Iface S T}
    {ιS : Type} {Src : OracleSpec ιS} {C : ReductionDsl.GameCodec S Src}
    {In ShallowIn Out ShallowOut : ReductionDsl.Ty S}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut qep_c qep : ℕ} (hqep : qep_c ≤ qep)
    {base : ℕ → Option ℕ → ℕ → ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut}
    {dummy : ReductionDsl.CostedReduction O I Src C In ShallowIn Out ShallowOut}
    (hbase : ∀ t < qep_c + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t, ∀ j < q,
      GRedBounded (base j tL t) wTag wSamp q qOut (ratchetCostBudget q qep_c))
    (hdummy : GRedBounded dummy wTag wSamp q qOut (ratchetCostBudget q qep)) :
    ∀ t < qep + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t, ∀ j < q,
      GRedBounded (clampDFFsRed qep_c base dummy j tL t) wTag wSamp q qOut
        (ratchetCostBudget q qep) := by
  have hB := ratchetCostBudget_mono_qep (q := q) hqep
  intro t _ht tL htL j hj
  unfold clampDFFsRed
  split_ifs with hlt
  · exact gRedBounded_mono_budget hB (hbase t hlt tL htL j hj)
  · exact hdummy

/-! ## Program abbreviations -/

abbrev SimFig8RedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.fig8SmIface ℓ Pt)
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt) .unit .unit .bool .bool

abbrev SimDFRedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.fig8SmIfaceDF ℓ Pt)
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt) .unit .unit .bool .bool

abbrev SessionCoinOnlyRedProg (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : MlKem) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
    (ReductionDsl.coinOnlyIface ℓ Pt)
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (ReductionDsl.e2eSessionCodec ℓ Pt)
    (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .bool

abbrev Fig8DFRedProg (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {T : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) T) :=
  ReductionDsl.CostedReduction
    (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
    I
    (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (ReductionDsl.fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool

/-! ## Advantage bound monotonicity -/

theorem spuriousStepTerm_mono_qep {Pt : Type}
    (F : CryptoGames.HMAC.ShaState → List (BitVec 8) → CryptoGames.HMAC.ShaState)
    (encPt : Pt → List (BitVec 8)) (Dh : DHFun (BitVec 256) Pt) (q : ℕ)
    {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) :
    spuriousStepTerm F encPt Dh q qep₁ ≤ spuriousStepTerm F encPt Dh q qep₂ := by
  unfold spuriousStepTerm
  gcongr

theorem refineConst_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (Z : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (q : ℕ) (δ : ℝ≥0∞)
    {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂) :
    refineConst Z Dh encPt q qep₁ δ ≤ refineConst Z Dh encPt q qep₂ δ := by
  unfold refineConst
  have hsp := spuriousStepTerm_mono_qep Z.F encPt Dh q hqep
  have h1 : (qep₁ : ℝ≥0∞) ≤ (qep₂ : ℝ≥0∞) := Nat.cast_le.mpr hqep
  gcongr

theorem hiddenSaltMixtureBound_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep₁ q δ oa ida idb R A ≤
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep₂ q δ oa ida idb R A := by
  unfold hiddenSaltMixtureBound
  have hsum :
      ∀ f : ℕ → ℝ≥0∞,
        ∑ t ∈ Finset.range ((qep₁ + 1) + 2), f t ≤
          ∑ t ∈ Finset.range ((qep₂ + 1) + 2), f t := fun f =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hsp := spuriousStepTerm_mono_qep Z.F encPt Dh q hqep
  have h1 : (qep₁ : ℝ≥0∞) ≤ (qep₂ : ℝ≥0∞) := Nat.cast_le.mpr hqep
  refine add_le_add (add_le_add (hsum _) hsp) ?_
  gcongr

theorem fig8MixShortAuthV1_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep₁ q oa ida idb R A ≤
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep₂ q oa ida idb R A := by
  unfold fig8MixShortAuthV1
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    zero_le

theorem fig8MixShortPrivV1_mono_qep {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep₁ q oa ida idb R A ≤
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep₂ q oa ida idb R A := by
  unfold fig8MixShortPrivV1
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    zero_le

theorem uniformStartMixtureBound_mono_qep
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep₁ qep₂ : ℕ} (hqep : qep₁ ≤ qep₂)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep₁ q δ oa ida idb R A ≤
      uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep₂ q δ oa ida idb R A := by
  unfold uniformStartMixtureBound
  have hauth := fig8MixShortAuthV1_mono_qep Z K ℓ Dh encPt encT decT lam hqep q oa ida idb R
    (fun o => CryptoVerification.E2E.RefuseB0.refuseCorrB0 (A o))
  have hpriv := fig8MixShortPrivV1_mono_qep Z K ℓ Dh encPt encT decT lam hqep q oa ida idb R
    (fun o => CryptoVerification.E2E.RefuseB0.refuseCorrB0 (A o))
  have href := refineConst_mono_qep Z Dh encPt q δ hqep
  have hhs := hiddenSaltMixtureBound_mono_qep Z K ℓ Dh encPt encT decT lam hqep q δ oa ida idb R
    (fun o => CryptoVerification.E2E.RefuseB0.refuseCorrB0 (A o))
  gcongr

/-- Bounds `sessionAdvantageBound` at `qepClamp qep q` by `sessionAdvantageBound` at `qep` for clamp-invariant families. -/
theorem sessionAdvantageBound_qepClamp_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hD_eq : ∀ o,
      D C K (ida o) (idb o) Dh encPt encT decT 0 (qepClamp qep q) q =
        D C K (ida o) (idb o) Dh encPt encT decT 0 qep q) :
    sessionAdvantageBound ℓ D C K Dh encPt encT decT (qepClamp qep q) q δ oa ida idb s A ≤
      sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A := by
  unfold sessionAdvantageBound
  dsimp only
  simp only [hD_eq]
  have hu := uniformStartMixtureBound_mono_qep C K ℓ Dh encPt encT decT (0 : Pt)
    (qepClamp_le_qep qep q) q δ oa ida idb
    (fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 qep q) A
  gcongr

/-! ## Dummy witnesses and halted family constructors -/

@[expose] def dummyFig8SmRed {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {T : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) T) :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      I
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ReductionDsl.fig8SmCodec ℓ Pt) .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle := .ret (.pair (.inl .none) .unit)
  finish := .ret (.bool false)

theorem dummyFig8SmRed_gRedBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {T : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) T)
    (hu : I.uCost = 1)
    (hsmp : I.smp = ReductionDsl.atomicSamplers ℓ Pt)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q qOut qep : ℕ) :
    GRedBounded (dummyFig8SmRed ℓ C Dh encPt encT lam I) wTag wSamp q qOut
      (ratchetCostBudget q qep) := by
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds _ wTag wSamp q qOut
    (ratchetCostBudget q qep) ?_ ?_ ?_
    (ReductionDsl.atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (hsmp ▸ ReductionDsl.atomicSamplers_sizeHonest ℓ Pt)
  · have hcost :
        (dummyFig8SmRed ℓ C Dh encPt encT lam I).totalCost q = 4 + q * 37 + 2 := by
      simp [dummyFig8SmRed, ReductionDsl.CostedReduction.totalCost,
        ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, hu]
    rw [hcost]
    have hmj : maxForwardJumps = 25000 := rfl
    unfold ratchetCostBudget
    have hsq : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (Nat.succ_pos q)
    nlinarith
  · have hsize : (dummyFig8SmRed ℓ C Dh encPt encT lam I).size = 11 := rfl
    rw [hsize]
    have hrb : ReductionDsl.reductionSizeBudget = 2 ^ 24 := rfl
    omega
  · simp [dummyFig8SmRed, ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries]

@[expose] def dummyFig8SmDFRed {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {T : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) T) :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      I
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ReductionDsl.fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool where
  σ := .unit
  init := .ret (.pair .unit .unit)
  handle := .ret (.pair (.inl .none) .unit)
  finish := .ret (.bool false)

theorem dummyFig8SmDFRed_gRedBounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {T : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) T)
    (hu : I.uCost = 1)
    (hsmp : I.smp = ReductionDsl.atomicSamplers ℓ Pt)
    (wTag : I.Tag → ℕ) (wSamp : I.smp.Samp → ℕ) (q qOut qep : ℕ) :
    GRedBounded (dummyFig8SmDFRed ℓ C Dh encPt encT lam I) wTag wSamp q qOut
      (ratchetCostBudget q qep) := by
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds _ wTag wSamp q qOut
    (ratchetCostBudget q qep) ?_ ?_ ?_
    (ReductionDsl.atomicFig8Ops_sizeHonest ℓ Pt C Dh encPt encT lam)
    (hsmp ▸ ReductionDsl.atomicSamplers_sizeHonest ℓ Pt)
  · have hcost :
        (dummyFig8SmDFRed ℓ C Dh encPt encT lam I).totalCost q = 4 + q * 37 + 2 := by
      simp [dummyFig8SmDFRed, ReductionDsl.CostedReduction.totalCost,
        ReductionDsl.Comp.cost, ReductionDsl.Expr.cost, hu]
    rw [hcost]
    have hmj : maxForwardJumps = 25000 := rfl
    unfold ratchetCostBudget
    have hsq : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow 2 (q + 1) (Nat.succ_pos q)
    nlinarith
  · have hsize : (dummyFig8SmDFRed ℓ C Dh encPt encT lam I).size = 11 := rfl
    rw [hsize]
    have hrb : ReductionDsl.reductionSizeBudget = 2 ^ 24 := rfl
    omega
  · simp [dummyFig8SmDFRed, ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries]

@[expose] def dummyFig8CostedReds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) :
    Fig8CostedReds Dh encPt C codec ℓ encT idOf lam where
  challSim := dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.fig8SmIface ℓ Pt)
  privRedB := fun _ => dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.fig8SmIface ℓ Pt)
  redCKAAuth := fun _ _ => dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.ckaTargetIface ℓ Pt)
  redPRNGAuth := fun _ _ => dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.prngTargetIface ℓ Pt)
  redFSAuth := fun _ _ _ =>
    dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.fsaeadHeaderIface ℓ Pt)
  redCKAPriv := fun _ _ => dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.ckaTargetIface ℓ Pt)
  redPRNGPriv := fun _ _ => dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.prngTargetIface ℓ Pt)
  redFSPriv := fun _ _ =>
    dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.fsaeadHeaderIface ℓ Pt)
  redFSPrivCoin := fun _ _ =>
    dummyFig8SmRed ℓ C Dh encPt encT lam (ReductionDsl.fsaeadHeaderIface ℓ Pt)

private theorem dummyFig8SmRed_queryBound {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {G : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) (unifSpec + G))
    (hfwd : ∀ n, I.fwdU n = query (spec := unifSpec + G) (.inl n))
    {P : (unifSpec + G).Domain → Prop} [DecidablePred P] (hP : ∀ n, ¬ P (.inl n))
    (A : CryptoGames.LibsignalSM.Fig8Adv Pt ℓ) {q m : ℕ}
    (hA : CryptoGames.SM.MakesAtMostQueries A q) :
    ((dummyFig8SmRed ℓ C Dh encPt encT lam I).eval (fun _ => A) ()).IsQueryBoundP P m := by
  have hAg : A.IsQueryBoundP
      (ReductionDsl.isGameQuery
        (G := CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt))) q := by
    unfold CryptoGames.SM.MakesAtMostQueries at hA
    convert hA using 1
    funext x; cases x <;> simp [ReductionDsl.isGameQuery]
  have hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0 := fun n => by
    rw [hfwd n]; simp [OracleComp.isQueryBoundP_query_iff, hP n]
  have h0 := ReductionDsl.CostedReduction.queryBound_eval
    (dummyFig8SmRed ℓ C Dh encPt encT lam I) P
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) hU (fun _ => A) q (fun _ => hAg) ()
  have htq :
      (dummyFig8SmRed ℓ C Dh encPt encT lam I).totalQueries (fun _ => 1) (fun _ => 0) q = 0 := by
    simp [dummyFig8SmRed, ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries]
  exact (htq ▸ h0).mono (Nat.zero_le m)

private theorem dummyFig8SmDFRed_queryBound {Pt : Type} [DecidableEq Pt] [Zero Pt]
    (ℓ : ℕ) (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → Bytes) (encT : Pt → PublicKey) (lam : Pt)
    {ιT : Type} {G : OracleSpec ιT}
    (I : ReductionDsl.Iface (ReductionDsl.atomicSig ℓ Pt) (unifSpec + G))
    (hfwd : ∀ n, I.fwdU n = query (spec := unifSpec + G) (.inl n))
    {P : (unifSpec + G).Domain → Prop} [DecidablePred P] (hP : ∀ n, ¬ P (.inl n))
    (A : OracleComp
      (unifSpec + CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) (Fig8C Pt)) Bool)
    {q : ℕ}
    {pA : (unifSpec + CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain → Prop}
    [DecidablePred pA]
    (hpA : ∀ x, pA x ↔
      ReductionDsl.isGameQuery
        (G := CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt)) x)
    (hA : A.IsQueryBoundP pA q) {m : ℕ} :
    ((dummyFig8SmDFRed ℓ C Dh encPt encT lam I).eval (fun _ => A) ()).IsQueryBoundP P m := by
  have hAg : A.IsQueryBoundP
      (ReductionDsl.isGameQuery
        (G := CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) (Fig8C Pt))) q := by
    convert hA using 1
    funext x; exact propext (hpA x).symm
  have hU : ∀ n, (I.fwdU n).IsQueryBoundP P 0 := fun n => by
    rw [hfwd n]; simp [OracleComp.isQueryBoundP_query_iff, hP n]
  have h0 := ReductionDsl.CostedReduction.queryBound_eval
    (dummyFig8SmDFRed ℓ C Dh encPt encT lam I) P
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) hU (fun _ => A) q (fun _ => hAg) ()
  have htq :
      (dummyFig8SmDFRed ℓ C Dh encPt encT lam I).totalQueries (fun _ => 1) (fun _ => 0) q = 0 := by
    simp [dummyFig8SmDFRed, ReductionDsl.CostedReduction.totalQueries, ReductionDsl.Comp.queries]
  exact (htq ▸ h0).mono (Nat.zero_le m)

theorem dummyFig8CostedReds_bounds {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (q qep : ℕ) :
    fig8CostedBounds q qep (dummyFig8CostedReds Dh encPt C codec ℓ encT idOf lam) := by
  dsimp only [fig8CostedBounds, dummyFig8CostedReds, CryptoGames.CKA.MakesAtMostQueries,
    CryptoGames.PRFPRNG.MakesAtMostQueries, CryptoGames.FSAEAD.MakesAtMostQueries]
  exact ⟨dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q q qep,
    fun _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q q qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 + 2 * q) qep,
    fun _ _ _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 + 2 * q) qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) qep,
    fun _ _ _ _ => dummyFig8SmRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) qep,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA,
    fun _ _ _ _ A hA =>
      dummyFig8SmRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl) (fun _ => by rintro ⟨⟩) A hA⟩

@[expose] def clampSessionCostedReductions {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    (qep_c : ℕ)
    (base : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) :
    SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam where
  spk := base.spk
  fig8 := clampFig8CostedReds (qep_c + 1) base.fig8
    (dummyFig8CostedReds Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam)
  fs := base.fs
  simFig8 := base.simFig8
  simDeliverForge := base.simDeliverForge
  epoch0Red := base.epoch0Red
  uniformStartRed := base.uniformStartRed
  challSimDF := base.challSimDF
  B_cka := clampDFRed (qep_c + 1) base.B_cka
    (dummyFig8SmDFRed ℓ C Dh encPt encT lam (ReductionDsl.ckaTargetIface ℓ Pt))
  B_prng := clampDFRed (qep_c + 1) base.B_prng
    (dummyFig8SmDFRed ℓ C Dh encPt encT lam (ReductionDsl.prngTargetIface ℓ Pt))
  B_fs := clampDFFsRed (qep_c + 1) base.B_fs
    (dummyFig8SmDFRed ℓ C Dh encPt encT lam (ReductionDsl.fsaeadHeaderIface ℓ Pt))

section ClampSessionProjections

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
  (qep_c : ℕ) (base : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam)

@[simp] theorem clampSessionCostedReductions_spk :
    (clampSessionCostedReductions qep_c base).spk = base.spk := rfl
@[simp] theorem clampSessionCostedReductions_fs :
    (clampSessionCostedReductions qep_c base).fs = base.fs := rfl
@[simp] theorem clampSessionCostedReductions_simFig8 :
    (clampSessionCostedReductions qep_c base).simFig8 = base.simFig8 := rfl
@[simp] theorem clampSessionCostedReductions_simDeliverForge :
    (clampSessionCostedReductions qep_c base).simDeliverForge = base.simDeliverForge := rfl
@[simp] theorem clampSessionCostedReductions_epoch0Red :
    (clampSessionCostedReductions qep_c base).epoch0Red = base.epoch0Red := rfl
@[simp] theorem clampSessionCostedReductions_uniformStartRed :
    (clampSessionCostedReductions qep_c base).uniformStartRed = base.uniformStartRed := rfl
@[simp] theorem clampSessionCostedReductions_challSimDF :
    (clampSessionCostedReductions qep_c base).challSimDF = base.challSimDF := rfl
@[simp] theorem clampSessionCostedReductions_B_cka_of_lt {t : ℕ} (ht : t < (qep_c + 1) + 2)
    (tL : Option ℕ) : (clampSessionCostedReductions qep_c base).B_cka tL t = base.B_cka tL t := by
  simp [clampSessionCostedReductions, clampDFRed, ht]
@[simp] theorem clampSessionCostedReductions_B_prng_of_lt {t : ℕ} (ht : t < (qep_c + 1) + 2)
    (tL : Option ℕ) : (clampSessionCostedReductions qep_c base).B_prng tL t = base.B_prng tL t := by
  simp [clampSessionCostedReductions, clampDFRed, ht]
@[simp] theorem clampSessionCostedReductions_B_fs_of_lt {t : ℕ} (ht : t < (qep_c + 1) + 2)
    (j : ℕ) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).B_fs j tL t = base.B_fs j tL t := by
  simp [clampSessionCostedReductions, clampDFFsRed, ht]
@[simp] theorem clampSessionCostedReductions_fig8_challSim :
    (clampSessionCostedReductions qep_c base).fig8.challSim = base.fig8.challSim := rfl
@[simp] theorem clampSessionCostedReductions_fig8_privRedB_of_lt {i : ℕ}
    (hi : i < (qep_c + 1) + 1) :
    (clampSessionCostedReductions qep_c base).fig8.privRedB i = base.fig8.privRedB i := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redCKAAuth_of_lt {t : ℕ}
    (ht : t < (qep_c + 1) + 2) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redCKAAuth tL t = base.fig8.redCKAAuth tL t := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redPRNGAuth_of_lt {t : ℕ}
    (ht : t < (qep_c + 1) + 2) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redPRNGAuth tL t =
      base.fig8.redPRNGAuth tL t := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redFSAuth_of_lt {t : ℕ}
    (ht : t < (qep_c + 1) + 2) (j : ℕ) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redFSAuth j tL t =
      base.fig8.redFSAuth j tL t := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redCKAPriv_of_lt {i : ℕ}
    (hi : i < (qep_c + 1) + 1) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redCKAPriv tL i = base.fig8.redCKAPriv tL i := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redPRNGPriv_of_lt {i : ℕ}
    (hi : i < (qep_c + 1) + 1) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redPRNGPriv tL i =
      base.fig8.redPRNGPriv tL i := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redFSPriv_of_lt {i : ℕ}
    (hi : i < (qep_c + 1) + 1) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redFSPriv tL i = base.fig8.redFSPriv tL i := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl
@[simp] theorem clampSessionCostedReductions_fig8_redFSPrivCoin_of_lt {i : ℕ}
    (hi : i < (qep_c + 1) + 1) (tL : Option ℕ) :
    (clampSessionCostedReductions qep_c base).fig8.redFSPrivCoin tL i =
      base.fig8.redFSPrivCoin tL i := by
  dsimp only [clampSessionCostedReductions, clampFig8CostedReds]; split_ifs; rfl

end ClampSessionProjections

theorem clampSessionCostedReductions_bounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {ℓ : ℕ} {C : Crypto} {K : MlKem} {idA idB : IdentityKey}
    {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {qep_c qep q : ℕ} (hqep : qep_c ≤ qep)
    {base : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam}
    (hbase : sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep_c q base) :
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (clampSessionCostedReductions qep_c base) := by
  rcases hbase with ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13⟩
  have hle_succ : qep_c + 1 ≤ qep + 1 := Nat.add_le_add_right hqep 1
  have hB_succ : ratchetCostBudget q (qep_c + 1) ≤ ratchetCostBudget q (qep + 1) :=
    ratchetCostBudget_mono_qep (q := q) hle_succ
  refine ⟨spkCostedBounds_mono_qep hqep hb1,
    clampFig8CostedReds_bounds hle_succ hb2
      (dummyFig8CostedReds_bounds Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam
        q (qep + 1)),
    fsCostedBounds_mono_qep hle_succ hb3,
    gRedBounded_mono_budget hB_succ hb4,
    gRedBounded_mono_budget hB_succ hb5,
    gRedBounded_mono_budget hB_succ hb6,
    gRedBounded_mono_budget hB_succ hb7,
    gRedBounded_mono_budget hB_succ hb8,
    clampDFRed_gRedBounded hle_succ hb9
      (dummyFig8SmDFRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 + 2 * q) (qep + 1)),
    clampDFRed_gRedBounded hle_succ hb10
      (dummyFig8SmDFRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 + 2 * q) (qep + 1)),
    clampDFFsRed_gRedBounded hle_succ hb11
      (dummyFig8SmDFRed_gRedBounded ℓ C Dh encPt encT lam _ rfl rfl _ _ q (2 * q) (qep + 1)),
    ?_, ?_⟩
  · intro t _ht tL htL A hA
    by_cases hlt : t < (qep_c + 1) + 2
    · rw [clampSessionCostedReductions_B_prng_of_lt qep_c base hlt tL]
      exact hb12 t hlt tL htL A hA
    · simp only [clampSessionCostedReductions, clampDFRed, hlt, ↓reduceIte,
        CryptoGames.PRFPRNG.MakesAtMostQueries]
      exact dummyFig8SmDFRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl)
        (fun _ => by rintro ⟨⟩) A (by rintro (_ | _) <;> simp [ReductionDsl.isGameQuery]) hA
  · intro t _ht tL htL j hj A hA
    by_cases hlt : t < (qep_c + 1) + 2
    · rw [clampSessionCostedReductions_B_fs_of_lt qep_c base hlt j tL]
      exact hb13 t hlt tL htL j hj A hA
    · simp only [clampSessionCostedReductions, clampDFFsRed, hlt, ↓reduceIte,
        CryptoGames.FSAEAD.MakesAtMostQueries]
      exact dummyFig8SmDFRed_queryBound ℓ C Dh encPt encT lam _ (fun _ => rfl)
        (fun _ => by rintro ⟨⟩) A (by rintro (_ | _) <;> simp [ReductionDsl.isGameQuery]) hA

/-- Clamps a `SessionCostedReductionFamily` to `qepClamp qep q` above `q + 4`. -/
@[expose] def clampSessionCostedReductionFamily {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ) : SessionCostedReductionFamily Pt ℓ :=
  fun C K idA idB Dh encPt encT decT lam qep q =>
    if qep ≤ q + 4 then
      D C K idA idB Dh encPt encT decT lam qep q
    else
      clampSessionCostedReductions (q + 4)
        (D C K idA idB Dh encPt encT decT lam (q + 4) q)

@[simp] theorem clampSessionCostedReductionFamily_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {qep q : ℕ} (hqep : qep ≤ q + 4) :
    clampSessionCostedReductionFamily ℓ D C K idA idB Dh encPt encT decT lam qep q =
      D C K idA idB Dh encPt encT decT lam qep q := by
  simp [clampSessionCostedReductionFamily, hqep]

theorem clampSessionCostedReductionFamily_of_gt
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt)
    {qep q : ℕ} (hqep : q + 4 < qep) :
    clampSessionCostedReductionFamily ℓ D C K idA idB Dh encPt encT decT lam qep q =
      clampSessionCostedReductions (q + 4) (D C K idA idB Dh encPt encT decT lam (q + 4) q) := by
  simp [clampSessionCostedReductionFamily, Nat.not_le.mpr hqep]

theorem clampSessionCostedReductionFamily_bounded
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (hD : ∀ C K idA idB Dh encPt encT decT lam qep q,
      qep ≤ q + 4 →
        sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
          (D C K idA idB Dh encPt encT decT lam qep q)) :
    SessionCostedReductionFamilyBounded ℓ (clampSessionCostedReductionFamily ℓ D) := by
  intro C K idA idB Dh encPt encT decT lam qep q
  by_cases hqep : qep ≤ q + 4
  · rw [clampSessionCostedReductionFamily_of_le ℓ D C K idA idB Dh encPt encT decT lam hqep]
    exact hD C K idA idB Dh encPt encT decT lam qep q hqep
  · rw [clampSessionCostedReductionFamily_of_gt ℓ D C K idA idB Dh encPt encT decT lam
      (Nat.lt_of_not_ge hqep)]
    exact clampSessionCostedReductions_bounded (Nat.le_of_not_ge hqep)
      (hD C K idA idB Dh encPt encT decT lam (q + 4) q le_rfl)

theorem fig8MixShortAuthV1_congr
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R₁ R₂ : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hfs : ∀ o, (R₁ o).fs = (R₂ o).fs)
    (hsim : ∀ o, (R₁ o).simFig8 = (R₂ o).simFig8)
    (hchall : ∀ o, (R₁ o).fig8.challSim = (R₂ o).fig8.challSim)
    (hcka : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ tL,
      (R₁ o).fig8.redCKAAuth tL t = (R₂ o).fig8.redCKAAuth tL t)
    (hprng : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ tL,
      (R₁ o).fig8.redPRNGAuth tL t = (R₂ o).fig8.redPRNGAuth tL t)
    (hfsa : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ j tL,
      (R₁ o).fig8.redFSAuth j tL t = (R₂ o).fig8.redFSAuth j tL t) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R₁ A =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R₂ A := by
  unfold fig8MixShortAuthV1
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun t ht => ?_)
  have hlt : t < (qep + 1) + 2 := Finset.mem_range.mp ht
  simp only [hfs, hsim, hchall, fun o tL => hcka o hlt tL, fun o tL => hprng o hlt tL,
    fun o j tL => hfsa o hlt j tL]

theorem fig8MixShortPrivV1_congr
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R₁ R₂ : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hfs : ∀ o, (R₁ o).fs = (R₂ o).fs)
    (hsim : ∀ o, (R₁ o).simFig8 = (R₂ o).simFig8)
    (hprivB : ∀ o {i : ℕ}, i < (qep + 1) + 1 →
      (R₁ o).fig8.privRedB i = (R₂ o).fig8.privRedB i)
    (hcka : ∀ o {i : ℕ}, i < (qep + 1) + 1 → ∀ tL,
      (R₁ o).fig8.redCKAPriv tL i = (R₂ o).fig8.redCKAPriv tL i)
    (hprng : ∀ o {i : ℕ}, i < (qep + 1) + 1 → ∀ tL,
      (R₁ o).fig8.redPRNGPriv tL i = (R₂ o).fig8.redPRNGPriv tL i)
    (hfsp : ∀ o {i : ℕ}, i < (qep + 1) + 1 → ∀ tL,
      (R₁ o).fig8.redFSPriv tL i = (R₂ o).fig8.redFSPriv tL i)
    (hfspc : ∀ o {i : ℕ}, i < (qep + 1) + 1 → ∀ tL,
      (R₁ o).fig8.redFSPrivCoin tL i = (R₂ o).fig8.redFSPrivCoin tL i) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R₁ A =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R₂ A := by
  unfold fig8MixShortPrivV1
  refine congrArg (2 * ·) (Finset.sum_congr rfl fun i hi => ?_)
  have hlt : i < (qep + 1) + 1 := Finset.mem_range.mp hi
  simp only [hfs, hsim, fun o => hprivB o hlt, fun o tL => hcka o hlt tL,
    fun o tL => hprng o hlt tL, fun o tL => hfsp o hlt tL, fun o tL => hfspc o hlt tL]

theorem hiddenSaltMixtureBound_congr
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R₁ R₂ : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (hfs : ∀ o, (R₁ o).fs = (R₂ o).fs)
    (hsimDF : ∀ o, (R₁ o).simDeliverForge = (R₂ o).simDeliverForge)
    (hchallDF : ∀ o, (R₁ o).challSimDF = (R₂ o).challSimDF)
    (hbCka : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ tL, (R₁ o).B_cka tL t = (R₂ o).B_cka tL t)
    (hbPrng : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ tL, (R₁ o).B_prng tL t = (R₂ o).B_prng tL t)
    (hbFs : ∀ o {t : ℕ}, t < (qep + 1) + 2 → ∀ j tL, (R₁ o).B_fs j tL t = (R₂ o).B_fs j tL t) :
    hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R₁ A =
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R₂ A := by
  unfold hiddenSaltMixtureBound
  refine congrArg (fun x => x + _ + _) (Finset.sum_congr rfl fun t ht => ?_)
  have hlt : t < (qep + 1) + 2 := Finset.mem_range.mp ht
  simp only [hfs, hsimDF, hchallDF, fun o tL => hbCka o hlt tL, fun o tL => hbPrng o hlt tL,
    fun o j tL => hbFs o hlt j tL]

theorem fig8MixShortAuthV1_clampSessionCostedReductions_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep qep_c : ℕ} (hqep : qep ≤ qep_c)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => clampSessionCostedReductions qep_c (R o)) A =
      fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A :=
  fig8MixShortAuthV1_congr Z K ℓ Dh encPt encT decT lam qep q oa ida idb _ R A
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun o _ ht tL => clampSessionCostedReductions_fig8_redCKAAuth_of_lt qep_c (R o) (by omega) tL)
    (fun o _ ht tL => clampSessionCostedReductions_fig8_redPRNGAuth_of_lt qep_c (R o) (by omega) tL)
    (fun o _ ht j tL =>
      clampSessionCostedReductions_fig8_redFSAuth_of_lt qep_c (R o) (by omega) j tL)

theorem fig8MixShortPrivV1_clampSessionCostedReductions_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep qep_c : ℕ} (hqep : qep ≤ qep_c)
    (q : ℕ) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb
        (fun o => clampSessionCostedReductions qep_c (R o)) A =
      fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R A :=
  fig8MixShortPrivV1_congr Z K ℓ Dh encPt encT decT lam qep q oa ida idb _ R A
    (fun _ => rfl) (fun _ => rfl)
    (fun o _ hi => clampSessionCostedReductions_fig8_privRedB_of_lt qep_c (R o) (by omega))
    (fun o _ hi tL => clampSessionCostedReductions_fig8_redCKAPriv_of_lt qep_c (R o) (by omega) tL)
    (fun o _ hi tL => clampSessionCostedReductions_fig8_redPRNGPriv_of_lt qep_c (R o) (by omega) tL)
    (fun o _ hi tL => clampSessionCostedReductions_fig8_redFSPriv_of_lt qep_c (R o) (by omega) tL)
    (fun o _ hi tL =>
      clampSessionCostedReductions_fig8_redFSPrivCoin_of_lt qep_c (R o) (by omega) tL)

theorem hiddenSaltMixtureBound_clampSessionCostedReductions_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep qep_c : ℕ} (hqep : qep ≤ qep_c)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb
        (fun o => clampSessionCostedReductions qep_c (R o)) A =
      hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A :=
  hiddenSaltMixtureBound_congr Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb _ R A
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun o _ ht tL => clampSessionCostedReductions_B_cka_of_lt qep_c (R o) (by omega) tL)
    (fun o _ ht tL => clampSessionCostedReductions_B_prng_of_lt qep_c (R o) (by omega) tL)
    (fun o _ ht j tL => clampSessionCostedReductions_B_fs_of_lt qep_c (R o) (by omega) j tL)

theorem uniformStartMixtureBound_clampSessionCostedReductions_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) {qep qep_c : ℕ} (hqep : qep ≤ qep_c)
    (q : ℕ) (δ : ℝ≥0∞) (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb
        (fun o => clampSessionCostedReductions qep_c (R o)) A =
      uniformStartMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R A := by
  unfold uniformStartMixtureBound
  rw [fig8MixShortAuthV1_clampSessionCostedReductions_eq Z K ℓ Dh encPt encT decT lam hqep q oa
      ida idb R _,
    fig8MixShortPrivV1_clampSessionCostedReductions_eq Z K ℓ Dh encPt encT decT lam hqep q oa
      ida idb R _,
    hiddenSaltMixtureBound_clampSessionCostedReductions_eq Z K ℓ Dh encPt encT decT lam hqep q δ oa
      ida idb R _]
  simp only [clampSessionCostedReductions_epoch0Red, clampSessionCostedReductions_uniformStartRed]

theorem sessionAdvantageBound_clampSessionCostedReductionFamily_eq_of_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) {qep q : ℕ} (hqep : qep ≤ q + 4) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    sessionAdvantageBound ℓ (clampSessionCostedReductionFamily ℓ D) C K Dh encPt encT decT
        qep q δ oa ida idb s A =
      sessionAdvantageBound ℓ D C K Dh encPt encT decT qep q δ oa ida idb s A := by
  unfold sessionAdvantageBound
  dsimp only
  simp only [clampSessionCostedReductionFamily_of_le ℓ D C K _ _ Dh encPt encT decT _ hqep]

theorem sessionAdvantageBound_le_clampSessionCostedReductionFamily
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    sessionAdvantageBound ℓ D C K Dh encPt encT decT (qepClamp qep q) q δ oa ida idb s A ≤
      sessionAdvantageBound ℓ (clampSessionCostedReductionFamily ℓ D) C K Dh encPt encT decT
        qep q δ oa ida idb s A := by
  by_cases hqep : qep ≤ q + 4
  · rw [qepClamp_eq_qep_of_le hqep,
      sessionAdvantageBound_clampSessionCostedReductionFamily_eq_of_le ℓ D C K Dh encPt encT
        decT hqep δ oa ida idb s A]
  · have hgt : q + 4 < qep := Nat.lt_of_not_ge hqep
    have hc : qepClamp qep q = q + 4 := Nat.min_eq_right (Nat.le_of_lt hgt)
    let D' : SessionCostedReductionFamily Pt ℓ :=
      fun C' K' idA' idB' Dh' encPt' encT' decT' lam' _ q' =>
        clampSessionCostedReductions (q' + 4)
          (D C' K' idA' idB' Dh' encPt' encT' decT' lam' (q' + 4) q')
    have hle := sessionAdvantageBound_qepClamp_le ℓ D' C K Dh encPt encT decT qep q δ
      oa ida idb s A (fun _ => rfl)
    rw [hc] at hle ⊢
    have heqL :
        sessionAdvantageBound ℓ D' C K Dh encPt encT decT (q + 4) q δ oa ida idb s A =
          sessionAdvantageBound ℓ D C K Dh encPt encT decT (q + 4) q δ oa ida idb s A := by
      unfold sessionAdvantageBound
      dsimp only [D']
      simp only [clampSessionCostedReductions_spk]
      rw [uniformStartMixtureBound_clampSessionCostedReductions_eq C K ℓ Dh encPt encT decT
        (0 : Pt) le_rfl q δ oa ida idb
        (fun o => D C K (ida o) (idb o) Dh encPt encT decT 0 (q + 4) q) A]
    have heqR :
        sessionAdvantageBound ℓ D' C K Dh encPt encT decT qep q δ oa ida idb s A =
          sessionAdvantageBound ℓ (clampSessionCostedReductionFamily ℓ D) C K Dh encPt encT decT
            qep q δ oa ida idb s A := by
      unfold sessionAdvantageBound
      dsimp only [D']
      simp only [clampSessionCostedReductionFamily_of_gt ℓ D C K _ _ Dh encPt encT decT _ hgt]
    rw [← heqL, ← heqR]
    exact hle

theorem sessionAdvantageBound_clampSessionCostedReductionFamily_le
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    sessionAdvantageBound ℓ (clampSessionCostedReductionFamily ℓ D) C K Dh encPt encT decT
        (qepClamp qep q) q δ oa ida idb s A ≤
      sessionAdvantageBound ℓ (clampSessionCostedReductionFamily ℓ D) C K Dh encPt encT decT
        qep q δ oa ida idb s A := by
  rw [sessionAdvantageBound_clampSessionCostedReductionFamily_eq_of_le ℓ D C K Dh encPt encT decT
    (qepClamp_le_add qep q) δ oa ida idb s A]
  exact sessionAdvantageBound_le_clampSessionCostedReductionFamily ℓ D C K Dh encPt encT decT
    qep q δ oa ida idb s A

@[simp] theorem clampSessionCostedReductionFamily_fs
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    (clampSessionCostedReductionFamily ℓ D C K idA idB Dh encPt encT decT lam qep q).fs =
      (D C K idA idB Dh encPt encT decT lam (qepClamp qep q) q).fs := by
  by_cases hqep : qep ≤ q + 4
  · simp [clampSessionCostedReductionFamily, hqep, qepClamp_eq_qep_of_le hqep]
  · simp [clampSessionCostedReductionFamily, hqep, qepClamp, Nat.le_of_not_ge hqep]

@[simp] theorem clampSessionCostedReductionFamily_qepClamp
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ)
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) :
    clampSessionCostedReductionFamily ℓ D C K idA idB Dh encPt encT decT lam (qepClamp qep q) q =
      D C K idA idB Dh encPt encT decT lam (qepClamp qep q) q :=
  clampSessionCostedReductionFamily_of_le ℓ D C K idA idB Dh encPt encT decT lam
    (qepClamp_le_add qep q)

section SpkHalted

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {ℓ : ℕ} {C : Crypto} {K : MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

@[expose] def mkSpkCostedRedsHalted
    (leak : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam)
    (leakU : SpkLeakRedUProg Pt ℓ)
    (hop2Prg : ℕ → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam)
    (hop2Prf : ℕ → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam) :
    SpkCostedReds Pt ℓ C K Dh encPt encT decT lam where
  spkLeakRed := leak
  spkLeakRedU := leakU
  hop2PrgRedK := fun k => if k < spkSwapHybridCount then hop2Prg k else hop2Prg 0
  hop2PrfRedK := fun k => if k < spkSwapHybridCount then hop2Prf k else hop2Prf 0

section SpkHaltedProjections
variable (leak : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam) (leakU : SpkLeakRedUProg Pt ℓ)
  (hop2Prg : ℕ → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam)
  (hop2Prf : ℕ → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam)

@[simp] theorem mkSpkCostedRedsHalted_spkLeakRed :
    (mkSpkCostedRedsHalted leak leakU hop2Prg hop2Prf).spkLeakRed = leak := by rfl

@[simp] theorem mkSpkCostedRedsHalted_spkLeakRedU :
    (mkSpkCostedRedsHalted leak leakU hop2Prg hop2Prf).spkLeakRedU = leakU := by rfl

@[simp] theorem mkSpkCostedRedsHalted_hop2PrgRedK_of_lt {k : ℕ} (hk : k < spkSwapHybridCount) :
    (mkSpkCostedRedsHalted leak leakU hop2Prg hop2Prf).hop2PrgRedK k = hop2Prg k := by
  simp [mkSpkCostedRedsHalted, hk]

@[simp] theorem mkSpkCostedRedsHalted_hop2PrfRedK_of_lt {k : ℕ} (hk : k < spkSwapHybridCount) :
    (mkSpkCostedRedsHalted leak leakU hop2Prg hop2Prf).hop2PrfRedK k = hop2Prf k := by
  simp [mkSpkCostedRedsHalted, hk]

end SpkHaltedProjections

theorem mkSpkCostedRedsHalted_bounds
    {q qep : ℕ}
    {leak : SpkLeakRedProg Pt ℓ C K Dh encPt encT decT lam}
    {leakU : SpkLeakRedUProg Pt ℓ}
    {hop2Prg : ℕ → SpkSwapPrgHybridProg Pt ℓ C K Dh encPt encT decT lam}
    {hop2Prf : ℕ → SpkSwapPrfHybridProg Pt ℓ C K Dh encPt encT decT lam}
    (hleak : GRedBounded leak (fun _ => 1) (fun _ => 0) q (q + 1) (spkHopBudget q qep ℓ))
    (hleakU : GRedBounded leakU (fun _ => 1) (fun _ => 0) (q + 1) (q + 1) (spkLeakRedUBudget q))
    (hhop2Prg : ∀ k < spkSwapHybridCount,
      GRedBounded (hop2Prg k) Empty.elim (fun _ => 0) q 0 (spkHopBudget q qep ℓ))
    (hhop2Prf : ∀ k < spkSwapHybridCount,
      GRedBounded (hop2Prf k) (fun _ => 1) (fun _ => 0) q q (spkHopBudget q qep ℓ)) :
    spkCostedBounds q qep (mkSpkCostedRedsHalted leak leakU hop2Prg hop2Prf) :=
  ⟨hleak, hleakU,
    fun k hk => by simp only [mkSpkCostedRedsHalted, hk, ↓reduceIte]; exact hhop2Prg k hk,
    fun k hk => by simp only [mkSpkCostedRedsHalted, hk, ↓reduceIte]; exact hhop2Prf k hk⟩

end SpkHalted

end

end Computational.Proofs.SessionCostedHalt
