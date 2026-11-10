/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementIdsModel
public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import Computational.Specifications.Pqxdh.Game
public import Computational.Specifications.Session.ACD19.SM.Theorem8And12Statements
public import Computational.Specifications.Reductions.ReductionDsl.AtomicOps
public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs

/-!
# Session-level bound terms, adversary wrapper and reduction bundles shared by the statements

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `paramsV1`, which is checked by Lean; the ones they use are part of what you must read to
trust the result. See `Computational/docs/TRUSTED_BASE.md`.

Assembles the single-session security bound (`uniformStartMixtureBound`) for the Double Ratchet with
SPQR V1 (`paramsV1`) from the ACD19 (Alwen, Coretti, Dodis, EUROCRYPT 2019) Fig. 8 authenticity and
privacy bounds (`fig8MixShortAuthV1`, `fig8MixShortPrivV1`, `fsAeadMixtureBound`), the
session-to-Fig. 8 refinement slack (`refineConst`, `hiddenSaltMixtureBound`; DEV-LS36), and the
epoch-0 and uniform-start root-KDF PRG switches (`eps0IdealUnit`). Also defines the early-corruption
refusal wrapper `RefuseB0.refuseCorrB0` (DEV-LS33, DEV-LS34), ML-KEM encapsulation totality
(`Encaps1Total`), and scalar-independent DH equality fibers (`DhKerUniform`).

Bounds are stated over a context mixture `oa : ProbComp α` via `prefixPrgAvg`, `prefixPrfAvg`,
`prefixWireAvg`, and `prefixAdvAvg`, and evaluated on first-order `ReductionDsl.CostedReduction`
bundles (`SessionCostedReductions`, `sessionCostedReductionsBounded`; see
`Computational/docs/REDUCTION_DSL_TUTORIAL.md`).
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoGames.Ratchet.LibsignalSim
  CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1

/-! ## ML-KEM encapsulation totality -/

/-- `K.encaps1` succeeds on every 64-byte header (satisfied by libcrux ML-KEM-768, which checks
only header length). -/
def Encaps1Total (K : LibsignalSpqrV1.MlKem) : Prop :=
  ∀ (hdr : Bytes) (rand : List.Vector (BitVec 8) 32),
    hdr.length = 64 → (K.encaps1 hdr rand).isSome

/-! ## Early-corruption refusal wrapper -/

namespace RefuseB0

/-- Observable game-state shadow tracked by `refuseCorrB0`: party epochs, within-epoch indices,
and in-transit `(pos, ct)` pairs. -/
structure RefuseState (C : Type) where
  epoch : Party → ℕ := fun _ => 0
  idx : Party → ℕ := fun _ => 0
  trans : List (SM.Pos × C) := []

namespace RefuseState

variable {C : Type}

/-- Updates `RefuseState` after an accepted `transmit` or `chall` returning `some c`. -/
def onSend (rs : RefuseState C) (P : Party) (c : C) : RefuseState C :=
  let ep' :=
    if P.sendsIn (rs.epoch P + 1) then Function.update rs.epoch P (rs.epoch P + 1) else rs.epoch
  let idx₀ := if P.sendsIn (rs.epoch P + 1) then Function.update rs.idx P 0 else rs.idx
  let pos : SM.Pos := ⟨P, ep' P, idx₀ P + 1⟩
  { epoch := ep'
    idx := Function.update idx₀ P (idx₀ P + 1)
    trans := (pos, c) :: rs.trans }

/-- Updates `RefuseState` when `P` accepts a message at position `pos`. -/
def onAccept (rs : RefuseState C) (P : Party) (pos : SM.Pos) : RefuseState C :=
  { rs with
    epoch := Function.update rs.epoch P (max (rs.epoch P) pos.epoch)
    trans := rs.trans.filter (fun pc => pc.1 != pos) }

/-- Updates `RefuseState` after an accepted `deliver-P(c)`. -/
def onDeliver [DecidableEq C] (rs : RefuseState C) (P : Party) (c : C) : RefuseState C :=
  match rs.trans.find? (fun pc => pc.1.sender == P.other && decide (pc.2 = c)) with
  | some (pos, _) => rs.onAccept P pos
  | none => rs

end RefuseState

abbrev RefuseM (St Msg Coins C : Type) := StateT (RefuseState C) (SM.AdversaryComp St Msg Coins C)

def refuseTransmit {St Msg Coins C : Type} :
    QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
  fun ⟨P, m, r⟩ => do
    let res ← StateT.lift (SM.transmitQuery (St := St) P m r)
    match res with
    | some c =>
      let rs ← get
      set (rs.onSend P c)
    | none => pure ()
    return res

def refuseChall {St Msg Coins C : Type} :
    QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let res ← StateT.lift (SM.challQuery (St := St) P m₀ m₁ r)
    match res with
    | some c =>
      let rs ← get
      set (rs.onSend P c)
    | none => pure ()
    return res

def refuseDeliver {St Msg Coins C : Type} [DecidableEq C] :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg)) (RefuseM St Msg Coins C) :=
  fun ⟨P, c⟩ => do
    let res ← StateT.lift (SM.deliverQuery (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted _ _ _) =>
      let rs ← get
      set (rs.onDeliver P c)
    | _ => pure ()
    return res

def refuseInject {St Msg Coins C : Type} :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg)) (RefuseM St Msg Coins C) :=
  fun ⟨P, c⟩ => do
    let res ← StateT.lift (SM.injectQuery (St := St) (Coins := Coins) P c)
    match res with
    | some (.accepted t' i' _) =>
      let rs ← get
      set (rs.onAccept P ⟨P.other, t', i'⟩)
    | _ => pure ()
    return res

/-- Locally refuses `corr-B` when `epoch .B == 0` (DEV-LS33) or `epoch .A < 10` (DEV-LS34), and
forwards all other corruption queries. -/
def refuseCorr {St Msg Coins C : Type} :
    QueryImpl (Party →ₒ Option St) (RefuseM St Msg Coins C) :=
  fun P => do
    let rs ← get
    if (P == .B && (rs.epoch .B == 0)) || (P == .B && decide (rs.epoch .A < 10)) then
      return none
    else
      StateT.lift (SM.corrQuery (Msg := Msg) (Coins := Coins) (C := C) P)

def refuseCorrB0Impl {St Msg Coins C : Type} [DecidableEq C] :
    QueryImpl (unifSpec + SM.spec St Msg Coins C) (RefuseM St Msg Coins C) :=
  let c : QueryImpl unifSpec (RefuseM St Msg Coins C) := fun n =>
    StateT.lift (query (spec := unifSpec + SM.spec St Msg Coins C) (.inl n))
  let i₁ : QueryImpl ((Party × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
    refuseTransmit
  let i₂ : QueryImpl ((Party × Msg × Msg × Option Coins) →ₒ Option C) (RefuseM St Msg Coins C) :=
    refuseChall
  let i₃ : QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg)) (RefuseM St Msg Coins C) :=
    refuseDeliver
  let i₄ : QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg)) (RefuseM St Msg Coins C) :=
    refuseInject
  let i₅ : QueryImpl (Party →ₒ Option St) (RefuseM St Msg Coins C) :=
    refuseCorr
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

/-- Wraps `A` so that `corr-B` queries refused by `noBobCorrInEpoch0` (DEV-LS33) or
`noBobCorrWhileAliceBelowEpoch10` (DEV-LS34) return `none` without querying the game. -/
def refuseCorrB0 {St Msg Coins C : Type} [DecidableEq C]
    (A : SM.Adversary St Msg Coins C) : SM.Adversary St Msg Coins C :=
  (simulateQ refuseCorrB0Impl A).run' {}

end RefuseB0

/-! ## Mixture averaging and SPQR V1 session bound -/

/-- Averages a family of PRG distinguishers `D o` over a prefix distribution `oa`. -/
def prefixPrgAvg {α R : Type} (oa : ProbComp α) (D : α → PRGScheme.PRGAdversary R) :
    PRGScheme.PRGAdversary R := fun r => oa >>= fun o => D o r

/-- Averages a family of PRF adversaries `D o` over a prefix distribution `oa`. -/
def prefixPrfAvg {α Input Tag : Type} (oa : ProbComp α)
    (D : α → MACScheme.PRFAdversary Input Tag) :
    MACScheme.PRFAdversary Input Tag :=
  bind (m := OracleComp (unifSpec + MACScheme.prfSpec Input Tag))
    (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α) D

/-- Averages a family of wire OT-CCA adversaries `A o` over a prefix distribution `oa`. -/
def prefixWireAvg {α AD H M M' T : Type} (oa : ProbComp α)
    (A : α → WireAEAD.WireAdversary AD H M M' T) :
    WireAEAD.WireAdversary AD H M M' T :=
  bind (m := OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T))
    (liftM oa : OracleComp (unifSpec + WireAEAD.wireSpec AD H M M' T) α) A

/-- Averages a family of adversaries in an arbitrary game with coins `unifSpec`. -/
def prefixAdvAvg {ι : Type} {spec : OracleSpec ι} {α β : Type} (oa : ProbComp α)
    (D : α → OracleComp (unifSpec + spec) β) : OracleComp (unifSpec + spec) β :=
  bind (m := OracleComp (unifSpec + spec)) (liftM oa : OracleComp (unifSpec + spec) α) D

/-- Bundle of first-order `ReductionDsl.CostedReduction` programs for a single Double Ratchet +
SPQR V1 session at send coins `BitVec 512`. Combines the SPK (`spk`), ACD19 Fig. 8 (`fig8`), and
FS-AEAD (`fs`) reduction bundles with the session-to-Fig. 8 simulators, root-KDF PRG
distinguishers, and `DeliverForge` authenticity reductions. ML-KEM encapsulation and decapsulation
failures are excluded here and charged via `MlKem.KemFailBad` on the universally quantified
adversary, since an existentially quantified reduction could hard-code a failing seed pair. -/
structure SessionCostedReductions (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ)
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) where
  spk : SpkCostedReds Pt ℓ C K Dh encPt encT decT lam
  fig8 : Fig8CostedReds Dh encPt C protoSignalCodec ℓ encT (idsOf idA idB) lam
  fs : FsCostedReds C protoSignalCodec ℓ encT (idsOf idA idB)
  /-- Outer session-to-Fig. 8 refinement simulator. -/
  simFig8 :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (ReductionDsl.fig8SmIface ℓ Pt)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (ReductionDsl.e2eSessionCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Outer session-to-`SM.specDF` simulator for the hidden-salt `DeliverForge` game. -/
  simDeliverForge :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (ReductionDsl.fig8SmIfaceDF ℓ Pt)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (ReductionDsl.e2eSessionCodec ℓ Pt)
      .unit .unit .bool .bool
  /-- Epoch-0 `rootKdfAsPrg` distinguisher. -/
  epoch0Red :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (ReductionDsl.coinOnlyIface ℓ Pt)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (ReductionDsl.e2eSessionCodec ℓ Pt)
      (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .bool
  /-- Uniform-start `rootKdfAsPrg` distinguisher. -/
  uniformStartRed :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (ReductionDsl.coinOnlyIface ℓ Pt)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes)
      (ReductionDsl.e2eSessionCodec ℓ Pt)
      (.prod ReductionDsl.BV256 ReductionDsl.BV256) .unit .bool .bool
  /-- Authenticity challenge simulator over the 6-oracle `SM.specDF` interface. -/
  challSimDF :
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fig8SmIfaceDF ℓ Pt)
      (SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodecDF ℓ Pt)
      .unit .unit .bool .bool
  /-- `DeliverForge` CKA authenticity reduction at leak guess `tL` and epoch `t`. -/
  B_cka : (tL : Option ℕ) → (t : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.ckaTargetIface ℓ Pt)
      (SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodecDF ℓ Pt)
      .unit .unit .bool .bool
  /-- `DeliverForge` PRF-PRNG authenticity reduction at leak guess `tL` and epoch `t`. -/
  B_prng : (tL : Option ℕ) → (t : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.prngTargetIface ℓ Pt)
      (SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodecDF ℓ Pt)
      .unit .unit .bool .bool
  /-- `DeliverForge` FS-AEAD authenticity reduction at query index `j`, leak guess `tL`, and epoch `t`. -/
  B_fs : (j : ℕ) → (tL : Option ℕ) → (t : ℕ) →
    ReductionDsl.CostedReduction
      (ReductionDsl.atomicFig8Ops ℓ Pt C Dh encPt encT lam)
      (ReductionDsl.fsaeadHeaderIface ℓ Pt)
      (SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
      (ReductionDsl.fig8SmCodecDF ℓ Pt)
      .unit .unit .bool .bool

/-- Step-cost, program-size, and oracle-query bounds for all reductions in `R` at query budget `q`,
epoch bound `qep`, and cost budget `ratchetCostBudget q (qep + 1)`. Also imposes semantic query
bounds `min (2 + 2 * q) (q + 3)` on `R.B_prng` and `min (2 * q) (q + 2)` on `R.B_fs`. -/
def sessionCostedReductionsBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (lam : Pt) (qep q : ℕ)
    (R : SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam) : Prop :=
  let B := ratchetCostBudget q (qep + 1)
  spkCostedBounds q qep R.spk ∧
  fig8CostedBounds q (qep + 1) R.fig8 ∧
  fsCostedBounds (min (2 * q) (q + 2)) (qep + 1) R.fs ∧
  GRedBounded R.simFig8 (fun _ => 1) (fun _ => 0) q q B ∧
  GRedBounded R.simDeliverForge (fun _ => 1) (fun _ => 0) q q B ∧
  GRedBounded R.epoch0Red Empty.elim (fun _ => 0) q 0 B ∧
  GRedBounded R.uniformStartRed Empty.elim (fun _ => 0) q 0 B ∧
  GRedBounded R.challSimDF (fun _ => 1) (fun _ => 0) q q B ∧
  (∀ t < (qep + 1) + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t,
    GRedBounded (R.B_cka tL t) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
  (∀ t < (qep + 1) + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t,
    GRedBounded (R.B_prng tL t) (fun _ => 1) (fun _ => 0) q (2 + 2 * q) B) ∧
  (∀ t < (qep + 1) + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t, ∀ j < q,
    GRedBounded (R.B_fs j tL t) (fun _ => 1) (fun _ => 0) q (2 * q) B) ∧
  (∀ t < (qep + 1) + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t,
    ∀ A : OracleComp
        (unifSpec +
          SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (LibsignalSim.Fig8C Pt))
        Bool,
      A.IsQueryBoundP (· matches .inr _) q →
        PRFPRNG.MakesAtMostQueries ((R.B_prng tL t).eval (fun _ => A) ())
          (min (2 + 2 * q) (q + 3))) ∧
  (∀ t < (qep + 1) + 2, ∀ tL ∈ admissibleLastLeakGuesses 2 t, ∀ j < q,
    ∀ A : OracleComp
        (unifSpec +
          SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (LibsignalSim.Fig8C Pt))
        Bool,
      A.IsQueryBoundP (· matches .inr _) q →
        FSAEAD.MakesAtMostQueries ((R.B_fs j tL t).eval (fun _ => A) ())
          (min (2 * q) (q + 2)))

/-- Per-session computational FS-AEAD deliver-forgery bound on `R` across the `fsSlotCount qR`
active slots (chain-PRG, twice salt-PRF, and wire OT-CCA). -/
noncomputable def fsAeadSlotSumBound {Pt : Type} [DecidableEq Pt]
    (C : Crypto) {codec : SignalMessageProtoCodec} {ℓ : ℕ} {encT : Pt → PublicKey}
    {idOf : Party → IdentityKey} (qR : ℕ)
    (R : FsCostedReds C codec ℓ encT idOf) (A : FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ k ∈ Finset.range (fsSlotCount qR),
    (chainPRGTermCosted C qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR k) +
      2 * saltPRFTermCosted C qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR k) +
      wireOtccaTermCosted C codec ℓ qR R A (FSAEAD.Thm5.slotToHybridHopIndex qR k))

/-- Mixture-averaged chain-PRG advantage at hybrid hop `m` and query fuel `qR`. -/
noncomputable def fsChainPrgMixtureTerm {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
    {codec : SignalMessageProtoCodec} {ℓ : ℕ} {encT : Pt → PublicKey} (oa : ProbComp α)
    {idOf : α → Party → IdentityKey} (qR : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A : α → FsAdv Pt ℓ) (m : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (m / 2)).prgAdvantage
    (prefixPrgAvg oa fun o =>
      fun mt => evalTwoStage1 ((R o).prgRedZero m) qR false (fun _ => pubToADCosted (R o) (A o)) mt)

/-- Mixture-averaged salt-PRF and wire OT-CCA advantage terms at hybrid hop `m` and query fuel
`qR`. -/
noncomputable def fsSaltWireMixtureTerm {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) {encT : Pt → PublicKey} (oa : ProbComp α)
    {idOf : α → Party → IdentityKey} (qR : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A : α → FsAdv Pt ℓ) (m : ℕ) : ℝ≥0∞ :=
  let la := FSAEAD.Thm5.isLookaheadHop m
  2 * (lSaltPRF32 C.F).prfAdvantage
      (prefixPrfAvg oa fun o =>
        (R o).lSaltRed.eval
          (fun _ => ((R o).slotSaltRed m).eval
            (fun _ => multiSlotAdvCosted qR (R o) la (A o)) ()) ()) +
    (lWire C codec ℓ).wireOtccaAdvantage
      (prefixWireAvg oa fun o =>
        (R o).lWireRed.eval
          (fun _ => ((R o).slotWireRed m).eval
            (fun _ => multiSlotAdvCosted qR (R o) la (A o)) ()) ())

/-- Mixture-averaged FS-AEAD short bound across `fsSlotCount q` active slots plus the hoisted
MAC-forgery term `4 * qd * macForgeryProb C.F`. -/
noncomputable def fsAeadMixtureBound {Pt : Type} [DecidableEq Pt] {α : Type} (C : Crypto)
    (codec : SignalMessageProtoCodec) (ℓ : ℕ) {encT : Pt → PublicKey} (oa : ProbComp α)
    {idOf : α → Party → IdentityKey} (q qd : ℕ)
    (R : ∀ o, FsCostedReds C codec ℓ encT (idOf o))
    (A : α → FsAdv Pt ℓ) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (fsSlotCount q),
      (fsChainPrgMixtureTerm C oa q R A (FSAEAD.Thm5.slotToHybridHopIndex q j) +
        fsSaltWireMixtureTerm C codec ℓ oa q R A (FSAEAD.Thm5.slotToHybridHopIndex q j)) +
    4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)

/-- Session parameters for identity keys `idA`, `idB` with SPQR V1 (`spqrV1SessionUniformCoins Z.F K`). -/
abbrev paramsV1 (Z : Crypto) (K : LibsignalSpqrV1.MlKem)
    (idA idB : IdentityKey) : LibsignalSession.Params Bytes (BitVec 512) :=
  paramsIdsWithSpqr Z (LibsignalSpqrV1.spqrV1SessionUniformCoins Z.F K) idA idB

/-- Context-independent session-to-Fig. 8 refinement slack: spurious DH-step terms plus the
ratchet-key collision bound `(qep + 2) * (q + qep + 2) * δ`. -/
noncomputable def refineConst {Pt : Type} [DecidableEq Pt] [Zero Pt] (Z : Crypto)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (q qep : ℕ) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  forgedEpochStartSpuriousStepTerm Z.F encPt Dh q + spuriousStepTerm Z.F encPt Dh q qep +
    (qep + 2) * (q + qep + 2) * δ

/-- Worst-case probability that uniform PRG output passes `wireMacVerifiesTest`, over chain
counters `c < 2 ^ 32` and wire lengths `ser.length < 2 ^ 32` (DEV-LS23). -/
noncomputable def eps0IdealUnit (F : ShaState → List (BitVec 8) → ShaState) : ℝ≥0∞ :=
  ⨆ (c : ℕ) (_ : c < 2 ^ 32) (salt : Salt) (ids : SerializedIdentityKeys) (ser : List (BitVec 8))
    (_ : ser.length < 2 ^ 32) (tag : BitVec 64),
    𝒟[PRGScheme.prgIdealExperiment (wireMacVerifiesTest F c salt ids ser tag)] {true}

/-- Mixture upper bound on the hidden-salt refinement probe game when SPQR lacks salt binding
(DEV-LS36). Integrates the `DeliverForge` CKA, PRF-PRNG, FS-AEAD, and MAC-forgery bounds over
`o ← oa`, plus `spuriousStepTerm` (for forward-evicted honest wires probed after sender
corruption) and `(qep + 1) * (qep + 2) * δ`. Excludes ML-KEM failure probabilities, which are
charged at top level via the real-game bad event `MlKem.KemFailBad` on the universally
quantified adversary. -/
noncomputable def hiddenSaltMixtureBound {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  let dfAdv : α →
      OracleComp
        (unifSpec +
          SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (LibsignalSim.Fig8C Pt))
        Bool :=
    fun o => (R o).simDeliverForge.eval (fun _ => A o) ()
  let challAdvDF : α →
      OracleComp
        (unifSpec +
          SM.specDF (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256)
            (LibsignalSim.Fig8C Pt))
        Bool :=
    fun o => (R o).challSimDF.eval (fun _ => dfAdv o) ()
  ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses 2 t,
    ((∫⁻ o, CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (((R o).B_cka tL t).eval (fun _ => challAdvDF o) ()) ∂𝒟[oa]) +
      (∫⁻ o, PRFPRNG.advantage (rootPRNG Z.F encPt)
        (((R o).B_prng tL t).eval (fun _ => challAdvDF o) ()) ∂𝒟[oa]) +
      (∑ j ∈ Finset.range q,
        ∫⁻ o, fsAeadSlotSumBound Z (min (2 * q) (q + 2)) (R o).fs
          (((R o).B_fs j tL t).eval (fun _ => challAdvDF o) ()) ∂𝒟[oa]) +
      4 * (q : ℝ≥0∞) * CryptoVerification.LibsignalSession.macForgeryTerm Z q) +
    spuriousStepTerm Z.F encPt Dh q qep +
    (qep + 1) * (qep + 2) * δ

/-- Mixture-averaged ACD19 Fig. 8 authenticity bound for `(R o).simFig8` on SPQR V1, with
FS-AEAD terms expanded via `fsAeadMixtureBound`. -/
noncomputable def fig8MixShortAuthV1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  let simAdv : α → Fig8Adv Pt ℓ :=
    fun o => (R o).simFig8.eval (fun _ => A o) ()
  let challAdv : α → Fig8Adv Pt ℓ :=
    fun o => (R o).fig8.challSim.eval (fun _ => simAdv o) ()
  2 * ∑ t ∈ Finset.range ((qep + 1) + 2), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) t,
    (CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o => ((R o).fig8.redCKAAuth tL t).eval (fun _ => challAdv o) ())
      + PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o => ((R o).fig8.redPRNGAuth tL t).eval (fun _ => challAdv o) ())
      + ∑ j ∈ Finset.range q,
          fsAeadMixtureBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q (fun o => (R o).fs)
            (fun o => ((R o).fig8.redFSAuth j tL t).eval (fun _ => challAdv o) ()))

/-- Mixture-averaged ACD19 Fig. 8 privacy bound for `(R o).simFig8` on SPQR V1, with FS-AEAD
terms expanded via `fsAeadMixtureBound`. -/
noncomputable def fig8MixShortPrivV1 {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (oa : ProbComp α)
    (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  let simAdv : α → Fig8Adv Pt ℓ :=
    fun o => (R o).simFig8.eval (fun _ => A o) ()
  2 * ∑ i ∈ Finset.range ((qep + 1) + 1), ∑ tL ∈ admissibleLastLeakGuesses (2 + 1) i,
    let privAdv : α → Fig8Adv Pt ℓ :=
      fun o => ((R o).fig8.privRedB i).eval (fun _ => simAdv o) ()
    (2 * CKA.advantage (dhScheme Dh) 1 (healEpoch tL)
        (prefixAdvAvg oa fun o => ((R o).fig8.redCKAPriv tL i).eval (fun _ => privAdv o) ())
      + 2 * PRFPRNG.advantage (rootPRNG Z.F encPt)
        (prefixAdvAvg oa fun o => ((R o).fig8.redPRNGPriv tL i).eval (fun _ => privAdv o) ())
      + fsAeadMixtureBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q (fun o => (R o).fs)
          (fun o => ((R o).fig8.redFSPriv tL i).eval (fun _ => privAdv o) ())
      + 2 * fsAeadMixtureBound Z protoSignalCodec ℓ oa (min (2 * q) (q + 2)) q (fun o => (R o).fs)
          (fun o => ((R o).fig8.redFSPrivCoin tL i).eval (fun _ => privAdv o) ()))

/-- Upper bound on the mixture-averaged `sessionSchemeU` game bias with SPQR V1 on
`RefuseB0.refuseCorrB0`-wrapped adversaries: sums the ACD19 Fig. 8 authenticity and privacy
bounds, `refineConst`, the epoch-0 and uniform-start `rootKdfAsPrg` advantages, and
`2 * hiddenSaltMixtureBound`. -/
noncomputable def uniformStartMixtureBound {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {α : Type} (Z : Crypto) (K : LibsignalSpqrV1.MlKem) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ) (δ : ℝ≥0∞)
    (oa : ProbComp α) (ida idb : α → IdentityKey)
    (R : ∀ o, SessionCostedReductions Pt ℓ Z K (ida o) (idb o) Dh encPt encT decT lam)
    (A : α → SM.Adversary (GhostState Bytes) (CBC.Plain ℓ) (BitVec 512) Bytes) : ℝ≥0∞ :=
  2 * fig8MixShortAuthV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A o))
    + fig8MixShortPrivV1 Z K ℓ Dh encPt encT decT lam qep q oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A o))
    + 2 * refineConst Z Dh encPt q qep δ
    + 2 * ((rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
          (prefixPrgAvg oa fun o => fun rc =>
            (R o).epoch0Red.eval (fun _ => RefuseB0.refuseCorrB0 (A o)) rc)
        + q * eps0IdealUnit Z.F)
    + 2 * hiddenSaltMixtureBound Z K ℓ Dh encPt encT decT lam qep q δ oa ida idb R
        (fun o => RefuseB0.refuseCorrB0 (A o))
    + 2 * (rootKdfAsPrg Z.F (encPt lam)).prgAdvantage
        (prefixPrgAvg oa fun o => fun rc =>
          (R o).uniformStartRed.eval (fun _ => RefuseB0.refuseCorrB0 (A o)) rc)

/-! ## Parameterized reduction families and DH kernel hypothesis -/

/-- Family of `SessionCostedReductions` bundles indexed by cryptographic primitives, identity
keys, group encoding, and query budgets `(qep, q)`. -/
abbrev SessionCostedReductionFamily (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt] (ℓ : ℕ) :
    Type :=
  (C : Crypto) → (K : LibsignalSpqrV1.MlKem) → (idA idB : IdentityKey) →
  (Dh : DHFun (BitVec 256) Pt) → (encPt : Pt → Bytes) →
  (encT : Pt → PublicKey) → (decT : PublicKey → Option Pt) →
  (lam : Pt) → (qep q : ℕ) →
  SessionCostedReductions Pt ℓ C K idA idB Dh encPt encT decT lam

/-- Uniform resource boundedness (`sessionCostedReductionsBounded`) across all parameter
instantiations of `D`. -/
def SessionCostedReductionFamilyBounded {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (ℓ : ℕ) (D : SessionCostedReductionFamily Pt ℓ) : Prop :=
  ∀ (C : Crypto) (K : LibsignalSpqrV1.MlKem) (idA idB : IdentityKey)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (lam : Pt) (qep q : ℕ),
    sessionCostedReductionsBounded ℓ C K idA idB Dh encPt encT decT lam qep q
      (D C K idA idB Dh encPt encT decT lam qep q)

/-- Scalar-independence of DH equality fibers (`Dh.dh x Q = Dh.dh x Q' ↔ Dh.dh s Q = Dh.dh s Q'`),
used in hop 2 to relabel the epoch-0 random function across scalars.

For clamped x-only X25519 on the prime-order subgroup `Pt` (`0` plus the `(ℓ - 1) / 2` pairs
`{±P}` of order `ℓ = 2 ^ 252 + 27742317777372353535851937790883648493`), every clamped scalar
`c = 8m` (`2 ^ 251 ≤ m < 2 ^ 252`) satisfies `gcd(c, ℓ) = 1`, so `Q ↦ u(c · Q)` is a bijection on
`Pt` (`δ = 2 ^ (-250)`). The carrier `Pt` must be restricted to this prime-order subgroup under
clamped scalars: nonzero `E[8]` or twist `E'[4]` torsion points are annihilated by `8m` (which
violates `dh x Q ≠ 0`), mixed-order or twist cosets separate uniform `Pt` challenges from honest
basepoint multiples in `CKA.corrGame`, and unclamped scalars fail at `x ≡ 0 (mod ℓ)`. -/
def DhKerUniform {Pt : Type} (Dh : DHFun (BitVec 256) Pt) : Prop :=
  ∀ (s x : BitVec 256) (Q Q' : Pt), Dh.dh x Q = Dh.dh x Q' ↔ Dh.dh s Q = Dh.dh s Q'

end CryptoVerification.E2E
