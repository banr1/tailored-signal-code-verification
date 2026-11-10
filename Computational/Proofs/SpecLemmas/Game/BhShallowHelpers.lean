/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables
public import Computational.Specifications.Reductions.Pqxdh.StatementPqReds

/-!
# Shallow reference reductions for binary-harness and composition games

Defines shallow `OracleComp` reference runners (`L_bh`, `bhKindRedWith`, and
`Prefix1Key.bhPrefixRedWith`) used by the `ReductionDsl` equivalence proofs in
`Computational/Proofs/E2E/Dsl/`, keeping proof-only simulation helpers out of costed operation and
sampler tables.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession (stdinCapBytes)

namespace CryptoVerification.E2E

/-- Decoded query sum for `bhTargetGameSpec S ℓ PQC`. -/
abbrev BHTargetQuery (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) : Type :=
  (SignalPqxdh.KeyIndQuery S ⊕ SignalPqxdh.SessionId S) ⊕
    (ℕ × (SM.spec (GhostState Bytes) (Plain ℓ) PQC Bytes).Domain)

/-- Packed response sum for `bhTargetGameSpec S ℓ PQC`. -/
abbrev BHTargetResp (ℓ : ℕ) : Type :=
  (SignalPqxdh.KeyIndResponse ⊕ Option ℕ) ⊕ BHE2ESmResp ℓ

def bhTargetQenc {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type} :
    (bhTargetGameSpec S ℓ PQC).Domain → BHTargetQuery S ℓ PQC
  | .inl (.inl kq) => .inl (.inl kq)
  | .inl (.inr (.startDR sid)) => .inl (.inr sid)
  | .inr ⟨i, sq⟩ => .inr (i, sq)

def bhTargetRdec {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (t : (bhTargetGameSpec S ℓ PQC).Domain) (r : BHTargetResp ℓ) :
    (bhTargetGameSpec S ℓ PQC).Range t :=
  match t, r with
  | .inl (.inl _), .inl (.inl kr) => kr
  | .inl (.inl _), _ => .noneResp
  | .inl (.inr _), .inl (.inr idx?) => idx?
  | .inl (.inr _), _ => none
  | .inr ⟨_, sq⟩, .inr sr => bhUnpackSmResp sq sr
  | .inr ⟨_, sq⟩, _ => bhModelSmDefault sq

def bhTargetDefaultResp {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type} :
    BHTargetQuery S ℓ PQC → BHTargetResp ℓ
  | .inl (.inl _) => .inl (.inl .noneResp)
  | .inl (.inr _) => .inl (.inr none)
  | .inr _ => .inr (none, none, none)

def bhFwdU {κ : Type} {G : OracleSpec κ} (n : unifSpec.Domain) :
    OracleComp (unifSpec + G) (unifSpec.Range n) :=
  query (spec := unifSpec + G) (.inl n)

def bhLiftP {κ α : Type} {G : OracleSpec κ} (p : ProbComp α) :
    OracleComp (unifSpec + G) α :=
  simulateQ (bhFwdU (G := G)) p

@[simp] theorem e2eKeyIndTargetIface_fwdU_eq_bhFwdU (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (n : unifSpec.Domain) :
    (Costed.e2eKeyIndTargetIface S ℓ).fwdU n = bhFwdU n := rfl

@[simp] theorem e2eSessionTargetIface_fwdU_eq_bhFwdU (ℓ : ℕ) (n : unifSpec.Domain) :
    (Costed.e2eSessionTargetIface ℓ).fwdU n = bhFwdU n := rfl

@[simp] theorem e2eKeyIndTargetIface_liftP_eq_bhLiftP (S : SignalPqxdh.Setup) (ℓ : ℕ)
    {α : Type} (p : ProbComp α) :
    (Costed.e2eKeyIndTargetIface S ℓ).liftP p = bhLiftP p := rfl

@[simp] theorem e2eSessionTargetIface_liftP_eq_bhLiftP (ℓ : ℕ)
    {α : Type} (p : ProbComp α) :
    (Costed.e2eSessionTargetIface ℓ).liftP p = bhLiftP p := rfl

@[simp] theorem bhLiftP_pure {κ α : Type} {G : OracleSpec κ} (x : α) :
    bhLiftP (G := G) (pure x) = pure x := by
  simp [bhLiftP]

theorem bhLiftP_bind {κ α β : Type} {G : OracleSpec κ}
    (p : ProbComp α) (f : α → ProbComp β) :
    bhLiftP (G := G) (p >>= f) = (bhLiftP p >>= fun x => bhLiftP (f x)) := by
  simp [bhLiftP, simulateQ_bind]

theorem bhLiftP_map {κ α β : Type} {G : OracleSpec κ}
    (f : α → β) (p : ProbComp α) :
    bhLiftP (G := G) (f <$> p) = f <$> bhLiftP p := by
  simp [bhLiftP, simulateQ_map]

/-! ## Shallow reduction containers -/

/-- Shallow 1-stage reduction from adversary game `G` to target oracle `T`. -/
structure BhShallowRed {κ ι : Type} (G : OracleSpec κ) (T : OracleSpec ι)
    (In Out AIn AOut St : Type) where
  init : In → OracleComp T (AIn × St)
  impl : QueryImpl (unifSpec + G) (StateT St (OracleComp T))
  finish : St → AOut → OracleComp T Out

def BhShallowRed.eval {κ ι : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    {In Out AIn AOut St : Type}
    (R : BhShallowRed G T In Out AIn AOut St)
    (A : AIn → OracleComp (unifSpec + G) AOut) (x : In) : OracleComp T Out := do
  let (a, s) ← R.init x
  let (b, s') ← (simulateQ R.impl (A a)).run s
  R.finish s' b

def bhShallowImplOfHandle {κ ι Q R St : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (handle : St → Q → OracleComp (unifSpec + T) (R × St)) :
    QueryImpl (unifSpec + G) (StateT St (OracleComp (unifSpec + T)))
  | .inl n => StateT.mk fun s => do
    let u ← bhFwdU (G := T) n
    return (u, s)
  | .inr t => StateT.mk fun s => do
    let (r, s') ← handle s (qenc t)
    return (rdec t r, s')

/-- Runs an adversary computation for at most `fuel` game queries using shallow handler `h`. -/
def bhShallowRunFuel {κ ι Q R St α : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ℕ → St → OracleComp (unifSpec + T) (α × St) :=
  OracleComp.construct (C := fun _ => ℕ → St → OracleComp (unifSpec + T) (α × St))
    (fun a _ s => pure (a, s))
    (fun q _ r f s => match q with
      | .inl n => do let u ← bhFwdU (G := T) n; r u f s
      | .inr t => match f with
        | 0 => pure (dflt, s)
        | f + 1 => do
          let p ← h s (qenc t)
          r (rdec t p.1) f p.2)
    oa

/-- Shallow 2-stage reduction from adversary game `G` to target `unifSpec + T`. -/
structure BhShallowTwoStageRed {κ ι : Type} (G : OracleSpec κ) (T : OracleSpec ι)
    (Q R rIn aIn aOut ch rIn2 out σ π : Type) where
  qenc : G.Domain → Q
  rdec : (t : G.Domain) → R → G.Range t
  init : rIn → OracleComp (unifSpec + T) (aIn × σ)
  handlePre : σ → Q → OracleComp (unifSpec + T) ((R × σ) ⊕ (ch × (π × σ)))
  chDone : σ → aOut → OracleComp (unifSpec + T) ch
  resume : σ → π → rIn2 → OracleComp (unifSpec + T) (R × σ)
  handlePost : σ → Q → OracleComp (unifSpec + T) (R × σ)
  finish : σ → aOut → rIn2 → OracleComp (unifSpec + T) out

def BhShallowTwoStageRed.run1 {κ ι Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    {α : Type} (dflt : α) (oa : OracleComp (unifSpec + G) α) :
    ℕ → σ → OracleComp (unifSpec + T) (ReductionDsl.Mid G α π σ ch) :=
  OracleComp.construct
    (C := fun _ => ℕ → σ → OracleComp (unifSpec + T) (ReductionDsl.Mid G α π σ ch))
    (fun a _ s => pure (.done a s))
    (fun q k r f s => match q with
      | .inl n => do let u ← bhFwdU (G := T) n; r u f s
      | .inr t => match f with
        | 0 => pure (.done dflt s)
        | f + 1 => do
          match ← Red.handlePre s (Red.qenc t) with
          | .inl (v, s') => r (Red.rdec t v) f s'
          | .inr (c, p, s') => pure (.paused t c p s' k))
    oa

def BhShallowTwoStageRed.eval1 {κ ι Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (A : aIn → OracleComp (unifSpec + G) aOut) (x : rIn) (fuel : ℕ) (dflt : aOut) :
    OracleComp (unifSpec + T) (ch × ReductionDsl.Mid G aOut π σ ch) := do
  let (a, s) ← Red.init x
  let m ← Red.run1 dflt (A a) fuel s
  match m with
  | .done b s' => do let c ← Red.chDone s' b; pure (c, m)
  | .paused _ c _ _ _ => pure (c, m)

def BhShallowTwoStageRed.eval2 {κ ι Q R rIn aIn aOut ch rIn2 out σ π : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (m : ReductionDsl.Mid G aOut π σ ch) (y : rIn2) (fuel : ℕ) (dflt : aOut) :
    OracleComp (unifSpec + T) out := do
  let (b, s) ← match m with
    | .done b s => pure (b, s)
    | .paused t _ p s k => do
      let (v, s') ← Red.resume s p y
      bhShallowRunFuel Red.qenc Red.rdec Red.handlePost dflt (k (Red.rdec t v)) fuel s'
  Red.finish s b y

@[simp] theorem bhShallowRunFuel_pure {κ ι Q R St α : Type} {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    (dflt a : α) (f : ℕ) (s : St) :
    bhShallowRunFuel qenc rdec h dflt (pure a) f s = pure (a, s) := rfl

@[simp] theorem bhShallowRunFuel_query_inl {κ ι Q R St α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    (dflt : α) (n : ℕ) (mx : Fin (n + 1) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : St) :
    bhShallowRunFuel qenc rdec h dflt
        ((liftM ((unifSpec + G).query (.inl n)) : OracleComp (unifSpec + G) _) >>= mx) f s =
      (bhFwdU (G := T) n >>= fun u => bhShallowRunFuel qenc rdec h dflt (mx u) f s) := by
  simp [bhShallowRunFuel, construct_query_bind]

@[simp] theorem bhShallowRunFuel_query_inr_zero {κ ι Q R St α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    (dflt : α) (t : κ) (mx : G.Range t → OracleComp (unifSpec + G) α) (s : St) :
    bhShallowRunFuel qenc rdec h dflt
        ((liftM ((unifSpec + G).query (.inr t)) : OracleComp (unifSpec + G) _) >>= mx) 0 s =
      pure (dflt, s) := by
  simp [bhShallowRunFuel, construct_query_bind]

@[simp] theorem bhShallowRunFuel_query_inr_succ {κ ι Q R St α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (qenc : G.Domain → Q) (rdec : (t : G.Domain) → R → G.Range t)
    (h : St → Q → OracleComp (unifSpec + T) (R × St))
    (dflt : α) (t : κ) (mx : G.Range t → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : St) :
    bhShallowRunFuel qenc rdec h dflt
        ((liftM ((unifSpec + G).query (.inr t)) : OracleComp (unifSpec + G) _) >>= mx) (f + 1) s =
      (h s (qenc t) >>= fun p =>
        bhShallowRunFuel qenc rdec h dflt (mx (rdec t p.1)) f p.2) := by
  simp [bhShallowRunFuel, construct_query_bind]

@[simp] theorem BhShallowTwoStageRed.run1_pure {κ ι Q R rIn aIn aOut ch rIn2 out σ π α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (dflt a : α) (f : ℕ) (s : σ) :
    Red.run1 dflt (pure a) f s = pure (.done a s) := rfl

@[simp] theorem BhShallowTwoStageRed.run1_query_inl
    {κ ι Q R rIn aIn aOut ch rIn2 out σ π α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (dflt : α) (n : ℕ) (mx : Fin (n + 1) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ) :
    Red.run1 dflt
        ((liftM ((unifSpec + G).query (.inl n)) : OracleComp (unifSpec + G) _) >>= mx) f s =
      (bhFwdU (G := T) n >>= fun u => Red.run1 dflt (mx u) f s) := by
  simp [BhShallowTwoStageRed.run1, construct_query_bind]

@[simp] theorem BhShallowTwoStageRed.run1_query_inr_zero
    {κ ι Q R rIn aIn aOut ch rIn2 out σ π α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (dflt : α) (t : κ) (mx : G.Range t → OracleComp (unifSpec + G) α) (s : σ) :
    Red.run1 dflt
        ((liftM ((unifSpec + G).query (.inr t)) : OracleComp (unifSpec + G) _) >>= mx) 0 s =
      pure (.done dflt s) := by
  simp [BhShallowTwoStageRed.run1, construct_query_bind]

@[simp] theorem BhShallowTwoStageRed.run1_query_inr_succ
    {κ ι Q R rIn aIn aOut ch rIn2 out σ π α : Type}
    {G : OracleSpec κ} {T : OracleSpec ι}
    (Red : BhShallowTwoStageRed G T Q R rIn aIn aOut ch rIn2 out σ π)
    (dflt : α) (t : κ) (mx : G.Range t → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ) :
    Red.run1 dflt
        ((liftM ((unifSpec + G).query (.inr t)) : OracleComp (unifSpec + G) _) >>= mx) (f + 1) s =
      (Red.handlePre s (Red.qenc t) >>= fun res =>
        match res with
        | .inl (v, s') => Red.run1 dflt (mx (Red.rdec t v)) f s'
        | .inr (c, p, s') => pure (.paused t c p s' mx)) := by
  simp [BhShallowTwoStageRed.run1, construct_query_bind]

/-! ## Shallow E2E driver transitions and `KeyInd` reduction -/

def bhShallowStepStartU {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) (kU : KeyU) :
    Option ℕ × BHE2EDrvState S ℓ :=
  match bhE2EGuard σ sid with
  | none => (none, σ)
  | some (hdr, bnd, (u, j)) =>
    let idA := bhIdKeyOf hdr.ikAPk
    let idB := bhIdKeyOf bnd.ikB
    let spqr := LibsignalSpqrV1.spqrV1SessionUniformCoins C.F K
    let sch := sessionSchemeU (paramsIdsWithSpqr C spqr idA idB) ℓ
    let gs0 := SM.initState sch.sendPart kU σ.b
    let inst : BHModelInst S ℓ :=
      { sid, hdr, idA, idB, spkCoins := kU.2.1, gs := some gs0 }
    let im : ModelDriverInstanceMeta S :=
      { respPrin := some u, respSpkIdx := some j, instOpkId? := hdr.opkId? }
    (some σ.insts.length,
     { σ with insts := σ.insts ++ [inst], instMeta := σ.instMeta ++ [im] })

/-- Pre-query admissibility and PreKey header-stripping check for external session slot `k`. -/
def bhShallowCheckExtSm {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (i : ℕ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    BHTargetResp ℓ ⊕ (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain :=
  if i != k || !bhE2EDrvInstClean σ k then
    .inl (.inr (none, none, none))
  else
    match σ.insts[k]?, σ.instMeta[k]? with
    | some d, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
        .inl (.inr (none, none, none))
      else
        match sq with
        | .inl (.inl (.inr (.A, c))) =>
          if (bhDecodePreKeyMsgE c).isSome then
            .inl (.inr (none, none, none))
          else .inr sq
        | .inl (.inr (.A, c)) =>
          if (bhDecodePreKeyMsgE c).isSome then
            .inl (.inr (none, none, none))
          else .inr sq
        | .inl (.inl (.inr (.B, c))) =>
          if !im.bobAccepted then
            match bhDecodePreKeyMsgE c with
            | some m =>
              if c == wirePrekey ::
                  (bhExpectedPreKeyMsg (bhInitRegId d.sid) d.hdr m.inner).bytes then
                .inr (.inl (.inl (.inr (.B, m.inner))))
              else .inl (.inr (none, none, none))
            | none => .inl (.inr (none, none, none))
          else
            match bhDecodePreKeyMsgE c with
            | some m =>
              if bhHdrOfPreKeyMsg m == d.hdr then
                .inr (.inl (.inl (.inr (.B, m.inner))))
              else .inl (.inr (none, none, none))
            | none => .inr (.inl (.inl (.inr (.B, c))))
        | .inl (.inr (.B, c)) =>
          if !im.bobAccepted then
            .inl (.inr (none, none, none))
          else
            match bhDecodePreKeyMsgE c with
            | some m =>
              if bhHdrOfPreKeyMsg m == d.hdr && shortCiphertext c &&
                 decide (m.inner.length + 2048 < 2 ^ 32) then
                .inr (.inl (.inr (.B, m.inner)))
              else .inl (.inr (none, none, none))
            | none => .inr (.inl (.inr (.B, c)))
        | _ => .inr sq
    | _, _ => .inl (.inr (none, none, none))

/-- Post-query metadata update after forwarding a query to external session slot `k`. -/
def bhShallowCommitExtSm {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : ℕ) (σ : BHE2EDrvState S ℓ)
    (sq : (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (sr : BHE2ESmResp ℓ) : BHTargetResp ℓ × BHE2EDrvState S ℓ :=
  let σ1 :=
    if !bhE2EDrvInstClean σ k then σ
    else match σ.insts[k]?, σ.instMeta[k]? with
      | some d, some im =>
        if !im.bobAccepted && bhIsBobRecvSMQuery sq && bhE2EInstIkACorr σ d then
          { σ with instMeta :=
              σ.instMeta.set k { im with bobAccepted := true, ikACorrAtAccept := true } }
        else
          let r := bhUnpackSmResp sq sr
          let im' := if !im.bobAccepted && bhIsBobAcceptSMResp sq r then
              { im with bobAccepted := true, ikACorrAtAccept := bhE2EInstIkACorr σ d }
            else im
          { σ with instMeta := σ.instMeta.set k im' }
      | _, _ => σ
  (.inr sr, σ1)

def bhShallowStepPreNonCtl {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × BHE2EDrvState S ℓ) := do
  match q with
  | .inl (.inl kq) =>
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return (.inl (.inl .noneResp), σ)
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return (.inl (.inl .noneResp), σ)
    else
      let (kr, st') ← (ki kq).run σ.st
      return (.inl (.inl kr), bhE2EMirror { σ with st := st' } kq kr)
  | .inl (.inr _) => return (.inl (.inr none), σ)
  | .inr (i, sq) =>
    let (sr, σ') ← bhE2EStepLocalSm C K qep decT encT σ i sq
    return (.inr sr, σ')

def bhShallowStepPreCtl {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem)
    (k : ℕ) (σ : BHE2EDrvState S ℓ) (sid : SignalPqxdh.SessionId S) :
    ProbComp ((Option ℕ × BHE2EDrvState S ℓ) ⊕
      (BHPrefixCtx × (Option ℕ × BHE2EDrvState S ℓ))) := do
  let (idx?, σ') ← compositionLocalStart ki C K (some true) σ sid
  if k < σ'.insts.length then
    let ctx : BHPrefixCtx := match σ'.insts[k]? with
      | some d => { idA := d.idA, idB := d.idB, spkCoins := d.spkCoins }
      | none => { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
    let insts' := σ'.insts.mapIdx (fun i d => if i = k then { d with gs := none } else d)
    return .inr (ctx, (idx?, { σ' with insts := insts', paused := true }))
  else return .inl (idx?, σ')

def bhShallowStepPostLocal {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (σ : BHE2EDrvState S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    ProbComp (BHTargetResp ℓ × BHE2EDrvState S ℓ) := do
  match q with
  | .inl (.inl kq) =>
    if !bhDrvKiQueryOk P σ.toModelDriverBase kq then
      return (.inl (.inl .noneResp), σ)
    else if (match kq with | .corruptIK u => bhNoOpkRespPromoted σ.instMeta u | _ => false) then
      return (.inl (.inl .noneResp), σ)
    else
      let (kr, st') ← (ki kq).run σ.st
      return (.inl (.inl kr), bhE2EMirror { σ with st := st' } kq kr)
  | .inl (.inr sid) =>
    let (idx?, σ1) ← compositionLocalStart ki C K (some false) σ sid
    return (.inl (.inr idx?), σ1)
  | .inr (i, sq) =>
    let (sr, σ') ← bhE2EStepLocalSm C K qep decT encT σ i sq
    return (.inr sr, σ')

def bhShallowFinishPrefix {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (P : SignalPqxdh.Primitives) (σ : BHE2EDrvState S ℓ) (b' flip : Bool) :
    ProbComp Bool := do
  if !σ.paused then return false
  else if !allTestedSessionsFresh P σ.st then
    let coin ← ($ᵗ Bool : ProbComp Bool)
    return (coin ^^ flip)
  else
    let out := if bhE2EDrvWon σ true then true else if bhE2EDrvWon σ false then false else b'
    return (out ^^ flip)

def bhKindHandleWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (_ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (drv : BHE2EDrvState S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) (BHTargetResp ℓ × BHE2EDrvState S ℓ) :=
  match q with
  | .inl (.inl kq) =>
    if bhDrvKiQueryOk P drv.toModelDriverBase kq &&
        !(match kq with | .corruptIK u => bhNoOpkRespPromoted drv.instMeta u | _ => false) then do
      let kr ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      return (.inl (.inl kr), bhE2EMirror drv kq kr)
    else
      pure (.inl (.inl .noneResp), drv)
  | .inl (.inr sid) =>
    match (bhE2EGuard drv sid).map (fun (_, _, uj) => uj) with
    | none => pure (.inl (.inr none), drv)
    | some (u, j) => do
      let ts ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.testSession sid))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let sk ← (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr (.revealSpkSk u j))) :
        OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _)
      let bv ← bhLiftP (G := SignalPqxdh.keyIndSpec S) ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      let fin := bhE2EFinishStartSpk C K (some drv.b) drv sid ts sk bv
      return (.inl (.inr fin.1), fin.2)
  | .inr (i, sq) => do
    let res ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (bhE2EStepLocalSm C K qep decT encT drv i sq)
    return (.inr res.1, res.2)

/-- Shallow 1-stage `KeyInd` reference reduction `bhKindRedWith`. -/
def bhKindRedWith {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    BhShallowRed (bhTargetGameSpec S ℓ (BitVec 512))
      (unifSpec + SignalPqxdh.keyIndSpec S)
      Unit Bool Unit Bool (BHE2EDrvState S ℓ) where
  init _ := do
    let drv ← bhLiftP (G := SignalPqxdh.keyIndSpec S)
      (do let b ← ($ᵗ Bool : ProbComp Bool); return ({ b := b } : BHE2EDrvState S ℓ))
    return ((), drv)
  impl := bhShallowImplOfHandle bhTargetQenc bhTargetRdec
    (bhKindHandleWith P ki C K qep decT encT)
  finish drv aOut := pure (aOut == drv.b || bhE2EDrvWon drv drv.b)

/-! ## Binary-harness wire and state adapter -/

/-- State of the shallow binary-harness adapter `L_bh`: per-instance metadata table, Alice
acknowledgement flags, and public `KeyInd` transcript mirror. -/
abbrev CliAdapterState (S : SignalPqxdh.Setup) : Type :=
  (ℕ → Option (BHAdapterInstMeta S)) × (ℕ → Bool) × ModelDriverBase S

def cliAdapterInitState (S : SignalPqxdh.Setup) : CliAdapterState S :=
  (fun _ => none, (fun _ => false, {}))

def bhShallowWrapWhisper (ct : Bytes) : Bytes :=
  if ct.isEmpty then [] else wireWhisper :: ct

def bhShallowSplitWhisper : Bytes → Option Bytes
  | t :: body => if t == wireWhisper then some body else none
  | [] => none

def bhShallowParsePreKey (c : Bytes) : Option (SignalPqxdh.HandshakeHdr × Bytes) :=
  (bhDecodePreKeyMsgE c).map (fun m => (bhHdrOfPreKeyMsg m, m.inner))

def bhShallowStepMirrorGuard {S : SignalPqxdh.Setup} :
    ((ModelDriverBase S × (SignalPqxdh.KeyIndQuery S × SignalPqxdh.KeyIndResponse)) ⊕
      (ModelDriverBase S × SignalPqxdh.SessionId S)) →
    ModelDriverBase S × Option (BHAdapterInstMeta S)
  | .inl (drv, (kq, kr)) => (bhBaseMirror drv kq kr, none)
  | .inr (drv, sid) =>
    match drv.sends.find? (fun (s, _, _) => s == sid) with
    | none => (drv, none)
    | some (_, bnd, hdr) =>
      match drv.bundles.find? (fun ((_, j), (spkB, pqspkB)) =>
          spkB == bnd.spkB && pqspkB == bnd.pqspkB &&
          hdr.spkId == UInt32.ofNat j.val &&
          hdr.pqspkId == UInt32.ofNat j.val) with
      | none => (drv, none)
      | some ((u_resp, j_resp), _) =>
        if drv.prins.any (fun (u', pk) => u' == u_resp && pk == bnd.ikB) &&
           bhBaseOpkOk drv u_resp j_resp bnd then
          let regIdA : BitVec 32 := bhInitRegId sid
          (drv, some { sid := sid, u_resp := u_resp, hdr := hdr, idB := bnd.ikB,
                       bobRemoteRegId := regIdA })
        else (drv, none)

def bhShallowUpdateInstMeta {S : SignalPqxdh.Setup}
    (inst : BHAdapterInstMeta S) (setAck setAcc : Bool) (c : Bytes) :
    Bool × BHAdapterInstMeta S :=
  let regId' :=
    match bhDecodePreKeyMsgE c with | some m => m.regId | none => inst.bobRemoteRegId
  let eqHdr := match bhDecodePreKeyMsgE c with
    | some m =>
      if !inst.bobAccepted then
        c == wirePrekey :: (bhExpectedPreKeyMsg (bhInitRegId inst.sid) inst.hdr m.inner).bytes
      else bhHdrOfPreKeyMsg m == inst.hdr
    | none => false
  (eqHdr, { inst with aliceAcked := inst.aliceAcked || setAck,
                      bobAccepted := inst.bobAccepted || setAcc,
                      bobRemoteRegId := if !inst.bobAccepted && setAcc then regId'
                                        else inst.bobRemoteRegId })

def bhShallowBobUpdate {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : CliAdapterState S) (i : ℕ) (inst : BHAdapterInstMeta S) (c : Bytes)
    (optRr : Option (SM.RecvResult (Plain ℓ))) : CliAdapterState S :=
  match optRr with
  | some (.accepted _ _ _) =>
    let inst' := (bhShallowUpdateInstMeta inst false true c).2
    ((fun j => if j = i then some inst' else σ.1 j), σ.2)
  | _ => σ

def bhShallowAliceUpdate {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : CliAdapterState S) (i : ℕ)
    (optRr : Option (SM.RecvResult (Plain ℓ))) : CliAdapterState S :=
  match optRr with
  | some (.accepted _ _ _) =>
    (σ.1, ((fun j => if j = i then true else σ.2.1 j), σ.2.2))
  | _ => σ

def bhShallowQueryTarget {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (q : (bhTargetGameSpec S ℓ PQC).Domain) :
    OracleComp (unifSpec + bhTargetGameSpec S ℓ PQC) ((bhTargetGameSpec S ℓ PQC).Range q) :=
  (liftM ((unifSpec + bhTargetGameSpec S ℓ PQC).query (.inr q)) :
    OracleComp (unifSpec + bhTargetGameSpec S ℓ PQC) _)

/-- Single game-query handler of the shallow adapter `L_bh`. -/
def bhShallowAdapterGameStep {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC : Type}
    (t : (bhGameSpec S ℓ PQC).Domain) (σ : CliAdapterState S) :
    OracleComp (unifSpec + bhTargetGameSpec S ℓ PQC)
      ((bhGameSpec S ℓ PQC).Range t × CliAdapterState S) :=
  match t with
  | .inl (.inl kq) => do
    let kr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC) (.inl (.inl kq))
    let drv' := (bhShallowStepMirrorGuard (.inl (σ.2.2, (kq, kr)))).1
    return (kr, (σ.1, (σ.2.1, drv')))
  | .inl (.inr (.startDR sid)) => do
    let optIdx ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC) (.inl (.inr (.startDR sid)))
    match optIdx with
    | none => return (none, σ)
    | some idx =>
      match (bhShallowStepMirrorGuard (.inr (σ.2.2, sid))).2 with
      | none => return (some idx, σ)
      | some inst =>
        return (some idx, ((fun j => if j = idx then some inst else σ.1 j), σ.2))
  | .inr ⟨instIdx, .inl (.inl (.inl (.inl (p, m, r))))⟩ =>
    match σ.1 instIdx with
    | none => pure (none, σ)
    | some inst => do
      let optCt ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
        (.inr ⟨instIdx, .inl (.inl (.inl (.inl (p, m, r))))⟩)
      match optCt with
      | none => return (none, σ)
      | some ct =>
        let wire :=
          if SM.partyEnc p then bhShallowWrapWhisper ct
          else if σ.2.1 instIdx then bhShallowWrapWhisper ct
          else bhWrapSendOut inst .A ct
        return (some wire, σ)
  | .inr ⟨instIdx, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩ =>
    match σ.1 instIdx with
    | none => pure (none, σ)
    | some inst => do
      let optCt ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
        (.inr ⟨instIdx, .inl (.inl (.inl (.inr (p, m0, m1, r))))⟩)
      match optCt with
      | none => return (none, σ)
      | some ct =>
        let wire :=
          if SM.partyEnc p then bhShallowWrapWhisper ct
          else if σ.2.1 instIdx then bhShallowWrapWhisper ct
          else bhWrapSendOut inst .A ct
        return (some wire, σ)
  | .inr ⟨instIdx, .inl (.inl (.inr (.B, c)))⟩ =>
    match σ.1 instIdx with
    | none => pure (none, σ)
    | some inst =>
      match bhShallowParsePreKey c with
      | none =>
        match bhShallowSplitWhisper c with
        | none => do
          let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
          return (none, σ)
        | some body =>
          match bhShallowParsePreKey body with
          | none =>
            match bhShallowSplitWhisper (bhShallowWrapWhisper body) with
            | none => do
              let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
                (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper body))⟩)
              return (none, σ)
            | some _ => do
              let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
                (.inr ⟨instIdx, .inl (.inl (.inr (.B, body)))⟩)
              return (optRr, σ)
          | some _ => do
            let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.B, c))⟩)
            return (none, σ)
      | some hdr_inner =>
        match bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) with
        | none => do
          let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper hdr_inner.2))⟩)
          return (none, σ)
        | some _ => do
          let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inl (.inr (.B, c)))⟩)
          return (optRr, bhShallowBobUpdate σ instIdx inst c optRr)
  | .inr ⟨instIdx, .inl (.inl (.inr (.A, c)))⟩ =>
    match bhShallowSplitWhisper c with
    | none =>
      match bhShallowSplitWhisper (bhShallowWrapWhisper c) with
      | none => do
        let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
          (.inr ⟨instIdx, .inl (.inl (.inr (.A, c)))⟩)
        return (optRr, σ)
      | some _ => pure (none, σ)
    | some body =>
      match bhShallowSplitWhisper (bhShallowWrapWhisper body) with
      | none => pure (none, σ)
      | some body' => do
        let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
          (.inr ⟨instIdx, .inl (.inl (.inr (.A, body')))⟩)
        return (optRr, bhShallowAliceUpdate σ instIdx optRr)
  | .inr ⟨instIdx, .inl (.inr (.B, c))⟩ =>
    match bhShallowSplitWhisper c with
    | none =>
      match bhShallowParsePreKey c with
      | none => do
        let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
          (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
        return (none, σ)
      | some hdr_inner =>
        if decide (c.length ≤ stdinCapBytes) && shortCiphertext c &&
            decide (hdr_inner.2.length + 2048 < 2 ^ 32) then
          match σ.1 instIdx with
          | none => do
            let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.B, c))⟩)
            return (optRr, σ)
          | some inst =>
            match bhShallowSplitWhisper (bhShallowWrapWhisper hdr_inner.2) with
            | none =>
              if (bhShallowUpdateInstMeta inst false false c).1 then do
                let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
                  (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
                return (optRr, σ)
              else do
                let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
                  (.inr ⟨instIdx, .inl (.inr (.B, c))⟩)
                return (optRr, σ)
            | some _ => do
              let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
                (.inr ⟨instIdx, .inl (.inr (.B, c))⟩)
              return (optRr, σ)
        else do
          let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
          return (none, σ)
    | some body =>
      if decide (c.length ≤ stdinCapBytes) && shortCiphertext c then
        match bhShallowParsePreKey body with
        | none =>
          match bhShallowSplitWhisper (bhShallowWrapWhisper body) with
          | none => do
            let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
            return (optRr, σ)
          | some body' => do
            let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.B, body'))⟩)
            return (optRr, σ)
        | some _ => do
          let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper body))⟩)
          return (optRr, σ)
      else do
        let _ ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
          (.inr ⟨instIdx, .inl (.inr (.B, bhShallowWrapWhisper c))⟩)
        return (none, σ)
  | .inr ⟨instIdx, .inl (.inr (.A, c))⟩ =>
    match bhShallowSplitWhisper c with
    | none => pure (none, σ)
    | some body =>
      if decide (c.length ≤ stdinCapBytes) && shortCiphertext c then
        match bhShallowParsePreKey body with
        | none =>
          match bhShallowSplitWhisper (bhShallowWrapWhisper body) with
          | none => do
            let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.A, bhShallowWrapWhisper c))⟩)
            return (optRr, σ)
          | some body' => do
            let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
              (.inr ⟨instIdx, .inl (.inr (.A, body'))⟩)
            return (optRr, bhShallowAliceUpdate σ instIdx optRr)
        | some _ => do
          let optRr ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC)
            (.inr ⟨instIdx, .inl (.inr (.A, bhShallowWrapWhisper body))⟩)
          return (optRr, bhShallowAliceUpdate σ instIdx optRr)
      else pure (none, σ)
  | .inr ⟨instIdx, .inr p⟩ =>
    match σ.1 instIdx with
    | none => pure (none, σ)
    | some inst => do
      let optG ← bhShallowQueryTarget (S := S) (ℓ := ℓ) (PQC := PQC) (.inr ⟨instIdx, .inr p⟩)
      match optG with
      | none => return (none, σ)
      | some g => return (some (bhBinStateOfParty inst g), σ)

def bhShallowAdapterImpl (S : SignalPqxdh.Setup) (ℓ : ℕ) (PQC : Type) :
    QueryImpl (unifSpec + bhGameSpec S ℓ PQC)
      (StateT (CliAdapterState S) (OracleComp (unifSpec + bhTargetGameSpec S ℓ PQC)))
  | .inl n => StateT.mk fun σ => do
    let u ← bhFwdU (G := bhTargetGameSpec S ℓ PQC) n
    return (u, σ)
  | .inr t => StateT.mk fun σ => bhShallowAdapterGameStep t σ

/-- Shallow reference wire/state adapter `L_bh` from `bhGameSpec` to `bhTargetGameSpec`. -/
def L_bh {S : SignalPqxdh.Setup} {ℓ : ℕ} {PQC Pt : Type}
    (_decT : PublicKey → Option Pt) (_encT : Pt → PublicKey) :
    BhShallowRed (bhGameSpec S ℓ PQC) (unifSpec + bhTargetGameSpec S ℓ PQC)
      Unit Bool Unit Bool (CliAdapterState S) where
  init _ := pure ((), cliAdapterInitState S)
  impl := bhShallowAdapterImpl S ℓ PQC
  finish _ out := pure out

end CryptoVerification.E2E

namespace CryptoVerification.E2E.Prefix1Key

open CryptoVerification.E2E

def bhPrefixHandlePreWith (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (drv : BHE2EDrvState S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      ((BHTargetResp ℓ × BHE2EDrvState S ℓ) ⊕
        (BHPrefixCtx × (Option ℕ × BHE2EDrvState S ℓ))) :=
  match q with
  | .inl (.inl kq) => do
    let res ← bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtl P ki C K qep decT encT drv (.inl (.inl kq)))
    return .inl res
  | .inl (.inr sid) => do
    let res ← bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreCtl ki C K k drv sid)
    match res with
    | .inl ans => return .inl (.inl (.inr ans.1), ans.2)
    | .inr ctxAndDrv => return .inr ctxAndDrv
  | .inr iSq => do
    let res ← bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPreNonCtl P ki C K qep decT encT drv (.inr iSq))
    return .inl res

def bhPrefixHandlePostWith (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ)
    (drv : BHE2EDrvState S ℓ) (q : BHTargetQuery S ℓ (BitVec 512)) :
    OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetResp ℓ × BHE2EDrvState S ℓ) :=
  match q with
  | .inl kiOrCtl =>
    bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowStepPostLocal P ki C K qep decT encT drv (.inl kiOrCtl))
  | .inr (i, sq) =>
    match bhShallowCheckExtSm k drv i sq with
    | .inl _ =>
      bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
        (bhShallowStepPostLocal P ki C K qep decT encT drv (.inr (i, sq)))
    | .inr sq' => do
      let r ← (liftM
        ((unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).query (.inr sq')) :
        OracleComp (unifSpec + SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) _)
      return bhShallowCommitExtSm k drv sq' (bhPackSmResp sq' r)

/-- Shallow 2-stage prefix reference reduction `bhPrefixRedWith`. -/
def bhPrefixRedWith (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (k : ℕ) :
    BhShallowTwoStageRed (bhTargetGameSpec S ℓ (BitVec 512))
      (SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (BHTargetQuery S ℓ (BitVec 512)) (BHTargetResp ℓ)
      Unit Unit Bool BHPrefixCtx Bool Bool (BHE2EDrvState S ℓ) (Option ℕ) where
  qenc := bhTargetQenc
  rdec := bhTargetRdec
  init _ := pure ((), {})
  handlePre := bhPrefixHandlePreWith S ℓ P ki C K qep decT encT k
  chDone _ _ := pure { idA := bhIdKeyOf [], idB := bhIdKeyOf [], spkCoins := 0 }
  resume σ p flip := pure (.inl (.inr p), { σ with b := flip })
  handlePost := bhPrefixHandlePostWith S ℓ P ki C K qep decT encT k
  finish σ b' flip :=
    bhLiftP (G := SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (bhShallowFinishPrefix P σ b' flip)

end CryptoVerification.E2E.Prefix1Key
