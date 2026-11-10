/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SpecLemmas.Game.BhShallowHelpers -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1 -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.AtomicTablesHonest -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness

/-!
# Two-Stage Simulation Equivalence for Atomic Prefix Reductions

Proves Stage-1, Stage-2, and full two-stage experiment equivalence (`twoStage_stage12_comp_eq`,
`evalDist_twoStage_stage12_eq`) between any costed two-stage reduction over `atomicSig ℓ Pt` and
a shallow `BhShallowTwoStageRed` reference runner under `TwoStageAtomicSimSpec`.
-/

public section

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface GameCodec Env Expr Comp Mid TwoStageCostedReduction
  runFuel atomicSig e2eSessionTargetIface prefixCtxT keyIndRdec pqKeyIndRenc
  keyIndRdec_pqKeyIndRenc smRT smRdec recvResultEnc recvResultDec GhostStT)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (IdentityKey GhostState)
open CryptoVerification.E2E (Bytes BHE2ESmResp BHTargetQuery BHTargetResp BHPrefixCtx
  bhTargetGameSpec e2eTargetGameCodec bhTargetQenc bhTargetRdec bhFwdU bhLiftP
  BhShallowTwoStageRed bhShallowRunFuel bhShallowRunFuel_pure bhShallowRunFuel_query_inl
  bhShallowRunFuel_query_inr_zero bhShallowRunFuel_query_inr_succ bhUnpackSmResp
  stageOneAsProbComp isSmTargetQuery bhClassifyTarget bhClassifyTargetOnly)

/-! ## Codec round-trips and support helpers -/

@[simp] private theorem recvResultDec_recvResultEnc {ℓ : ℕ} {Pt : Type}
    (rr : CryptoGames.SM.RecvResult (Plain ℓ)) :
    recvResultDec (ℓ := ℓ) (Pt := Pt) (recvResultEnc rr) = rr := by
  cases rr <;> rfl

@[expose] def packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type} (br : BHE2ESmResp ℓ) :
    (smRT (ℓ := ℓ) (Pt := Pt) GhostStT).denote :=
  (br.1, (br.2.1.map recvResultEnc, br.2.2))

@[simp] theorem smRdec_id_packAtomicSmRespEnc {ℓ : ℕ} {Pt : Type}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (br : BHE2ESmResp ℓ) :
    smRdec (ℓ := ℓ) (Pt := Pt) (stT := GhostStT) id sq (packAtomicSmRespEnc br) =
      bhUnpackSmResp sq br := by
  rcases br with ⟨w, rr?, st?⟩
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases rr? <;> simp [packAtomicSmRespEnc, smRdec, bhUnpackSmResp]
  · cases st? <;> rfl

@[expose] def atomicGameRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type} :
    BHTargetResp ℓ → (e2eTargetGameCodec S ℓ Pt).R.denote
  | .inl (.inl kr) => .inl (.inl (pqKeyIndRenc kr))
  | .inl (.inr idx?) => .inl (.inr idx?)
  | .inr sr => .inr (packAtomicSmRespEnc sr)

@[simp] theorem e2eTargetGameCodec_rdec_atomicGameRespEnc {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {Pt : Type} (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (r : BHTargetResp ℓ) :
    (e2eTargetGameCodec S ℓ Pt).rdec t (atomicGameRespEnc (S := S) (Pt := Pt) r) =
      bhTargetRdec t r := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · rcases r with (kr | idx?) | sr
    · exact keyIndRdec_pqKeyIndRenc kr
    · rfl
    · rfl
  · rcases cq with ⟨sid⟩
    rcases r with (kr | idx?) | sr <;> rfl
  · rcases r with (kr | idx?) | sr
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · rcases sq with (((_ | _) | _) | _) | _ <;> rfl
    · exact smRdec_id_packAtomicSmRespEnc sq sr

@[expose] def atomicPrefixCtxEnc {ℓ : ℕ} {Pt : Type} (c : BHPrefixCtx) :
    (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote :=
  (c.idA, (c.idB, c.spkCoins))

@[simp] theorem atomicSessionTargetIface_fwdU_eq_bhFwdU {ℓ : ℕ} {Pt : Type}
    (n : unifSpec.Domain) :
    (e2eSessionTargetIface ℓ Pt).fwdU n = bhFwdU n := rfl

@[simp] theorem atomicSessionTargetIface_liftP_eq_bhLiftP {ℓ : ℕ} {Pt : Type}
    {α : Type} (p : ProbComp α) :
    (e2eSessionTargetIface ℓ Pt).liftP p = bhLiftP p := rfl

theorem mem_support_of_atomicSessionLiftP {ℓ : ℕ} {Pt α : Type} (p : ProbComp α) {x : α}
    (hx : x ∈ support ((e2eSessionTargetIface ℓ Pt).liftP p)) : x ∈ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa [Iface.liftP] using hx
  | query_bind n mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, mem_support_bind_iff] at hx ⊢
    rcases hx with ⟨v, -, hxv⟩
    exact ⟨v, mem_support_query n v, ih v hxv⟩

theorem mem_support_of_mem_support_stageOneAsProbComp {ℓ : ℕ} {α : Type}
    (oa : OracleComp
      (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α)
    {x : α} (hx : x ∈ support (stageOneAsProbComp oa))
    (hq0 : oa.IsQueryBoundP (isSmTargetQuery ℓ) 0) :
    x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [stageOneAsProbComp] using hx
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hq0
    cases q with
    | inl n =>
      unfold stageOneAsProbComp at hx
      rw [simulateQ_query_bind] at hx
      change x ∈ support (liftM (query (spec := unifSpec) n) >>=
        fun u => stageOneAsProbComp (mx u)) at hx
      rw [mem_support_bind_iff] at hx ⊢
      rcases hx with ⟨u, -, hxu⟩
      exact ⟨u, mem_support_query (spec := unifSpec +
          CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) (Sum.inl n) u,
        ih u hxu ((hq0.2 u).mono (by simp [isSmTargetQuery]))⟩
    | inr sq =>
      exfalso
      rcases hq0.1 with hfalse | hlt
      · simp [isSmTargetQuery] at hfalse
      · omega

private theorem run1_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (pure a) f s = pure (.done a s) := by
  simp only [TwoStageCostedReduction.run1, construct_pure]

private theorem run1_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => R.run1 dflt (mx u) f s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (.done dflt s) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]

private theorem run1_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {rIn aIn aOut ch rIn2 out : Ty S0}
    (R : TwoStageCostedReduction O I G C0 rIn aIn aOut ch rIn2 out)
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : R.σ.denote) :
    R.run1 dflt (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (R.handlePre.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun res =>
        match res with
        | .inl (v, s') => R.run1 dflt (mx (C0.rdec t v)) f s'
        | .inr (c, p, s') => pure (.paused t c p s' mx)) := by
  simp only [TwoStageCostedReduction.run1, construct_query_bind]
  refine bind_congr fun res => ?_
  rcases res with ⟨v, s'⟩ | ⟨c, p, s'⟩ <;> rfl

private theorem runFuel_pure {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (a : α) (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt (pure a) f s = pure (a, s) := by
  simp only [runFuel, construct_pure]

private theorem runFuel_query_inl {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (n : ℕ)
    (mx : (unifSpec + G).Range (.inl n) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= mx) f s =
      (I.fwdU n >>= fun u => runFuel (C := C0) h dflt (mx u) f s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_zero {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) 0 s =
      pure (dflt, s) := by
  simp only [runFuel, construct_query_bind]

private theorem runFuel_query_inr_succ {S0 : Sig} {ι : Type} {T : OracleSpec ι}
    {O : Ops S0} {I : Iface S0 T} {κ : Type} {G : OracleSpec κ} {C0 : GameCodec S0 G}
    {σ : Ty S0} (h : Comp O I [σ, C0.Q] (.prod C0.R σ))
    {α : Type} (dflt : α) (t : κ)
    (mx : (unifSpec + G).Range (.inr t) → OracleComp (unifSpec + G) α)
    (f : ℕ) (s : σ.denote) :
    runFuel (C := C0) h dflt
      (liftM (OracleSpec.query (spec := unifSpec + G) (.inr t)) >>= mx) (f + 1) s =
      (h.eval (.cons s (.cons (C0.qenc t) .nil)) >>= fun p =>
        runFuel (C := C0) h dflt (mx (C0.rdec t p.1)) f p.2) := by
  simp only [runFuel, construct_query_bind]

private theorem isQueryBoundP_atomicSessionTargetIface_fwdU {ℓ : ℕ} {Pt : Type} (n : ℕ) :
    ((e2eSessionTargetIface ℓ Pt).fwdU n).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
  dsimp only [e2eSessionTargetIface]
  exact (OracleComp.isQueryBoundP_query_iff _ _ _).2 (by simp [isSmTargetQuery])

/-! ## Simulation specification -/

@[expose] def StepBudgetOk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (b : SignalPqxdh.QueryBudget) (qStart qDR qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) : Prop :=
  match t with
  | .inl (.inl _) => qKiDone + 1 ≤ b.q_total
  | .inl (.inr _) => qStartDone + 1 ≤ qStart
  | .inr _ => qDrDone + 1 ≤ qDR

@[expose] def StepNextInv {S : SignalPqxdh.Setup} {ℓ : ℕ} {DrvSt : Type}
    (Inv : ℕ → ℕ → ℕ → DrvSt → Prop)
    (qKiDone qStartDone qDrDone : ℕ)
    (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) (σ1 : DrvSt) : Prop :=
  match t with
  | .inl (.inl _) => Inv (qKiDone + 1) qStartDone qDrDone σ1
  | .inl (.inr _) => Inv qKiDone (qStartDone + 1) qDrDone σ1
  | .inr _ => Inv qKiDone qStartDone (qDrDone + 1) σ1

/-- Per-category query bounds on an adversary `B_A` over `unifSpec + bhTargetGameSpec`. -/
structure TargetAdvBounded (S : SignalPqxdh.Setup) {ℓ : ℕ}
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) : Prop where
  tot : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
    b.q_total
  start : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
    qStart
  dr : B_A.IsQueryBoundP
    (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
    qDR

@[expose] def mapPreEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt DrvSt π_ref σ_den π_den : Type}
    (drvEnc : DrvSt → σ_den) (πEnc : π_ref → π_den) :
    (BHTargetResp ℓ × DrvSt) ⊕ (BHPrefixCtx × π_ref × DrvSt) →
    ((e2eTargetGameCodec S ℓ Pt).R.denote × σ_den) ⊕
      ((prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote × π_den × σ_den)
  | .inl (r, σ1) => .inl (atomicGameRespEnc r, drvEnc σ1)
  | .inr (c, p, σ1) => .inr (atomicPrefixCtxEnc c, πEnc p, drvEnc σ1)

@[expose] def mapMidEnc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α DrvSt π_ref σ_den π_den : Type}
    (drvEnc : DrvSt → σ_den) (πEnc : π_ref → π_den) :
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) α π_ref DrvSt BHPrefixCtx →
    Mid (bhTargetGameSpec S ℓ (BitVec 512)) α π_den σ_den
      (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote
  | .done a σ => .done a (drvEnc σ)
  | .paused t c p σ cont => .paused t (atomicPrefixCtxEnc c) (πEnc p) (drvEnc σ) cont

@[expose] def mapOut1Enc {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt α DrvSt π_ref σ_den π_den : Type}
    (drvEnc : DrvSt → σ_den) (πEnc : π_ref → π_den)
    (o : BHPrefixCtx × Mid (bhTargetGameSpec S ℓ (BitVec 512)) α π_ref DrvSt BHPrefixCtx) :
    (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote ×
      Mid (bhTargetGameSpec S ℓ (BitVec 512)) α π_den σ_den
        (prefixCtxT (ℓ := ℓ) (Pt := Pt)).denote :=
  (atomicPrefixCtxEnc o.1, mapMidEnc drvEnc πEnc o.2)

/-- Step-level simulation contract between a costed two-stage reduction over `atomicSig ℓ Pt` and
a `BhShallowTwoStageRed` reference reduction. -/
structure TwoStageAtomicSimSpec (S : SignalPqxdh.Setup) (Pt : Type) (ℓ : ℕ)
    (O : Ops (atomicSig ℓ Pt))
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) (DrvSt π_ref : Type) where
  R : TwoStageCostedReduction O (e2eSessionTargetIface ℓ Pt)
    (bhTargetGameSpec S ℓ (BitVec 512)) (e2eTargetGameCodec S ℓ Pt)
    .unit .unit .bool (prefixCtxT (ℓ := ℓ) (Pt := Pt)) .bool .bool
  R_ref : BhShallowTwoStageRed
    (bhTargetGameSpec S ℓ (BitVec 512))
    (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (BHTargetQuery S ℓ (BitVec 512)) (BHTargetResp ℓ)
    Unit Unit Bool BHPrefixCtx Bool Bool DrvSt π_ref
  drvEnc : DrvSt → R.σ.denote
  πEnc : π_ref → R.π.denote
  σ0 : DrvSt
  Inv : ℕ → ℕ → ℕ → DrvSt → Prop
  PausedInv : DrvSt → Prop
  qenc_eq : ∀ t, R_ref.qenc t = bhTargetQenc t
  rdec_eq : ∀ t r, R_ref.rdec t r = bhTargetRdec t r
  stage1_queries_zero :
    R.init.queries (fun _ => 1) (fun _ => 0) +
      R.handlePre.queries (fun _ => 1) (fun _ => 0) +
      R.chDone.queries (fun _ => 1) (fun _ => 0) = 0
  init_inv : Inv 0 0 0 σ0
  init_costed : R.init.eval (.cons () .nil) = pure ((), drvEnc σ0)
  init_ref : R_ref.init () = pure ((), σ0)
  chDone_eq : ∀ {qKi1 qSt1 qDr1 : ℕ} {σ_out : DrvSt},
    Inv qKi1 qSt1 qDr1 σ_out →
    ∀ b_out : Bool,
      R.chDone.eval (.cons (drvEnc σ_out) (.cons b_out .nil)) =
        atomicPrefixCtxEnc <$> R_ref.chDone σ_out b_out
  resume_eq : ∀ {qKi1 qSt1 qDr1 : ℕ} {σ_p : DrvSt},
    Inv qKi1 qSt1 qDr1 σ_p → PausedInv σ_p →
    ∀ (p : π_ref) (flip : Bool),
      R.resume.eval (.cons (drvEnc σ_p) (.cons (πEnc p) (.cons flip .nil))) =
        Prod.map atomicGameRespEnc drvEnc <$> R_ref.resume σ_p p flip
  resume_inv : ∀ {qKi1 qSt1 qDr1 : ℕ} {σ_p : DrvSt},
    Inv qKi1 qSt1 qDr1 σ_p → PausedInv σ_p →
    ∀ (p : π_ref) (flip : Bool),
      ∀ rs ∈ support (R_ref.resume σ_p p flip),
        Inv qKi1 qSt1 qDr1 rs.2 ∧ PausedInv rs.2
  stepPre_eq : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      R.handlePre.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        mapPreEnc drvEnc πEnc <$> R_ref.handlePre σ (bhTargetQenc t)
  stepPre_inv : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      ∀ res ∈ support (R_ref.handlePre σ (bhTargetQenc t)),
        match res with
        | .inl (_, σ1) => StepNextInv Inv qKiDone qStartDone qDrDone t σ1
        | .inr (_, _, σ1) =>
          (∃ cq, t = .inl (.inr cq)) ∧
          Inv qKiDone (qStartDone + 1) qDrDone σ1 ∧
          PausedInv σ1
  stepPost_eq : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ → PausedInv σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      R.handlePost.eval (.cons (drvEnc σ) (.cons ((e2eTargetGameCodec S ℓ Pt).qenc t) .nil)) =
        Prod.map atomicGameRespEnc drvEnc <$> R_ref.handlePost σ (bhTargetQenc t)
  stepPost_inv : ∀ {qKiDone qStartDone qDrDone : ℕ} {σ : DrvSt},
    Inv qKiDone qStartDone qDrDone σ → PausedInv σ →
    ∀ t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain,
      StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t →
      ∀ p ∈ support (R_ref.handlePost σ (bhTargetQenc t)),
        PausedInv p.2 ∧ StepNextInv Inv qKiDone qStartDone qDrDone t p.2
  finish_eq : ∀ {qKi2 qSt2 qDr2 : ℕ} {σ_out : DrvSt},
    Inv qKi2 qSt2 qDr2 σ_out →
    ∀ (b_out flip : Bool),
      R.finish.eval (.cons (drvEnc σ_out) (.cons b_out (.cons flip .nil))) =
        R_ref.finish σ_out b_out flip

/-! ## Stage-1, Stage-2, and experiment equivalence -/

section SimProofs

variable {S : SignalPqxdh.Setup} {Pt : Type} {ℓ : ℕ}
  {O : Ops (atomicSig ℓ Pt)}
  {b : SignalPqxdh.QueryBudget} {qStart qDR : ℕ} {DrvSt π_ref : Type}

theorem twoStage_run1_eq_and_inv
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    {α : Type} (dflt : α) :
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ)
      (σ : DrvSt),
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
        qKiRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStartRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
        qDrRem →
      qKiDone + qKiRem ≤ b.q_total →
      qStartDone + qStartRem ≤ qStart →
      qDrDone + qDrRem ≤ qDR →
      spec.Inv qKiDone qStartDone qDrDone σ →
      (spec.R.run1 dflt oa fuel (spec.drvEnc σ) =
        mapMidEnc spec.drvEnc spec.πEnc <$> spec.R_ref.run1 dflt oa fuel σ) ∧
      (∀ m ∈ support (spec.R_ref.run1 dflt oa fuel σ),
        match m with
        | .done _ σ_out =>
          ∃ qKi1 qSt1 qDr1, spec.Inv qKi1 qSt1 qDr1 σ_out
        | .paused _ _ _ σ_p cont =>
          ∃ qKi1 qKiR1 qSt1 qStR1 qDr1 qDrR1,
            qKi1 + qKiR1 ≤ b.q_total ∧
            qSt1 + qStR1 ≤ qStart ∧
            qDr1 + qDrR1 ≤ qDR ∧
            spec.Inv qKi1 qSt1 qDr1 σ_p ∧
            spec.PausedInv σ_p ∧
            ∀ v,
              (cont v).IsQueryBoundP
                (fun q =>
                  bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
                qKiR1 ∧
              (cont v).IsQueryBoundP
                (fun q =>
                  bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
                qStR1 ∧
              (cont v).IsQueryBoundP
                (fun q =>
                  bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
                qDrR1) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      _ _ _ _ _ _ hInv
    refine ⟨by rw [run1_pure, BhShallowTwoStageRed.run1_pure, map_pure]; rfl, ?_⟩
    intro m hm
    rw [BhShallowTwoStageRed.run1_pure] at hm
    simp only [support_pure, Set.mem_singleton_iff] at hm
    subst hm
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      hTot hStart hDr hqKi hqSt hqDr hInv
    rw [isQueryBoundP_query_bind_iff] at hTot hStart hDr
    cases q with
    | inl n =>
      have hContTot : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
          qKiRem := fun u => (hTot.2 u).mono (by simp [bhClassifyTarget])
      have hContSt : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          qStartRem := fun u => (hStart.2 u).mono (by simp [bhClassifyTarget])
      have hContDr : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
          qDrRem := fun u => (hDr.2 u).mono (by simp [bhClassifyTarget])
      refine ⟨?_, ?_⟩
      · rw [run1_query_inl, BhShallowTwoStageRed.run1_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
            (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv).1
      · intro m hm
        rw [BhShallowTwoStageRed.run1_query_inl, mem_support_bind_iff] at hm
        rcases hm with ⟨u, -, hmu⟩
        exact (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv).2 m hmu
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [run1_query_inr_zero, BhShallowTwoStageRed.run1_query_inr_zero, map_pure]; rfl,
          ?_⟩
        intro m hm
        rw [BhShallowTwoStageRed.run1_query_inr_zero] at hm
        simp only [support_pure, Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
      | succ f =>
        have htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t := by
          rcases ht : t with (kq | cq) | ⟨i, sq⟩
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
        have hStepEq := spec.stepPre_eq hInv t htBound
        have hResInv := spec.stepPre_inv hInv t htBound
        refine ⟨?_, ?_⟩
        · rw [run1_query_inr_succ, BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun res hres => ?_
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · dsimp only [mapPreEnc]
            have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
            dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
            rw [hAns, spec.rdec_eq t r_ans]
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hpos : 0 < qKiRem :=
                hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                (by omega) hqSt hqDr hR).1
            · have hpos : 0 < qStartRem :=
                hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi (by omega) hqDr hR).1
            · have hpos : 0 < qDrRem :=
                hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi hqSt (by omega) hR).1
          · simp [mapPreEnc, mapMidEnc]
        · intro m hm
          rw [BhShallowTwoStageRed.run1_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hm
          rcases hm with ⟨res, hres, hm_cont⟩
          have hR := hResInv res hres
          rcases res with ⟨r_ans, σ1⟩ | ⟨c_ans, p_ans, σ1⟩
          · dsimp only at hm_cont
            rw [spec.rdec_eq t r_ans] at hm_cont
            rcases t with (kq | cq) | ⟨i, sq⟩
            · have hpos : 0 < qKiRem :=
                hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                (by omega) hqSt hqDr hR).2 m hm_cont
            · have hpos : 0 < qStartRem :=
                hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi (by omega) hqDr hR).2 m hm_cont
            · have hpos : 0 < qDrRem :=
                hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
              exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
                ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
                hqKi hqSt (by omega) hR).2 m hm_cont
          · simp only [support_pure, Set.mem_singleton_iff] at hm_cont
            subst hm_cont
            rcases hR with ⟨⟨cq, rfl⟩, hInv1, hPaused1⟩
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            refine ⟨qKiDone, qKiRem, qStartDone + 1, qStartRem - 1, qDrDone, qDrRem,
              hqKi, by omega, hqDr, hInv1, hPaused1, fun v => ⟨?_, ?_, ?_⟩⟩
            · exact (hTot.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            · exact (hStart.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            · exact (hDr.2 v).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly])

theorem twoStage_eval1_eq
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : TargetAdvBounded S B_A b qStart qDR) (fuel : ℕ) (dflt : Bool) :
    spec.R.eval1 (fun _ => B_A) () fuel dflt =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        spec.R_ref.eval1 (fun _ => B_A) () fuel dflt := by
  have hRun1 := (twoStage_run1_eq_and_inv spec dflt B_A fuel
    0 b.q_total 0 qStart 0 qDR spec.σ0
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega) spec.init_inv)
  simp only [TwoStageCostedReduction.eval1, BhShallowTwoStageRed.eval1]
  rw [spec.init_costed, spec.init_ref, pure_bind, pure_bind, hRun1.1, bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun m hm => ?_
  have hInvM := hRun1.2 m hm
  cases m with
  | done b_out σ_out =>
    rcases hInvM with ⟨qKi1, qSt1, qDr1, hInvOut⟩
    dsimp only [mapMidEnc]
    rw [spec.chDone_eq hInvOut b_out, bind_map_left, map_bind]
    refine bind_congr fun c => ?_
    simp [mapOut1Enc, mapMidEnc]
  | paused t c p σ_p cont =>
    simp [mapMidEnc, mapOut1Enc]

theorem twoStage_runFuel_eq_and_inv
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    {α : Type} (dflt : α) :
    ∀ (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
      (fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem : ℕ)
      (σ : DrvSt),
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
        qKiRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
        qStartRem →
      oa.IsQueryBoundP
        (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
        qDrRem →
      qKiDone + qKiRem ≤ b.q_total →
      qStartDone + qStartRem ≤ qStart →
      qDrDone + qDrRem ≤ qDR →
      spec.Inv qKiDone qStartDone qDrDone σ →
      spec.PausedInv σ →
      (runFuel (C := e2eTargetGameCodec S ℓ Pt)
          spec.R.handlePost dflt oa fuel (spec.drvEnc σ) =
        Prod.map id spec.drvEnc <$>
          bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ) ∧
      (∀ out ∈ support
          (bhShallowRunFuel spec.R_ref.qenc spec.R_ref.rdec
            spec.R_ref.handlePost dflt oa fuel σ),
        ∃ qKi2 qSt2 qDr2, spec.Inv qKi2 qSt2 qDr2 out.2) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      _ _ _ _ _ _ hInv _
    refine ⟨by rw [runFuel_pure, bhShallowRunFuel_pure, map_pure]; rfl, ?_⟩
    intro out hout
    rw [bhShallowRunFuel_pure] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
  | query_bind q mx ih =>
    intro fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
      hTot hStart hDr hqKi hqSt hqDr hInv hPaused
    rw [isQueryBoundP_query_bind_iff] at hTot hStart hDr
    cases q with
    | inl n =>
      have hContTot : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
          qKiRem := fun u => (hTot.2 u).mono (by simp [bhClassifyTarget])
      have hContSt : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
          qStartRem := fun u => (hStart.2 u).mono (by simp [bhClassifyTarget])
      have hContDr : ∀ u, (mx u).IsQueryBoundP
          (fun q => bhClassifyTarget (fun _ => false) (fun _ => false) (fun _ => true) q = true)
          qDrRem := fun u => (hDr.2 u).mono (by simp [bhClassifyTarget])
      refine ⟨?_, ?_⟩
      · rw [runFuel_query_inl, bhShallowRunFuel_query_inl,
          atomicSessionTargetIface_fwdU_eq_bhFwdU, map_bind]
        exact bind_congr fun u =>
          (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
            (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv hPaused).1
      · intro out hout
        rw [bhShallowRunFuel_query_inl, mem_support_bind_iff] at hout
        rcases hout with ⟨u, -, hout'⟩
        exact (ih u fuel qKiDone qKiRem qStartDone qStartRem qDrDone qDrRem σ
          (hContTot u) (hContSt u) (hContDr u) hqKi hqSt hqDr hInv hPaused).2 out hout'
    | inr t =>
      cases fuel with
      | zero =>
        refine ⟨by rw [runFuel_query_inr_zero, bhShallowRunFuel_query_inr_zero, map_pure]; rfl, ?_⟩
        intro out hout
        rw [bhShallowRunFuel_query_inr_zero] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact ⟨qKiDone, qStartDone, qDrDone, hInv⟩
      | succ f =>
        have htBound : StepBudgetOk b qStart qDR qKiDone qStartDone qDrDone t := by
          rcases ht : t with (kq | cq) | ⟨i, sq⟩
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
          · dsimp only [StepBudgetOk]
            have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by rw [ht]; simp [bhClassifyTarget, bhClassifyTargetOnly])
            omega
        have hStepEq := spec.stepPost_eq hInv hPaused t htBound
        have hPostInv := spec.stepPost_inv hInv hPaused t htBound
        refine ⟨?_, ?_⟩
        · rw [runFuel_query_inr_succ, bhShallowRunFuel_query_inr_succ, spec.qenc_eq t]
          rw [hStepEq, bind_map_left, map_bind]
          refine bind_congr_of_forall_mem_support _ fun ⟨r_ans, σ1⟩ hp => ?_
          have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          dsimp only [Prod.map]
          have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t r_ans
          dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
          rw [hAns, spec.rdec_eq t r_ans]
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              (by omega) hqSt hqDr hInv1 hP1).1
          · have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi (by omega) hqDr hInv1 hP1).1
          · have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi hqSt (by omega) hInv1 hP1).1
        · intro out hout
          rw [bhShallowRunFuel_query_inr_succ, spec.qenc_eq t, mem_support_bind_iff] at hout
          rcases hout with ⟨⟨r_ans, σ1⟩, hp, hout'⟩
          have ⟨hP1, hInv1⟩ := hPostInv (r_ans, σ1) hp
          dsimp only at hout'
          rw [spec.rdec_eq t r_ans] at hout'
          rcases t with (kq | cq) | ⟨i, sq⟩
          · have hpos : 0 < qKiRem :=
              hTot.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f (qKiDone + 1) (qKiRem - 1) qStartDone qStartRem qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              (by omega) hqSt hqDr hInv1 hP1).2 out hout'
          · have hpos : 0 < qStartRem :=
              hStart.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem (qStartDone + 1) (qStartRem - 1) qDrDone qDrRem σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi (by omega) hqDr hInv1 hP1).2 out hout'
          · have hpos : 0 < qDrRem :=
              hDr.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
            exact (ih _ f qKiDone qKiRem qStartDone qStartRem (qDrDone + 1) (qDrRem - 1) σ1
              ((hTot.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hStart.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              ((hDr.2 _).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
              hqKi hqSt (by omega) hInv1 hP1).2 out hout'

theorem twoStage_eval2_eq
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : TargetAdvBounded S B_A b qStart qDR)
    (fuel1 fuel2 : ℕ) (dflt : Bool) :
    ∀ o ∈ support (stageOneAsProbComp
        (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt)),
      ∀ flip : Bool,
        spec.R.eval2 (mapMidEnc spec.drvEnc spec.πEnc o.2) flip fuel2 dflt =
          spec.R_ref.eval2 o.2 flip fuel2 dflt := by
  intro o ho flip
  have hEval1Eq := twoStage_eval1_eq spec B_A hB fuel1 dflt
  have hZero := spec.stage1_queries_zero
  have hQb1Costed :
      (spec.R.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    have hU := isQueryBoundP_atomicSessionTargetIface_fwdU (ℓ := ℓ) (Pt := Pt)
    exact (TwoStageCostedReduction.eval1_queryBound spec.R (isSmTargetQuery ℓ)
      (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl) hU (fun _ => B_A) () fuel1 dflt).mono
      (by
        have hinit : spec.R.init.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hpre : spec.R.handlePre.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        have hch : spec.R.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := by omega
        simp [hinit, hpre, hch])
  have hQb1Ref :
      (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt).IsQueryBoundP (isSmTargetQuery ℓ) 0 := by
    rw [hEval1Eq] at hQb1Costed
    exact (OracleComp.isQueryBoundP_map_iff (p := isSmTargetQuery ℓ) _ _ 0).mp hQb1Costed
  have ho_raw : o ∈ support (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) :=
    mem_support_of_mem_support_stageOneAsProbComp _ ho hQb1Ref
  have hm_raw : o.2 ∈ support (spec.R_ref.run1 dflt B_A fuel1 spec.σ0) := by
    simp only [BhShallowTwoStageRed.eval1, spec.init_ref, pure_bind, mem_support_bind_iff] at ho_raw
    rcases ho_raw with ⟨m, hm, hrest⟩
    cases m with
    | done b_out σ_out =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hrest
      rcases hrest with ⟨_, -, rfl⟩
      exact hm
    | paused t c p σ_p cont =>
      simp only [support_pure, Set.mem_singleton_iff] at hrest
      subst hrest
      exact hm
  have hInvM := (twoStage_run1_eq_and_inv spec dflt B_A fuel1
    0 b.q_total 0 qStart 0 qDR spec.σ0
    hB.tot hB.start hB.dr (by omega) (by omega) (by omega) spec.init_inv).2 o.2 hm_raw
  rcases hm_case : o.2 with ⟨b_out, σ_out⟩ | ⟨t, c_p, p_p, σ_p, cont⟩
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qSt1, qDr1, hInvOut⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2, pure_bind]
    exact spec.finish_eq hInvOut b_out flip
  · rw [hm_case] at hInvM
    rcases hInvM with ⟨qKi1, qKiR1, qSt1, qStR1, qDr1, qDrR1, hqKi1, hqSt1, hqDr1,
      hInvP, hPausedP, hContB⟩
    simp only [mapMidEnc, TwoStageCostedReduction.eval2, BhShallowTwoStageRed.eval2]
    rw [spec.resume_eq hInvP hPausedP p_p flip, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨v_ans, σ_res⟩ hrs => ?_
    have ⟨hInvRes, hPausedRes⟩ := spec.resume_inv hInvP hPausedP p_p flip (v_ans, σ_res) hrs
    dsimp only [Prod.map]
    have hAns := e2eTargetGameCodec_rdec_atomicGameRespEnc (S := S) (ℓ := ℓ) (Pt := Pt) t v_ans
    dsimp only [e2eTargetGameCodec, _root_.ReductionDsl.e2eGameCodec] at hAns ⊢
    rw [hAns, spec.rdec_eq t v_ans]
    let ans := bhTargetRdec t v_ans
    have ⟨hCB1, hCB2, hCB3⟩ := hContB ans
    have ⟨hFuelEq, hFuelInv⟩ := twoStage_runFuel_eq_and_inv spec dflt
      (cont ans) fuel2 qKi1 qKiR1 qSt1 qStR1 qDr1 qDrR1 σ_res
      hCB1 hCB2 hCB3 hqKi1 hqSt1 hqDr1 hInvRes hPausedRes
    rw [hFuelEq, bind_map_left]
    refine bind_congr_of_forall_mem_support _ fun ⟨b_out, σ_out⟩ hout => ?_
    rcases hFuelInv (b_out, σ_out) hout with ⟨qKi2, qSt2, qDr2, hInvOut⟩
    exact spec.finish_eq hInvOut b_out flip

/-- Full two-stage `ProbComp` equality between `spec.R` and `spec.R_ref` for any Stage-2
experiment `game2`. -/
theorem twoStage_stage12_comp_eq
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : TargetAdvBounded S B_A b qStart qDR)
    {β : Type}
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (fuel1 fuel2 : ℕ) (dflt flip : Bool) :
    (stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (spec.R.eval2 o.2 flip fuel2 dflt)) =
    (stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (spec.R_ref.eval2 o.2 flip fuel2 dflt)) := by
  have h1 := twoStage_eval1_eq spec B_A hB fuel1 dflt
  have h1s :
      stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) =
      mapOut1Enc spec.drvEnc spec.πEnc <$>
        stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) := by
    unfold stageOneAsProbComp
    rw [h1, simulateQ_map]
  rw [h1s, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun o ho => ?_
  have h2 := twoStage_eval2_eq spec B_A hB fuel1 fuel2 dflt o ho flip
  dsimp only [Function.comp_def, mapOut1Enc, atomicPrefixCtxEnc]
  rw [h2]

theorem evalDist_twoStage_stage12_eq
    (spec : TwoStageAtomicSimSpec S Pt ℓ O b qStart qDR DrvSt π_ref)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (hB : TargetAdvBounded S B_A b qStart qDR)
    {β : Type} [MeasurableSpace β]
    (game2 : IdentityKey → IdentityKey → BitVec 256 →
      OracleComp
        (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) Bool →
      ProbComp β)
    (fuel1 fuel2 : ℕ) (dflt flip : Bool) :
    𝒟[stageOneAsProbComp (spec.R.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.1 o.1.2.1 o.1.2.2 (spec.R.eval2 o.2 flip fuel2 dflt)] =
    𝒟[stageOneAsProbComp (spec.R_ref.eval1 (fun _ => B_A) () fuel1 dflt) >>= fun o =>
      game2 o.1.idA o.1.idB o.1.spkCoins (spec.R_ref.eval2 o.2 flip fuel2 dflt)] :=
  congrArg evalDist (twoStage_stage12_comp_eq spec B_A hB game2 fuel1 fuel2 dflt flip)

end SimProofs

end Computational.Proofs.E2E.Dsl.PrefixRedHaltedEval
