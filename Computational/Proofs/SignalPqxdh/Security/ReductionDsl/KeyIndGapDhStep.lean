/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreHol
import VCVio.EvalDist.Monad.Basic

/-!
# Per-Branch Evaluation Agreement for `fgKeyIndGapDhProg`

Proves that each helper and query branch in `KeyIndGapDh` evaluates to its shallow `GdhSimSpec`
counterpart whenever all state lists have length `≤ K`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open SignalPqxdh.Security.FgGapDh.Ik SignalPqxdh.Security.FgGapDh.Opk
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

attribute [simp] bundleV hdrV drKeyV sidV keyIndRenc keyIndQenc

/-! ## `liftBase`, `ddhQ`, and Expression Simp Lemmas -/

@[simp] theorem embedPrim_gapDhFrag {α : Type} (m : OracleComp PrimBaseSpec α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := gapDhDdhOracle.spec) m =
      _root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec) m := rfl

@[simp] theorem pqPrimIface_liftP {α : Type} (p : ProbComp α) :
    pqPrimIface.liftP p = _root_.SignalPqxdh.Security.embedUnif p := rfl

@[simp] theorem pqChalIface_liftP {C : ChallengerOracle} {α : Type} (p : ProbComp α) :
    (pqChalIface C).liftP p =
      _root_.SignalPqxdh.Security.embedPrim (_root_.SignalPqxdh.Security.embedUnif p) := by
  rw [← pqPrimIface_liftP]
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    simp only [Iface.liftP, pqChalIface, pqPrimIface, simulateQ_query_bind]
    congr 1; funext u; exact ih u

@[simp] theorem embedPrim_pure' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec) (Pure.pure a) = Pure.pure a := rfl

@[simp] theorem embedPrim_bind' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (m : OracleComp PrimBaseSpec α) (k : α → OracleComp PrimBaseSpec β) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec) (m >>= k) =
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) m >>=
        fun a => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (r u >>= k)) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (r u)) >>=
        fun a => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (k a)
    rw [bind_assoc]
    congr 1; funext u
    exact ih u

@[simp] theorem embedPrim_map' {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β) (m : OracleComp PrimBaseSpec α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec) (f <$> m) =
      f <$> _root_.SignalPqxdh.Security.embedPrim (spec := spec) m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, embedPrim_bind']
  rfl

theorem embedPrim_findML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (findML p L) =
        findML (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [findML, embedPrim_bind']
    congr 1; funext b; cases b
    · exact embedPrim_findML p xs
    · rfl

theorem embedPrim_anyML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) :
    ∀ (L : List α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (anyML p L) =
        anyML (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (p x)) L
  | [] => rfl
  | x :: xs => by
    simp only [anyML, embedPrim_bind']
    congr 1; funext b; cases b
    · exact embedPrim_anyML p xs
    · rfl

theorem embedPrim_mapML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → OracleComp PrimBaseSpec β) :
    ∀ (L : List α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (mapML f L) =
        mapML (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (f x)) L
  | [] => rfl
  | x :: xs => by
    simp only [mapML, embedPrim_bind', embedPrim_pure', embedPrim_mapML f xs]

theorem embedPrim_consumeFirstML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (m : α → α) :
    ∀ (L : List α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (consumeFirstML p m L) =
        consumeFirstML (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (p x)) m L
  | [] => rfl
  | x :: xs => by
    simp only [consumeFirstML, embedPrim_bind']
    congr 1; funext b; cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, embedPrim_bind',
        embedPrim_consumeFirstML p m xs, embedPrim_pure']
    · rfl

@[simp] theorem embedPrim_foldML {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β → OracleComp PrimBaseSpec β) :
    ∀ (init : β) (L : List α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (foldML f init L) =
        foldML (fun x acc => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (f x acc)) init L
  | _, [] => rfl
  | init, x :: xs => by
    simp only [foldML, embedPrim_bind']
    congr 1; funext b'; exact embedPrim_foldML f b' xs

@[simp] theorem embedPrim_iterM {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (f : α → OracleComp PrimBaseSpec α) :
    ∀ (n : ℕ) (a : α),
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) (iterM f n a) =
        iterM (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := spec) (f x)) n a
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterM, embedPrim_bind']
    congr 1; funext a'; exact embedPrim_iterM f n a'

@[simp] theorem liftBase_eval {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (liftBase (C := C) c).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := C.spec) (c.eval env) := by
  induction c with
  | ret e => rfl
  | bind c k ihc ihk =>
    simp only [liftBase, Comp.eval, ihc env, embedPrim_bind']
    congr 1; funext x; exact ihk (.cons x env)
  | ite b c d ihc ihd =>
    simp only [liftBase, Comp.eval]
    cases b.eval env <;> simp [ihc env, ihd env]
  | caseOpt e n s ihn ihs =>
    simp only [liftBase, Comp.eval]
    cases e.eval env with
    | none => exact ihn env
    | some x => exact ihs (.cons x env)
  | caseSum e l r ihl ihr =>
    simp only [liftBase, Comp.eval]
    cases e.eval env with
    | inl x => exact ihl (.cons x env)
    | inr y => exact ihr (.cons y env)
  | sample s e =>
    simp only [liftBase, Comp.eval, pqChalIface_liftP, pqPrimIface_liftP]
    rfl
  | query g e =>
    simp only [liftBase, Comp.eval, pqChalIface, pqPrimIface, embedPrim_map']
    rfl
  | iter n e body ihb =>
    simp only [liftBase, Comp.eval, embedPrim_iterM]
    have hFn : (fun a => (liftBase (C := C) body).eval (.cons a env)) =
        (fun a => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (body.eval (.cons a env))) := by
      funext a; exact ihb (.cons a env)
    rw [hFn]
  | findM K l p ihp =>
    simp only [liftBase, Comp.eval, embedPrim_findML]
    have hFn : (fun x => (liftBase (C := C) p).eval (.cons x env)) =
        (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | anyM K l p ihp =>
    simp only [liftBase, Comp.eval, embedPrim_anyML]
    have hFn : (fun x => (liftBase (C := C) p).eval (.cons x env)) =
        (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | mapM K l f ihf =>
    simp only [liftBase, Comp.eval, embedPrim_mapML]
    have hFn : (fun x => (liftBase (C := C) f).eval (.cons x env)) =
        (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (f.eval (.cons x env))) := by
      funext x; exact ihf (.cons x env)
    rw [hFn]
  | consumeFirstM K l p mk ihp =>
    simp only [liftBase, Comp.eval, embedPrim_consumeFirstML]
    have hFn : (fun x => (liftBase (C := C) p).eval (.cons x env)) =
        (fun x => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (p.eval (.cons x env))) := by
      funext x; exact ihp (.cons x env)
    rw [hFn]
  | foldM K l z f ihf =>
    simp only [liftBase, Comp.eval, embedPrim_foldML]
    have hFn : (fun x acc => (liftBase (C := C) f).eval (.cons x (.cons acc env))) =
        (fun x acc => _root_.SignalPqxdh.Security.embedPrim (spec := C.spec)
          (f.eval (.cons x (.cons acc env)))) := by
      funext x acc; exact ihf (.cons x (.cons acc env))
    rw [hFn]

@[simp] theorem gPrim_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (gPrim c).eval env =
      _root_.SignalPqxdh.Security.embedPrim (spec := gapDhOracleSpec) (c.eval env) :=
  liftBase_eval c env

theorem bind_congr {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {m : OracleComp spec α} {f g : α → OracleComp spec β}
    (h : ∀ a, f a = g a) : m >>= f = m >>= g :=
  congrArg (m >>= ·) (funext h)

@[simp] theorem FgGapDh_embedPrim_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (m : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) m =
      _root_.SignalPqxdh.Security.embedPrim (spec := spec) m := rfl

@[simp] theorem FgGapDh_embedUnif_eq {α : Type} (p : ProbComp α) :
    FgGapDh.embedUnif p = _root_.SignalPqxdh.Security.embedUnif p := rfl

@[simp] theorem FgGapDh_primQ_eq (op : PrimQuery) :
    FgGapDh.primQ op = _root_.SignalPqxdh.Security.primQ op := rfl

@[simp] theorem FgGapDh_findMPrim_eq {α : Type} (p : α → OracleComp PrimBaseSpec Bool)
    (L : List α) :
    FgGapDh.findMPrim p L = _root_.SignalPqxdh.Security.findMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [FgGapDh.findMPrim, _root_.SignalPqxdh.Security.findMPrim, ih]

@[simp] theorem FgGapDh_anyMPrim_eq {α : Type} (p : α → OracleComp PrimBaseSpec Bool)
    (L : List α) :
    FgGapDh.anyMPrim p L = _root_.SignalPqxdh.Security.anyMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [FgGapDh.anyMPrim, _root_.SignalPqxdh.Security.anyMPrim, ih]

@[simp] theorem FgGapDh_findHonestPrincipalPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikPk : Bytes) :
    FgGapDh.findHonestPrincipalPrim S principals ikPk =
      _root_.SignalPqxdh.Security.findHonestPrincipalPrim S principals ikPk := by
  simp only [FgGapDh.findHonestPrincipalPrim, _root_.SignalPqxdh.Security.findHonestPrincipalPrim,
    FgGapDh_findMPrim_eq, FgGapDh_primQ_eq]

@[simp] theorem FgGapDh_resolveSigPkPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikPk : Bytes) :
    FgGapDh.resolveSigPkPrim S principals ikPk =
      _root_.SignalPqxdh.Security.resolveSigPkPrim S principals ikPk := by
  simp only [FgGapDh.resolveSigPkPrim, _root_.SignalPqxdh.Security.resolveSigPkPrim,
    FgGapDh_findHonestPrincipalPrim_eq]
  rfl

@[simp] theorem FgGapDh_isHonestUncorruptedPeerPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikPk : Bytes) :
    FgGapDh.isHonestUncorruptedPeerPrim S principals ikPk =
      _root_.SignalPqxdh.Security.isHonestUncorruptedPeerPrim S principals ikPk := by
  simp only [FgGapDh.isHonestUncorruptedPeerPrim,
    _root_.SignalPqxdh.Security.isHonestUncorruptedPeerPrim,
    FgGapDh_findHonestPrincipalPrim_eq]
  rfl

@[simp] theorem FgGapDh_checkBundleProvenancePrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput) :
    FgGapDh.checkBundleProvenancePrim S principals spkBundles opkEntries bundle =
      _root_.SignalPqxdh.Security.checkBundleProvenancePrim S principals spkBundles
        opkEntries bundle := by
  simp only [FgGapDh.checkBundleProvenancePrim,
    _root_.SignalPqxdh.Security.checkBundleProvenancePrim,
    FgGapDh_findHonestPrincipalPrim_eq, FgGapDh_anyMPrim_eq, FgGapDh_primQ_eq]
  rfl

@[simp] theorem FgGapDh_isGameSpkPrim_eq (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (spkPk : Bytes) :
    FgGapDh.isGameSpkPrim S spkBundles spkPk =
      _root_.SignalPqxdh.Security.isGameSpkPrim S spkBundles spkPk := by
  simp only [FgGapDh.isGameSpkPrim, _root_.SignalPqxdh.Security.isGameSpkPrim,
    FgGapDh_anyMPrim_eq, FgGapDh_primQ_eq]

@[simp] theorem FgGapDh_isGameOpkPrim_eq (S : Setup)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (opkPk : Bytes) :
    FgGapDh.isGameOpkPrim S opkEntries opkPk =
      _root_.SignalPqxdh.Security.isGameOpkPrim S opkEntries opkPk := by
  simp only [FgGapDh.isGameOpkPrim, _root_.SignalPqxdh.Security.isGameOpkPrim,
    FgGapDh_anyMPrim_eq, FgGapDh_primQ_eq]

@[simp] theorem FgGapDh_keyIndPartnerPrim_eq {S : Setup}
    (init : KeyIndInitiatorEntry S) (resp : KeyIndRespEntry S) :
    FgGapDh.keyIndPartnerPrim init resp =
      _root_.SignalPqxdh.Security.keyIndPartnerPrim init resp := rfl

@[simp] theorem embedPrim_query' {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (q : ℕ ⊕ PrimQuery) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec)
      (liftM (OracleSpec.query (spec := PrimBaseSpec) q)) =
      liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) := by
  change (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>= pure) = _
  exact bind_pure _

@[simp] theorem embedPrim_primQ {ι : Type} {spec : OracleSpec.{0, 0} ι} (op : PrimQuery) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec)
      (_root_.SignalPqxdh.Security.primQ op) =
      liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl (Sum.inr op))) :=
  embedPrim_query' (Sum.inr op)

@[simp] theorem ddhQ_eval {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (ddhQ x y z).eval env = ddhGdhQ (x.eval env) (y.eval env) (z.eval env) := by
  simp [ddhQ, Comp.eval, Expr.eval, pqGapDhIface, pqChalIface, gapDhDdhOracle, ddhGdhQ]

@[simp] theorem slice32_eval (off : Nat) {Γ : List PT} (bs : Expr pqxdhOps Γ (B 192)) (env : Env Γ) :
    (slice32 off bs).eval env = List.take 32 (List.drop off (bs.eval env)) := rfl

theorem min_N_recv_spk_tot {S : Setup} (u : Fin S.N_id) :
    Nat.min S.N_recv S.N_spk_tot = S.N_recv :=
  Nat.min_eq_left (Nat.le_mul_of_pos_left _ u.pos)

theorem min_N_opk_opk_tot {S : Setup} (u : Fin S.N_id) (j : Fin S.N_recv) :
    Nat.min S.N_opk S.N_opk_tot = S.N_opk :=
  Nat.min_eq_left (Nat.le_mul_of_pos_left _ (Nat.mul_pos u.pos j.pos))

@[simp] theorem spkFlatIdxE_eval (S : Setup) {Γ : List PT} (u j : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (spkFlatIdxE S u j).eval env = u.eval env * Nat.min S.N_recv S.N_spk_tot + j.eval env := by
  simp [spkFlatIdxE, Expr.eval]

@[simp] theorem opkFlatIdxE_eval (S : Setup) {Γ : List PT} (u j o : Expr pqxdhOps Γ .nat)
    (env : Env Γ) :
    (opkFlatIdxE S u j o).eval env =
      (u.eval env * Nat.min S.N_recv S.N_spk_tot + j.eval env) *
        Nat.min S.N_opk S.N_opk_tot + o.eval env := by
  simp [opkFlatIdxE, Expr.eval]

@[simp] theorem respBundleKeyE_eval {S : Setup} {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy)
    (env : Env Γ) (s : SessionId S) (hs : sid.eval env = sessionIdToVal s) :
    (respBundleKeyE sid).eval env = respBundleKey s := by
  simp only [respBundleKeyE, eCaseSum, v, Expr.eval, Env.get,
    Ext.refl_wk', hs]
  cases s <;> rfl

@[simp] theorem findML_gdh {α : Type} (p : α → OracleComp GdhSimSpec Bool) (L : List α) :
    findML (m := OracleComp GdhSimSpec) p L = findMGdh p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [findML, findMGdh, ih]

theorem findMGdh_map {α β : Type} (f : α → β) (p : β → OracleComp GdhSimSpec Bool) (L : List α) :
    findMGdh p (L.map f) = Option.map f <$> findMGdh (fun x => p (f x)) L := by
  simp only [← findML_gdh, findML_map]

@[simp] theorem findMGdh_take_map {α β : Type} (f : α → β)
    (p : β → OracleComp GdhSimSpec Bool) (n : Nat) (L : List α) :
    findMGdh p ((L.map f).take n) = Option.map f <$> findMGdh (fun x => p (f x)) (L.take n) := by
  rw [← List.map_take, findMGdh_map]

@[simp] theorem anyML_gdh {α : Type} (p : α → OracleComp GdhSimSpec Bool) (L : List α) :
    anyML (m := OracleComp GdhSimSpec) p L = anyMGdh p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [anyML, anyMGdh, ih]

@[simp] theorem decPrin_enc' (l : List (Nat × PrincipalEntry)) :
    decPrin (l.map (fun x => (x.1, principalEntryToVal x.2))) = l :=
  decPrin_enc l

/-! ## Boundedness Predicate for `FgKeyIndSimState` -/

/-- All non-truncated lists in `FgKeyIndSimState S` have length `≤ n`. -/
structure FgSimListsBounded {S : Setup} (st : FgKeyIndSimState S) (n : Nat) : Prop where
  base_le       : KeyIndListsBounded st.base n
  rawRoCache_le : st.rawRoCache.length ≤ n
  advKeyPows_le : st.advKeyPows.length ≤ n

def encSimRS {S : Setup} (p : KeyIndResponse × FgKeyIndSimState S) :
    (Ty.prod keyIndRespTy simTy).denote :=
  (keyIndRespToVal p.1, simStateToVal p.2)

def encGdhRS {S : Setup} (pa : paramsTy.denote) (p : KeyIndResponse × FgKeyIndSimState S) :
    (Ty.prod keyIndRespTy gdhStateTy).denote :=
  (keyIndRespToVal p.1, (pa, simStateToVal p.2))

@[simp] theorem map_quad_id {α β γ δ : Type} (xs : List (α × β × γ × δ)) :
    xs.map (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2)) = xs :=
  List.map_id'' (fun ⟨_, _, _, _⟩ => rfl) xs

syntax "gdh_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| gdh_simp [$xs,*]) =>
    `(tactic| core_simp [Bool.false_eq_true, PNat.val_ofNat,
      liftBase_eval, gPrim_eval, embedPrim_gapDhFrag, ddhQ_eval, slice32_eval,
      spkFlatIdxE_eval, opkFlatIdxE_eval, findML_gdh, anyML_gdh, decPrin_enc',
      map_quad_id, Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
      handshakeHdrToVal, drKeyToVal,
      FgGapDh_embedPrim_eq, FgGapDh_embedUnif_eq, FgGapDh_primQ_eq,
      FgGapDh_findMPrim_eq, FgGapDh_anyMPrim_eq, FgGapDh_findHonestPrincipalPrim_eq,
      FgGapDh_resolveSigPkPrim_eq, FgGapDh_isHonestUncorruptedPeerPrim_eq,
      FgGapDh_checkBundleProvenancePrim_eq, FgGapDh_isGameSpkPrim_eq,
      FgGapDh_isGameOpkPrim_eq, FgGapDh_keyIndPartnerPrim_eq,
      embedPrim_query', embedPrim_primQ,
      embedPrim_pure', embedPrim_bind', embedPrim_map',
      bundleV, hdrV, drKeyV, sidV, keyIndRenc, keyIndQenc,
      preKeyBundleToVal, handshakeHdrToVal, drKeyToVal, sessionIdToVal,
      keyIndRespToVal, keyIndQueryToVal,
      Prod.map, id,
      fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
      paU, paV, paUp, paPrinFlag, paPrinIdx, paDhFlag, paEphIdx,
      paSpkIdx, paOpkMode, paOpkIdx, paMode, paMk,
      smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd, simStateToVal, $xs,*])

/-! ## DDH-Consistency Table Lemmas -/

@[simp] theorem mkSecretPosC_eval {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (mkSecretPosC z).eval env = fgPosToVal <$> mkSecretPos (z.eval env) := by
  unfold mkSecretPosC mkSecretPos
  gdh_simp [fgPosToVal, primGdhQ, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

@[simp] theorem mkPairPosC_eval {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (mkPairPosC pk1 pk2).eval env = fgPosToVal <$> mkPairPos (pk1.eval env) (pk2.eval env) := by
  unfold mkPairPosC mkPairPos
  gdh_simp [fgPosToVal, primGdhQ, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

@[simp] theorem computePosC_eval {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (computePosC sk1 sk2 pk1 pk2).eval env =
      fgPosToVal <$> computeTwoSideOrPairPos
        (sk1.eval env) (sk2.eval env) (pk1.eval env) (pk2.eval env) := by
  unfold computePosC computeTwoSideOrPairPos
  gdh_simp [primGdhQ, mkSecretPosC_eval, mkPairPosC_eval,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rcases sk1.eval env with _ | ⟨b1, bs1⟩ <;>
    rcases sk2.eval env with _ | ⟨b2, bs2⟩ <;> rfl

@[simp] theorem computeOptPosInitC_eval {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) (env : Env Γ) :
    (computeOptPosInitC sk1 pk1 opkB?).eval env =
      Option.map fgPosToVal <$>
        computeOptPos (sk1.eval env) (pk1.eval env)
          ((opkB?.eval env).map (fun (_, pk) => ([], pk))) := by
  unfold computeOptPosInitC computeOptPos
  simp only [letV_eval, caseOptV, bindV, Comp.eval, v,
    Expr.eval, Env.get_zero', Ext.step_wk', Ext.refl_wk']
  rcases opkB?.eval env with _ | ⟨id, pk⟩
  · rfl
  · simp only [Option.map_some, computePosC_eval, litB_eval, Expr.eval, Env.get_zero',
      Env.get_succ', map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

@[simp] theorem ddhEqC_eval {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) (env : Env Γ)
    (pos1 pos2 : FgPoS) (h1 : p1.eval env = fgPosToVal pos1)
    (h2 : p2.eval env = fgPosToVal pos2) :
    (ddhEqC p1 p2).eval env = ddhEqGdh pos1 pos2 := by
  unfold ddhEqC ddhEqGdh
  simp only [letV_eval, caseSumV, Comp.eval,
    Expr.eval, orE_eval, eqB_eval, v, Env.get, Ext.step_wk', Ext.refl_wk', h1, h2]
  rcases pos1 with ⟨z1, c1⟩ | ⟨a1, b1, w1, w2⟩ <;>
    rcases pos2 with ⟨z2, c2⟩ | ⟨a2, b2, w3, w4⟩ <;>
    (simp [fgPosToVal]; try rfl)

@[simp] theorem ddhEqOptC_eval {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) (env : Env Γ)
    (pos1? pos2? : Option FgPoS) (h1 : p1?.eval env = pos1?.map fgPosToVal)
    (h2 : p2?.eval env = pos2?.map fgPosToVal) :
    (ddhEqOptC p1? p2?).eval env = ddhEqOptGdh pos1? pos2? := by
  unfold ddhEqOptC ddhEqOptGdh
  rcases pos1? with _ | pos1 <;> rcases pos2? with _ | pos2
  · simp [letV_eval, caseOptV, Comp.eval, Expr.eval, v, Ext.step_wk', Ext.refl_wk', h1, h2]
  · simp [letV_eval, caseOptV, Comp.eval, Expr.eval, v, Ext.step_wk', Ext.refl_wk', h1, h2]
  · simp [letV_eval, caseOptV, Comp.eval, Expr.eval, v, Ext.step_wk', Ext.refl_wk', h1, h2]
  · simp only [letV_eval, caseOptV, Comp.eval, Expr.eval, v, Env.get, Ext.step_wk', Ext.refl_wk',
      h1, h2, Option.map_some]
    exact ddhEqC_eval _ _ _ pos1 pos2 rfl rfl

@[simp] theorem entryMatchesC_eval {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (p1V : Var Γ₁ fgPosTy) (p2V : Var Γ₂ fgPosTy) (p3V : Var Γ₃ fgPosTy)
    (p4V : Var Γ₄ (.opt fgPosTy)) (ssV : Var Γ₅ (B 32))
    (eV : Var Δ fgPatchEntryTy) (env : Env Δ)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes) (e : FgPatchEntry)
    (hp1 : env.get (Ext.wk p1V) = fgPosToVal pos1)
    (hp2 : env.get (Ext.wk p2V) = fgPosToVal pos2)
    (hp3 : env.get (Ext.wk p3V) = fgPosToVal pos3)
    (hp4 : env.get (Ext.wk p4V) = pos4?.map fgPosToVal)
    (hss : env.get (Ext.wk ssV) = ss)
    (he : env.get eV = fgPatchEntryToVal e) :
    (entryMatchesC p1V p2V p3V p4V ssV eV).eval env =
      fgEntryMatches pos1 pos2 pos3 pos4? ss e := by
  unfold entryMatchesC fgEntryMatches
  have hcond : (Expr.not (eqB (v ssV) (feSs (v eV)))).eval env = (ss != e.ss) := by
    simp only [Expr.eval, eqB_eval, v, feSs, Ext.refl_wk', hss, he, fgPatchEntryToVal]
    rfl
  simp only [Comp.eval, hcond]
  rcases hne : ss != e.ss
  · simp only [Bool.false_eq_true, ↓reduceIte, bindV, Comp.eval]
    rw [ddhEqC_eval _ _ _ pos1 e.pos1 (by simp [v, Expr.eval, hp1])
      (by simp [fePos1, v, Expr.eval, he, fgPatchEntryToVal])]
    refine bind_congr fun b1 => ?_
    rw [ddhEqC_eval _ _ _ pos2 e.pos2 (by simp [v, Expr.eval, hp2])
      (by simp [fePos2, v, Expr.eval, he, fgPatchEntryToVal])]
    refine bind_congr fun b2 => ?_
    rw [ddhEqC_eval _ _ _ pos3 e.pos3 (by simp [v, Expr.eval, hp3])
      (by simp [fePos3, v, Expr.eval, he, fgPatchEntryToVal])]
    refine bind_congr fun b3 => ?_
    rw [ddhEqOptC_eval _ _ _ pos4? e.pos4? (by simp [v, Expr.eval, hp4])
      (by simp [fePos4, v, Expr.eval, he, fgPatchEntryToVal])]
    simp only [Expr.eval, v, Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk']
  · simp only [↓reduceIte]; rfl

theorem fgPatchC_eval (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (p1V : Var Γ₁ fgPosTy) (p2V : Var Γ₂ fgPosTy) (p3V : Var Γ₃ fgPosTy)
    (p4V : Var Γ₄ (.opt fgPosTy)) (ssV : Var Γ₅ (B 32))
    (fgLE : Expr pqxdhOps Δ (.list fgPatchEntryTy)) (env : Env Δ)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes) (L : List FgPatchEntry)
    (hp1 : env.get (Ext.wk p1V) = fgPosToVal pos1)
    (hp2 : env.get (Ext.wk p2V) = fgPosToVal pos2)
    (hp3 : env.get (Ext.wk p3V) = fgPosToVal pos3)
    (hp4 : env.get (Ext.wk p4V) = pos4?.map fgPosToVal)
    (hss : env.get (Ext.wk ssV) = ss)
    (hL : fgLE.eval env = L.map fgPatchEntryToVal) :
    (fgPatchC K p1V p2V p3V p4V ssV fgLE).eval env =
      (fun (dk, L') => (drKeyToVal dk, L'.map fgPatchEntryToVal)) <$>
        fgPatch K pos1 pos2 pos3 pos4? ss L := by
  unfold fgPatchC fgPatch
  simp only [letV_eval, bindV, caseOptV, findMV, Comp.eval,
    findML_gdh, v, Expr.eval, Env.get, Ext.step_wk', Ext.refl_wk', Env.get_zero',
    hL, findMGdh_take_map]
  have hm : (fun x => (entryMatchesC p1V p2V p3V p4V ssV .zero).eval
      (Env.cons (t := fgPatchEntryTy) (fgPatchEntryToVal x)
        (Env.cons (t := .list fgPatchEntryTy) (L.map fgPatchEntryToVal) env))) =
      fgEntryMatches pos1 pos2 pos3 pos4? ss := by
    funext x
    exact entryMatchesC_eval p1V p2V p3V p4V ssV .zero _ pos1 pos2 pos3 pos4? ss x
      (by simp [hp1]) (by simp [hp2]) (by simp [hp3]) (by simp [hp4]) (by simp [hss]) rfl
  rw [hm]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun found => ?_
  rcases found with _ | e
  · gdh_simp [hp1, hp2, hp3, hp4, hss, fgPatchEntryToVal, unifGdh,
      map_eq_bind_pure_comp, bind_assoc, pure_bind]
    rfl
  · simp [feDk, fgPatchEntryToVal]; rfl

/-! ## KOSK & Partner Lookup Lemmas -/

@[simp] theorem isAdvPowsE_eval (K : Nat) {Γ : List PT}
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) (wPk : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (isAdvPowsE K pows wPk).eval env =
      isAdvRegisteredPows ((pows.eval env).take K) (wPk.eval env) := by
  unfold isAdvPowsE isAdvRegisteredPows
  core_simp []

@[simp] theorem koskSenderOkPowsC_eval (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (ik : Expr pqxdhOps Δ (B 32)) (env : Env Δ) (powsL : List (Bytes × Bytes))
    (hpL : pows.eval env = powsL) (hK : powsL.length ≤ K) :
    (koskSenderOkPowsC S K st pows ik).eval env =
      FgGapDh.koskSenderOkPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K) powsL (ik.eval env) := by
  unfold koskSenderOkPowsC FgGapDh.koskSenderOkPrim
  core_simp [hpL, List.take_of_length_le hK, findHonestC_eval, isAdvPowsE_eval,
    FgGapDh_primQ_eq, FgGapDh_findHonestPrincipalPrim_eq,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun o => ?_
  refine bind_congr fun w => ?_
  cases o <;> rfl

@[simp] theorem lookupSpkSkC_eval (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (spkPk : Expr pqxdhOps Δ (B 32)) (env : Env Δ) (powsL : List (Bytes × Bytes))
    (hpL : pows.eval env = powsL) (hK : powsL.length ≤ K) :
    (lookupSpkSkC S K st pows spkPk).eval env =
      lookupSpkSkPrim S ((decSpks (env.get (Ext.wk st)).2.2.1).take K) powsL (spkPk.eval env) := by
  unfold lookupSpkSkC lookupSpkSkPrim
  core_simp [hpL, List.take_of_length_le hK, FgGapDh_primQ_eq]
  refine bind_congr fun wSpk => ?_
  generalize (env.get (Ext.wk st)).2.2.1 = ls
  conv_lhs => rw [decSpks_rt ls]
  simp only [take_minK, ← List.map_take, findMPrim_map, Prod.map, id,
    spkBundleEntryToVal, FgGapDh_findMPrim_eq,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun f => ?_
  rcases f with _ | ⟨idx, b⟩
  · have hfn : (fun ((_sk, w) : Bytes × Bytes) => w == wSpk) = (fun p => p.2 == wSpk) := by
      funext ⟨_, _⟩; rfl
    simp only [Option.map, hfn]
    rcases h : List.find? (fun p => p.2 == wSpk) powsL with _ | ⟨sk, w⟩ <;> simp [h]
  · rfl

@[simp] theorem chooseRespRandC_eval (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (rV : Var Δ keyIndRespEntryTy) (env : Env Δ)
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S)
    (hsess : (env.get (Ext.wk st)).2.2.2.2.1 = sessions.map keyIndSessionEntryToVal)
    (hr : env.get rV = keyIndRespEntryToVal r) (hlen : sessions.length ≤ K) :
    (chooseRespRandC S K st rV).eval env =
      drKeyToVal <$> choosePartnerDrKeyRandGdh sessions r := by
  unfold chooseRespRandC choosePartnerDrKeyRandGdh
  simp only [bindV, caseOptV, findMV, liftBase_eval, embedPrim_gapDhFrag,
    Comp.eval, findML_prim, v, stSess,
    Expr.eval, Env.get, Ext.refl_wk', hsess, take_minK,
    List.take_of_length_le (show (sessions.map keyIndSessionEntryToVal).length ≤ K by simpa using hlen),
    findMPrim_take_map,
    FgGapDh_embedPrim_eq, FgGapDh_findMPrim_eq, FgGapDh_keyIndPartnerPrim_eq,
    embedPrim_bind', embedPrim_pure',
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  have hp : (fun x : KeyIndInitiatorEntry S =>
      (partnerC (Δ := keyIndSessionEntryTy :: Δ) (Var.zero (Γ := Δ)) rV).eval
        (.cons (keyIndSessionEntryToVal x) env)) =
      fun x => _root_.SignalPqxdh.Security.keyIndPartnerPrim x r := by
    funext x
    obtain ⟨_, _, _, _, opk1, _, _, _, _, _, _, _, _, _, _, _⟩ := x
    obtain ⟨_, _, _, opk2, _, _, _, _, _, _, _⟩ := r
    unfold partnerC _root_.SignalPqxdh.Security.keyIndPartnerPrim
    core_simp [hr, keyIndSessionEntryToVal, keyIndRespEntryToVal, hdrV]
    try erw [hr]
    try simp only [keyIndRespEntryToVal, hdrV]
    cases opk1 <;> cases opk2 <;>
    · simp only [Option.getD]
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      rfl
  rw [hp]
  refine bind_congr fun found => ?_
  rcases found with _ | s
  · gdh_simp [unifGdh, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  · simp [keyIndSessionEntryToVal]

@[simp] theorem chooseInitRandC_eval (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (sV : Var Δ keyIndSessionEntryTy) (env : Env Δ)
    (resps : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S)
    (hresps : (env.get (Ext.wk st)).2.2.2.2.2.1 = resps.map keyIndRespEntryToVal)
    (hs : env.get sV = keyIndSessionEntryToVal s) (hlen : resps.length ≤ K) :
    (chooseInitRandC S K st sV).eval env =
      drKeyToVal <$> chooseInitPartnerDrKeyRandGdh resps s := by
  unfold chooseInitRandC chooseInitPartnerDrKeyRandGdh
  simp only [bindV, caseOptV, findMV, liftBase_eval, embedPrim_gapDhFrag,
    Comp.eval, findML_prim, v, stResps,
    Expr.eval, Env.get, Ext.refl_wk', hresps, take_minK,
    List.take_of_length_le (show (resps.map keyIndRespEntryToVal).length ≤ K by simpa using hlen),
    findMPrim_take_map,
    FgGapDh_embedPrim_eq, FgGapDh_findMPrim_eq, FgGapDh_keyIndPartnerPrim_eq,
    embedPrim_bind', embedPrim_pure',
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  have hp : (fun x : KeyIndRespEntry S =>
      (partnerC (Δ := keyIndRespEntryTy :: Δ) sV (Var.zero (Γ := Δ))).eval
        (.cons (keyIndRespEntryToVal x) env)) =
      fun x => _root_.SignalPqxdh.Security.keyIndPartnerPrim s x := by
    funext x
    obtain ⟨_, _, _, _, opk1, _, _, _, _, _, _, _, _, _, _, _⟩ := s
    obtain ⟨_, _, _, opk2, _, _, _, _, _, _, _⟩ := x
    unfold partnerC _root_.SignalPqxdh.Security.keyIndPartnerPrim
    core_simp [hs, keyIndSessionEntryToVal, keyIndRespEntryToVal, hdrV]
    try erw [hs]
    try simp only [keyIndSessionEntryToVal, hdrV]
    cases opk1 <;> cases opk2 <;>
    · simp only [Option.getD]
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      refine bind_congr fun _ => ?_; refine bind_congr fun _ => ?_
      rfl
  rw [hp]
  refine bind_congr fun found => ?_
  rcases found with _ | r
  · gdh_simp [unifGdh, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  · simp [keyIndRespEntryToVal]

/-! ## Random-Oracle Branch Lemma -/

set_option maxHeartbeats 400000 in
theorem roParsedC_eval {S : Setup} (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (smV : Var Γ₁ simTy) (secV : Var Γ₂ (B 192)) (env : Env Δ)
    (st : FgKeyIndSimState S) (secrets : Bytes)
    (hsm : env.get (Ext.wk smV) = simStateToVal st)
    (hsec : env.get (Ext.wk secV) = secrets)
    (hB : FgSimListsBounded st K) :
    (roParsedC K smV secV).eval env =
      encSimRS <$> fgRoQueryGdh K secrets st := by
  have hRawFallback :
      (roRawFallbackC K smV secV).eval env =
        encSimRS <$>
          match st.rawRoCache.find? (fun x => x.1 == secrets) with
          | some (_, dk) => pure (.drKeyResp dk, { st with advRoLog := secrets :: st.advRoLog })
          | none => do
            let dk ← unifGdh sampleDRKey96
            return (.drKeyResp dk,
              { st with rawRoCache := (secrets, dk) :: st.rawRoCache,
                        advRoLog := secrets :: st.advRoLog }) := by
    unfold roRawFallbackC
    gdh_simp [hsm, hsec, List.take_of_length_le, hB.rawRoCache_le, unifGdh]
    rcases hf : st.rawRoCache.find? (fun x => x.1 == secrets) with _ | ⟨s', dk⟩
    · gdh_simp [hf, encSimRS, keyIndRespToVal, simStateToVal, List.map_cons,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    · gdh_simp [hf, encSimRS, keyIndRespToVal, simStateToVal, map_pure]
  unfold roParsedC fgRoQueryGdh parseRoSecrets
  simp only [Comp.eval, Expr.eval, eqB_eval, takeKB_eval, litB_eval, natEq_eval, lenB_eval,
    v, Ext.refl_wk', hsec, PNat.val_ofNat]
  by_cases h1 : secrets.take 32 = F_X25519
  swap
  · have h1b : (secrets.take 32 == F_X25519) = false := beq_false_of_ne h1
    have h1n : (secrets.take 32 != F_X25519) = true := bne_iff_ne.mpr h1
    simp only [h1b, h1n, Bool.not_false, ↓reduceIte, hRawFallback]; rfl
  · simp only [h1, beq_self_eq_true, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    by_cases h2 : secrets.length = 160
    · simp only [h2, beq_self_eq_true, ↓reduceIte]
      gdh_simp [hsec, mkSecretPosC_eval, FgGapDh.extractDh1, FgGapDh.extractDh2,
        FgGapDh.extractDh3, extractDh2, extractKemSsNoOPK,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun p1 => ?_
      refine bind_congr fun p2 => ?_
      refine bind_congr fun p3 => ?_
      rw [fgPatchC_eval K _ _ _ _ _ _ _ p1 p2 p3 none (List.take 32 (List.drop 128 secrets)) st.fgL
        rfl rfl rfl rfl rfl (by gdh_simp [hsm])]
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine bind_congr fun ⟨dk, fgL'⟩ => ?_
      gdh_simp [hsm, hsec, encSimRS, keyIndRespToVal]
    · have h2b : (secrets.length == 160) = false := beq_false_of_ne h2
      simp only [h2b, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : secrets.length = 192
      · simp only [h3, beq_self_eq_true, ↓reduceIte]
        gdh_simp [hsec, mkSecretPosC_eval, FgGapDh.extractDh1, FgGapDh.extractDh2,
          FgGapDh.extractDh3, FgGapDh.extractDh4, extractDh2, extractDh4, extractKemSsOPK,
          map_eq_bind_pure_comp, bind_assoc, pure_bind]
        refine bind_congr fun p1 => ?_
        refine bind_congr fun p2 => ?_
        refine bind_congr fun p3 => ?_
        refine bind_congr fun p4 => ?_
        rw [fgPatchC_eval K _ _ _ _ _ _ _ p1 p2 p3 (some p4)
          (List.take 32 (List.drop 160 secrets)) st.fgL
          rfl rfl rfl rfl rfl (by gdh_simp [hsm])]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨dk, fgL'⟩ => ?_
        gdh_simp [hsm, hsec, encSimRS, keyIndRespToVal]
      · have h3b : (secrets.length == 192) = false := beq_false_of_ne h3
        simp only [h3b, Bool.false_eq_true, ↓reduceIte, hRawFallback]; rfl

/-! ## Simple Query Branch Lemmas -/

section BranchEval
variable (S : Setup) (K : Nat)
  {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
  (paV : Var Γ₁ paramsTy) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
  (env : Env Δ) (pa : paramsTy.denote) (st : FgKeyIndSimState S)
  (hpa : env.get (Ext.wk paV) = pa)
  (hsm : env.get (Ext.wk smV) = simStateToVal st)
  (hbSt : env.get (Ext.wk bStV) = keyIndStateToVal st.base)
  (hB : FgSimListsBounded st K)
include hpa hsm hbSt hB

theorem initPrinGdhB_eval (uV : Var Γ₄ .nat) (u : Fin S.N_id)
    (hu : env.get (Ext.wk uV) = u.val) :
    (initPrinGdhB K paV smV bStV uV).eval env =
      encSimRS <$> fgKeyIndStep pa.2.2.2.1 pa.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.2.2.1 pa.2.1 (.initPrin u) st := by
  unfold initPrinGdhB fgKeyIndStep
  gdh_simp [hpa, hsm, hbSt, hu, List.take_of_length_le, hB.base_le.principals_le,
    unifGdh, sampleScalar32, primGdhQ]
  by_cases h : (st.base.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encSimRS, keyIndRespToVal, simStateToVal]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun sk0 => ?_
    refine bind_congr fun pk0 => ?_
    refine bind_congr fun skS => ?_
    refine bind_congr fun pkS => ?_
    simp [encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal, principalEntryToVal]

set_option maxHeartbeats 600000 in
theorem genSpkGdhB_eval (xV : Var Γ₄ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (genSpkGdhB S K paV smV bStV xV).eval env =
       encSimRS <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.genSPK u j) st := by
  unfold genSpkGdhB fgKeyIndStep
  gdh_simp [hpa, hsm, hbSt, hx, min_N_recv_spk_tot u, List.take_of_length_le,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, nat2_beq, FgGapDh.spkBundleFlatIdx,
    unifGdh, sampleScalar32, primGdhQ]
  by_cases h : (st.base.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
  · simp [h, encSimRS, keyIndRespToVal, simStateToVal]
  · rcases hf : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨idx, uE⟩
    · simp [h, hf, encSimRS, keyIndRespToVal, simStateToVal]
    · simp only [h, hf, Bool.false_eq_true, ↓reduceIte, Option.map_some,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun spkSkRaw => ?_
      refine bind_congr fun spkPkRaw => ?_
      refine bind_congr fun rSpk => ?_
      refine bind_congr fun spkSig => ?_
      refine bind_congr fun seed => ?_
      refine bind_congr fun kp => ?_
      refine bind_congr fun rPq => ?_
      refine bind_congr fun pqSig => ?_
      simp [encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal,
        spkBundleEntryToVal]

theorem genOpkGdhB_eval (xV : Var Γ₄ (.prod .nat (.prod .nat .nat)))
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hx : env.get (Ext.wk xV) = (u.val, (j.val, o.val))) :
    (genOpkGdhB S K paV smV bStV xV).eval env =
      encSimRS <$>
        if pa.2.2.2.2.2.2.2.2.1 then
          fgGenOPKGdhOpk pa.2.2.2.2.2.2.2.2.2.1 S pa.2.1 u j o st
        else
          fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
            pa.1 pa.2.1 (.genOPK u j o) st := by
  unfold genOpkGdhB fgGenOPKGdhOpk fgKeyIndStep
  gdh_simp [hpa, hsm, hbSt, hx, min_N_recv_spk_tot u, min_N_opk_opk_tot u j,
    List.take_of_length_le, hB.base_le.opkEntries_le,
    nat3_beq, opkFlatIdx, opkSlotFlatIdx, unifGdh, sampleScalar32, primGdhQ]
  cases pa.2.2.2.2.2.2.2.2.1 <;>
  · by_cases h :
        (st.base.opkEntries.any fun x => x.1.1 == ↑u && (x.1.2.1 == ↑j && x.1.2.2 == ↑o)) = true
    · simp [h, encSimRS, keyIndRespToVal, simStateToVal]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.false_and,
        map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun opkSkRaw => ?_
      refine bind_congr fun opkPkRaw => ?_
      simp [encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal, opkEntryToVal]

omit hpa hB in
theorem registerGdhB_eval (skV : Var Γ₄ (B 32)) (sk : Bytes)
    (hsk : env.get (Ext.wk skV) = sk) :
    (registerGdhB smV bStV skV).eval env =
      encSimRS <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.registerKey sk) st := by
  unfold registerGdhB fgKeyIndStep
  gdh_simp [hsm, hbSt, hsk, primGdhQ]
  try erw [hsk]
  by_cases h : sk.length = 32
  · simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bne_self_eq_false, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    refine bind_congr fun pk => ?_
    refine bind_congr fun wPk => ?_
    simp [encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal]
  · simp [h, encSimRS, keyIndRespToVal, simStateToVal]

theorem corruptGdh_eval (uV : Var Γ₄ .nat) (u : Fin S.N_id)
    (hu : env.get (Ext.wk uV) = u.val) :
    (wrapBase paV smV (corruptB K bStV uV)).eval env =
      encGdhRS pa <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.corruptIK u) st := by
  unfold wrapBase fgKeyIndStep
  simp only [bindV, liftBase_eval, embedPrim_gapDhFrag, Comp.eval,
    corruptB_eval true S K bStV env st.base hbSt hB.base_le uV u hu, embedPrim_map']
  gdh_simp [hpa, hsm, pqxdhKeyIndImplPrim]
  rcases hf : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨idx, e⟩
  · simp [hf, encGdhRS, encRS, keyIndRespToVal, simStateToVal]
  · simp [hf, encGdhRS, encRS, keyIndRespToVal, simStateToVal]

theorem testGdh_eval (sidV : Var Γ₄ sessionIdTy) (sid : SessionId S)
    (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid) :
    (wrapBase paV smV (testB K bStV sidV)).eval env =
      encGdhRS pa <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.testSession sid) st := by
  unfold wrapBase fgKeyIndStep
  simp only [bindV, liftBase_eval, embedPrim_gapDhFrag, Comp.eval,
    testB_eval true S K bStV env st.base hbSt hB.base_le sidV sid hsid, embedPrim_map']
  gdh_simp [hpa, hsm, pqxdhKeyIndImplPrim]
  by_cases hf : isKeyIndSessionTestable st.base sid = true
  · rcases hs : st.base.sessions.find? (fun e => e.sid == sid) with _ | e
    · rcases hr : st.base.respSessions.find? (fun r => r.sid == sid) with _ | r
      · simp [hf, hs, hr, encGdhRS, encRS, keyIndRespToVal, simStateToVal]
      · simp [hf, hs, hr, StateT.run_set, encGdhRS, encRS, keyIndRespToVal, simStateToVal]
    · simp [hf, hs, StateT.run_set, encGdhRS, encRS, keyIndRespToVal, simStateToVal]
  · simp only [Bool.not_eq_true] at hf
    simp [hf, encGdhRS, encRS, keyIndRespToVal, simStateToVal]

theorem revealGdh_eval (sidV : Var Γ₄ sessionIdTy) (sid : SessionId S)
    (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid) :
    (wrapBase paV smV (revealB K bStV sidV)).eval env =
      encGdhRS pa <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.revealSessionKey sid) st := by
  unfold wrapBase fgKeyIndStep
  simp only [bindV, liftBase_eval, embedPrim_gapDhFrag, Comp.eval,
    revealB_eval true S K bStV env st.base hbSt hB.base_le sidV sid hsid, embedPrim_map']
  gdh_simp [hpa, hsm, pqxdhKeyIndImplPrim]
  rcases hs : st.base.sessions.find? (fun e => e.sid == sid) with _ | e
  · rcases hr : st.base.respSessions.find? (fun r => r.sid == sid) with _ | r
    · simp only [hs, hr, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind,
        embedPrim_pure', map_pure, encGdhRS, encRS, keyIndRespToVal, simStateToVal,
        keyIndStateToVal]
    · cases ht : r.tested <;>
        simp only [hs, hr, ht, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
          Function.comp_def, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          embedPrim_pure', pure_bind, encGdhRS, encRS, keyIndRespToVal, simStateToVal,
          keyIndStateToVal, keyIndRenc, drKeyV]
  · cases ht : e.tested <;>
      simp only [hs, ht, Bool.false_eq_true, ↓reduceIte, map_eq_bind_pure_comp,
        Function.comp_def, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        embedPrim_pure', pure_bind, encGdhRS, encRS, keyIndRespToVal, simStateToVal,
        keyIndStateToVal, keyIndRenc, drKeyV]

theorem revealSpkGdh_eval (xV : Var Γ₄ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (wrapBase paV smV (revealSpkB K bStV xV)).eval env =
      encGdhRS pa <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.revealSpkSk u j) st := by
  unfold wrapBase fgKeyIndStep
  simp only [bindV, liftBase_eval, embedPrim_gapDhFrag, Comp.eval,
    revealSpkB_eval true S K bStV env st.base hbSt hB.base_le xV u j hx, embedPrim_map']
  gdh_simp [hpa, hsm, pqxdhKeyIndImplPrim]
  rcases hf : st.base.spkBundles.find? (fun x => x.1 == (↑u, ↑j)) with _ | ⟨idx, b⟩
  · simp [hf, encGdhRS, encRS, keyIndRespToVal, simStateToVal]
  · simp [hf, encGdhRS, encRS, keyIndRespToVal, simStateToVal]

/-! ## Accept Branch Lemmas -/

omit [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] hpa hsm hbSt hB in
theorem kyberCheck_eval_eq (used : List (ℕ × UInt32 × UInt32 × List UInt8))
    (k : ℕ) (pqId sId : UInt32) (ekA : List UInt8) :
    (if (used.any fun x => k == x.1 && (pqId == x.2.1 && (sId == x.2.2.1 && ekA == x.2.2.2))) = true
     then (false, used)
     else (true, (k, pqId, sId, ekA) :: used)) =
    checkAndMarkKyberBaseKeySeen used k pqId sId ekA := by
  unfold checkAndMarkKyberBaseKeySeen
  have h : (used.any fun x => k == x.1 && (pqId == x.2.1 && (sId == x.2.2.1 && ekA == x.2.2.2))) =
      used.contains (k, pqId, sId, ekA) := by
    rw [List.contains_eq_any_beq]; congr 1
  rw [h]

omit hpa in
set_option maxHeartbeats 800000 in
theorem finishAcceptGdhC_eval {Γ₅ Γ₆ Γ₇ : List PT}
    [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (hasOpk : Bool) (xV : Var Γ₄ accQTy)
    (keV : Var Γ₅ (.prod .nat principalEntryTy))
    (beV : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOptE : Expr pqxdhOps Δ (.opt (B 32)))
    (opksE : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedOE : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedNE : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kybE : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchRV : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy)))
    (sid : SessionId S) (kVal jVal thirdVal : Nat) (hdr : HandshakeHdr)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes)
    (opks' : List ((Nat × Nat × Nat) × OpkEntry))
    (usedO' usedN' : List (Nat × Nat × Nat))
    (kyb' : List (Nat × KeyId × KeyId × Bytes))
    (drKey : DRKey) (fgL' : List FgPatchEntry)
    (hx : env.get (Ext.wk xV) = (kVal, (jVal, (thirdVal, handshakeHdrToVal hdr))))
    (hsid : (if hasOpk then Sum.inr (Sum.inr (Sum.inl (kVal, (jVal, thirdVal))))
             else Sum.inr (Sum.inr (Sum.inr (kVal, (jVal, thirdVal))))) = sidV sid)
    (hke : env.get (Ext.wk keV) = (kVal, principalEntryToVal kEntry))
    (hbe : env.get (Ext.wk beV) = ((kVal, jVal), spkBundleEntryToVal bEntry))
    (hopkPk : opkPkOptE.eval env = opkPk?)
    (hopks : opksE.eval env =
      opks'.map (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal))
    (husedO : usedOE.eval env = usedO'.map (fun (u, j, o) => (u, (j, o))))
    (husedN : usedNE.eval env = usedN'.map (fun (u, j, l) => (u, (j, l))))
    (hkyb : kybE.eval env =
      kyb'.map (fun (u, pqId, sId, ek) => (u, (pqId, (sId, ek)))))
    (hpatch : env.get (Ext.wk patchRV) = (drKeyToVal drKey, fgL'.map fgPatchEntryToVal)) :
    (finishAcceptGdhC S K smV bStV hasOpk xV keV beV opkPkOptE opksE usedOE usedNE kybE
      patchRV).eval env =
      encSimRS <$> do
        let senderHonestOpt ← embedPrim (spec := gapDhOracleSpec)
          (findHonestPrincipalPrim S st.base.principals hdr.ikAPk)
        let rInit : KeyIndRespEntry S := {
          sid          := sid
          respIkPk     := kEntry.ikAPk
          spkPk        := bEntry.spkPk
          opkPk?       := opkPk?
          pqspkPk      := bEntry.pqspkPk
          hdr          := hdr
          senderHonest := senderHonestOpt.isSome
          drKeyReal    := drKey
          drKeyRand    := drKey
        }
        let drKeyRand ← choosePartnerDrKeyRandGdh st.base.sessions rInit
        let base' : KeyIndState S := { st.base with
          opkEntries       := opks'
          usedRecvOPK      := usedO'
          usedRecvNoOPK    := usedN'
          seenKyberBaseKeys := kyb'
          respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
        }
        let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
        match senderHonestOpt with
        | some _ => return (.acceptFreshResp, st')
        | none   => return (.drKeyResp drKey, st') := by
  unfold finishAcceptGdhC
  gdh_simp [findHonestC_eval, hopkPk, hopks, husedO, husedN, hkyb, hpatch,
    decPrin_enc, decPrin_enc', List.take_of_length_le, hB.base_le.principals_le,
    hx, hke, hbe, hbSt, principalEntryToVal, spkBundleEntryToVal, handshakeHdrToVal,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  try erw [hx]
  try simp only [handshakeHdrToVal, hdrV]
  try rw [decPrin_enc]
  try simp only [List.take_of_length_le hB.base_le.principals_le]
  refine bind_congr fun shOpt => ?_
  rw [chooseRespRandC_eval S K bStV .zero _ st.base.sessions
    { sid          := sid
      respIkPk     := kEntry.ikAPk
      spkPk        := bEntry.spkPk
      opkPk?       := opkPk?
      pqspkPk      := bEntry.pqspkPk
      hdr          := hdr
      senderHonest := shOpt.isSome
      drKeyReal    := drKey
      drKeyRand    := drKey }
    (by simp [hbSt, keyIndStateToVal])
    (by
      dsimp only [keyIndRespEntryToVal]
      rw [← hsid]
      cases hasOpk <;> cases shOpt <;>
        gdh_simp [hx, hke, hbe, hpatch, principalEntryToVal, spkBundleEntryToVal])
    hB.base_le.sessions_le]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun drKeyRand => ?_
  cases shOpt <;>
    (simp only [pure_bind, encSimRS, simStateToVal, keyIndStateToVal, List.map_cons,
       keyIndRespEntryToVal];
     rw [← hsid];
     cases hasOpk <;>
       gdh_simp [hsm, hbSt, hx, hke, hbe, hpatch, keyIndRespToVal, simStateToVal,
         keyIndStateToVal, principalEntryToVal, spkBundleEntryToVal, List.map_cons, pure_bind])

set_option maxHeartbeats 1000000 in
theorem acceptOpkGdhB_eval_dh (xV : Var Γ₄ accQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (o.val, handshakeHdrToVal hdr))))
    (hOpkMode : pa.2.2.2.2.2.2.2.2.1 = false) :
    (acceptOpkGdhB S K paV smV bStV xV).eval env =
      encSimRS <$> fgRunAcceptOPKGdh S K k j o hdr st := by
  unfold acceptOpkGdhB fgRunAcceptOPKGdh
  obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := hdr
  simp only [bindV, letV_eval, caseOptV, Comp.eval, gPrim_eval,
    koskSenderOkPowsC_eval S K bStV (smPows (v smV)) (hdIkAPk (qHdr (v xV))) env st.advKeyPows
      (by simp [smPows, v, Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hpa, hsm, hbSt, hx, hOpkMode, List.take_of_length_le,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.usedRecvOPK_le, hB.base_le.usedKyberTriples_le,
    handshakeHdrToVal, primGdhQ]
  try erw [hx]
  try simp only [handshakeHdrToVal, hdrV]
  rw [decPrin_enc]
  have hu : (st.base.usedRecvOPK.any fun x => x.1 == ↑k && (x.2.1 == ↑j && x.2.2 == ↑o)) =
      st.base.usedRecvOPK.contains (↑k, ↑j, ↑o) := by
    rw [List.contains_eq_any_beq]; congr 1; funext ⟨_, _, _⟩
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]; omega
  rw [hu]
  rcases oId with _ | oid
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  by_cases hg : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j && oid == UInt32.ofNat ↑o &&
      ikA.length == 32 && ekA.length == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, encSimRS, keyIndRespToVal, simStateToVal]
  by_cases h1 : (↑k, ↑j, ↑o) ∈ st.base.usedRecvOPK
  · simp [hg, h1, encSimRS, keyIndRespToVal, simStateToVal]
  have hg' : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j &&
      (some oid == some (UInt32.ofNat ↑o)) &&
      ikA.length == 32 && ekA.length == 32) = true := hg
  simp only [hg, hg', h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem,
    map_eq_bind_pure_comp, bind_assoc]
  try simp only [List.take_of_length_le hB.base_le.principals_le]
  refine bind_congr fun sOk => ?_
  cases sOk
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  rcases hk : st.base.principals.find? (fun x => x.1 == ↑k) with _ | ⟨k', kE⟩
  · simp [hk, encSimRS, keyIndRespToVal, simStateToVal]
  rcases hb : st.base.spkBundles.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) with _ | ⟨b', bE⟩
  · simp [hk, hb, nat2_beq, encSimRS, keyIndRespToVal, simStateToVal]
  rcases ho : st.base.opkEntries.find? (fun x => x.1.1 == ↑k && (x.1.2.1 == ↑j && x.1.2.2 == ↑o))
    with _ | ⟨o', oE⟩
  · simp [hk, hb, ho, nat2_beq, nat3_beq, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hk, hb, ho, nat2_beq, nat3_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.map_some]
  by_cases hc : oE.consumed = true
  · simp [hc, Prod.map, opkEntryToVal, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hc, Prod.map, id, opkEntryToVal, spkBundleEntryToVal, Bool.false_eq_true, ↓reduceIte,
    bne, bind_assoc]
  erw [kyberCheck_eval_eq st.base.seenKyberBaseKeys (↑k) pqId sId ekA]
  refine bind_congr fun canon => ?_
  refine bind_congr fun dh1Z => ?_
  refine bind_congr fun dh2Z => ?_
  refine bind_congr fun dh4 => ?_
  refine bind_congr fun ssOpt => ?_
  by_cases hchk : (!((checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys (↑k) pqId sId ekA).1 &&
      canon && (!dh1Z == List.replicate 32 0) && (!dh2Z == List.replicate 32 0) &&
      (!dh4 == List.replicate 32 0))) = true
  · simp only [hchk, ↓reduceIte]
    simp [encSimRS, keyIndRespToVal, simStateToVal]
  · simp only [Bool.not_eq_true] at hchk
    simp only [hchk, Bool.false_eq_true, ↓reduceIte]
    rcases ssOpt with _ | ss
    · simp [encSimRS, keyIndRespToVal, simStateToVal]
    gdh_simp [computePosC_eval, mkSecretPosC_eval, hx, spkBundleEntryToVal, principalEntryToVal,
      handshakeHdrToVal, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    try erw [hx]
    try simp only [handshakeHdrToVal, hdrV]
    refine bind_congr fun pos1 => ?_
    refine bind_congr fun pos2 => ?_
    refine bind_congr fun pos3 => ?_
    refine bind_congr fun pos4 => ?_
    rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 (some pos4) ss st.fgL
      rfl rfl rfl rfl rfl (by gdh_simp [hsm])]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨drKey, fgL'⟩ => ?_
    have hke' : k' = ↑k := by
      have := List.find?_some hk; simp at this; exact this
    have hbe' : b' = (↑k, ↑j) := by
      have := List.find?_some hb; simp at this; exact Prod.ext this.1 this.2
    subst hke' hbe'
    rw [finishAcceptGdhC_eval S K smV bStV _ st (by gdh_simp [hsm]) (by gdh_simp [hbSt]) hB
      true xV _ _ _ _ _ _ _ _
      (.recvOPK k j o) k.val j.val o.val ⟨ikA, ekA, sId, some oid, pqId, ct⟩ kE bE
      (some oE.opkPk)
      (st.base.opkEntries.map (fun (idx, e) =>
        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e)))
      ((k.val, j.val, o.val) :: st.base.usedRecvOPK)
      st.base.usedRecvNoOPK
      (checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val pqId sId ekA).2
      drKey fgL' (by gdh_simp [hx]) rfl rfl rfl
      (by gdh_simp [opkEntryToVal])
      (by
        gdh_simp [hbSt, hx, List.take_of_length_le, hB.base_le.opkEntries_le, nat3_beq]
        congr 1; funext x; split_ifs <;> rfl)
      (by gdh_simp [hbSt, hx, List.map_cons])
      (by gdh_simp [hbSt])
      (by gdh_simp [kyberCheck_eval_eq])
      rfl]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, nat3_beq]
    rfl

set_option maxHeartbeats 1000000 in
theorem acceptOpkGdhB_eval_opk (xV : Var Γ₄ accQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (o.val, handshakeHdrToVal hdr))))
    (hOpkMode : pa.2.2.2.2.2.2.2.2.1 = true) :
    (acceptOpkGdhB S K paV smV bStV xV).eval env =
      encSimRS <$> fgRunAcceptOPKGdhOpk S K k j o hdr st := by
  unfold acceptOpkGdhB fgRunAcceptOPKGdhOpk
  obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := hdr
  simp only [bindV, letV_eval, caseOptV, Comp.eval, gPrim_eval,
    koskSenderOkPowsC_eval S K bStV (smPows (v smV)) (hdIkAPk (qHdr (v xV))) env st.advKeyPows
      (by simp [smPows, v, Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hpa, hsm, hbSt, hx, hOpkMode, List.take_of_length_le,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.usedRecvOPK_le, hB.base_le.usedKyberTriples_le,
    handshakeHdrToVal, primGdhQ]
  try erw [hx]
  try simp only [handshakeHdrToVal, hdrV]
  rw [decPrin_enc]
  have hu : (st.base.usedRecvOPK.any fun x => x.1 == ↑k && (x.2.1 == ↑j && x.2.2 == ↑o)) =
      st.base.usedRecvOPK.contains (↑k, ↑j, ↑o) := by
    rw [List.contains_eq_any_beq]; congr 1; funext ⟨_, _, _⟩
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]; omega
  rw [hu]
  rcases oId with _ | oid
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  by_cases hg : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j && oid == UInt32.ofNat ↑o &&
      ikA.length == 32 && ekA.length == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, encSimRS, keyIndRespToVal, simStateToVal]
  by_cases h1 : (↑k, ↑j, ↑o) ∈ st.base.usedRecvOPK
  · simp [hg, h1, encSimRS, keyIndRespToVal, simStateToVal]
  have hg' : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j &&
      (some oid == some (UInt32.ofNat ↑o)) &&
      ikA.length == 32 && ekA.length == 32) = true := hg
  simp only [hg, hg', h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem,
    map_eq_bind_pure_comp, bind_assoc]
  try simp only [List.take_of_length_le hB.base_le.principals_le]
  refine bind_congr fun sOk => ?_
  cases sOk
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  rcases hk : st.base.principals.find? (fun x => x.1 == ↑k) with _ | ⟨k', kE⟩
  · simp [hk, encSimRS, keyIndRespToVal, simStateToVal]
  rcases hb : st.base.spkBundles.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) with _ | ⟨b', bE⟩
  · simp [hk, hb, nat2_beq, encSimRS, keyIndRespToVal, simStateToVal]
  rcases ho : st.base.opkEntries.find? (fun x => x.1.1 == ↑k && (x.1.2.1 == ↑j && x.1.2.2 == ↑o))
    with _ | ⟨o', oE⟩
  · simp [hk, hb, ho, nat2_beq, nat3_beq, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hk, hb, ho, nat2_beq, nat3_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.map_some]
  by_cases hc : oE.consumed = true
  · simp [hc, Prod.map, opkEntryToVal, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hc, Prod.map, id, opkEntryToVal, spkBundleEntryToVal, Bool.false_eq_true, ↓reduceIte,
    bne, bind_assoc]
  erw [kyberCheck_eval_eq st.base.seenKyberBaseKeys (↑k) pqId sId ekA]
  refine bind_congr fun canon => ?_
  refine bind_congr fun dh1Z => ?_
  refine bind_congr fun dh2Z => ?_
  refine bind_congr fun ssOpt => ?_
  by_cases hchk : (!((checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys (↑k) pqId sId ekA).1 &&
      canon && (!dh1Z == List.replicate 32 0) && (!dh2Z == List.replicate 32 0))) = true
  · simp only [hchk, ↓reduceIte]
    simp [encSimRS, keyIndRespToVal, simStateToVal]
  · simp only [Bool.not_eq_true] at hchk
    simp only [hchk, Bool.false_eq_true, ↓reduceIte]
    rcases ssOpt with _ | ss
    · simp [encSimRS, keyIndRespToVal, simStateToVal]
    gdh_simp [computePosC_eval, hx, opkEntryToVal, spkBundleEntryToVal, principalEntryToVal,
      handshakeHdrToVal, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    try erw [hx]
    try simp only [handshakeHdrToVal, hdrV]
    refine bind_congr fun pos1 => ?_
    refine bind_congr fun pos2 => ?_
    refine bind_congr fun pos3 => ?_
    refine bind_congr fun pos4 => ?_
    rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 (some pos4) ss st.fgL
      rfl rfl rfl rfl rfl (by gdh_simp [hsm])]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨drKey, fgL'⟩ => ?_
    have hke' : k' = ↑k := by
      have := List.find?_some hk; simp at this; exact this
    have hbe' : b' = (↑k, ↑j) := by
      have := List.find?_some hb; simp at this; exact Prod.ext this.1 this.2
    subst hke' hbe'
    rw [finishAcceptGdhC_eval S K smV bStV _ st (by gdh_simp [hsm]) (by gdh_simp [hbSt]) hB
      true xV _ _ _ _ _ _ _ _
      (.recvOPK k j o) k.val j.val o.val ⟨ikA, ekA, sId, some oid, pqId, ct⟩ kE bE
      (some oE.opkPk)
      (st.base.opkEntries.map (fun (idx, e) =>
        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e)))
      ((k.val, j.val, o.val) :: st.base.usedRecvOPK)
      st.base.usedRecvNoOPK
      (checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val pqId sId ekA).2
      drKey fgL' (by gdh_simp [hx]) rfl rfl rfl
      (by gdh_simp [opkEntryToVal])
      (by
        gdh_simp [hbSt, hx, List.take_of_length_le, hB.base_le.opkEntries_le, nat3_beq]
        congr 1; funext x; split_ifs <;> rfl)
      (by gdh_simp [hbSt, hx, List.map_cons])
      (by gdh_simp [hbSt])
      (by gdh_simp [kyberCheck_eval_eq])
      rfl]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, nat3_beq]
    rfl

omit hpa in
set_option maxHeartbeats 1000000 in
theorem acceptNoOpkGdhB_eval (xV : Var Γ₄ accQTy)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (l.val, handshakeHdrToVal hdr)))) :
    (acceptNoOpkGdhB S K smV bStV xV).eval env =
      encSimRS <$> fgRunAcceptNoOPKGdh S K k j l hdr st := by
  unfold acceptNoOpkGdhB fgRunAcceptNoOPKGdh
  obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := hdr
  simp only [bindV, letV_eval, caseOptV, Comp.eval, gPrim_eval,
    koskSenderOkPowsC_eval S K bStV (smPows (v smV)) (hdIkAPk (qHdr (v xV))) env st.advKeyPows
      (by simp [smPows, v, Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hsm, hbSt, hx, List.take_of_length_le,
    hB.base_le.principals_le, hB.base_le.spkBundles_le,
    hB.base_le.usedRecvNoOPK_le, hB.base_le.usedKyberTriples_le,
    handshakeHdrToVal, primGdhQ]
  try erw [hx]
  try simp only [handshakeHdrToVal, hdrV]
  rw [decPrin_enc]
  have hu : (st.base.usedRecvNoOPK.any fun x => x.1 == ↑k && (x.2.1 == ↑j && x.2.2 == ↑l)) =
      st.base.usedRecvNoOPK.contains (↑k, ↑j, ↑l) := by
    rw [List.contains_eq_any_beq]; congr 1; funext ⟨_, _, _⟩
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq]; omega
  rw [hu]
  rcases oId with _ | oid
  swap
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  simp only [beq_self_eq_true, Bool.and_true]
  by_cases hg : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j &&
      ikA.length == 32 && ekA.length == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, encSimRS, keyIndRespToVal, simStateToVal]
  by_cases h1 : (↑k, ↑j, ↑l) ∈ st.base.usedRecvNoOPK
  · simp [hg, h1, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hg, h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.contains_iff_mem,
    map_eq_bind_pure_comp, bind_assoc]
  try simp only [List.take_of_length_le hB.base_le.principals_le]
  refine bind_congr fun sOk => ?_
  cases sOk
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  rcases hk : st.base.principals.find? (fun x => x.1 == ↑k) with _ | ⟨k', kE⟩
  · simp [hk, encSimRS, keyIndRespToVal, simStateToVal]
  rcases hb : st.base.spkBundles.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) with _ | ⟨b', bE⟩
  · simp [hk, hb, nat2_beq, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hk, hb, nat2_beq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.map_some, Prod.map, id, spkBundleEntryToVal,
    bne, bind_assoc]
  erw [kyberCheck_eval_eq st.base.seenKyberBaseKeys (↑k) pqId sId ekA]
  refine bind_congr fun canon => ?_
  refine bind_congr fun dh1Z => ?_
  refine bind_congr fun dh2Z => ?_
  refine bind_congr fun ssOpt => ?_
  by_cases hchk : (!((checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys (↑k) pqId sId ekA).1 &&
      canon && (!dh1Z == List.replicate 32 0) && (!dh2Z == List.replicate 32 0))) = true
  · simp only [hchk, ↓reduceIte]
    simp [encSimRS, keyIndRespToVal, simStateToVal]
  · simp only [Bool.not_eq_true] at hchk
    simp only [hchk, Bool.false_eq_true, ↓reduceIte]
    rcases ssOpt with _ | ss
    · simp [encSimRS, keyIndRespToVal, simStateToVal]
    gdh_simp [computePosC_eval, hx, spkBundleEntryToVal, principalEntryToVal,
      handshakeHdrToVal, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    try erw [hx]
    try simp only [handshakeHdrToVal, hdrV]
    refine bind_congr fun pos1 => ?_
    refine bind_congr fun pos2 => ?_
    refine bind_congr fun pos3 => ?_
    rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 none ss st.fgL
      rfl rfl rfl rfl rfl (by gdh_simp [hsm])]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine bind_congr fun ⟨drKey, fgL'⟩ => ?_
    have hke' : k' = ↑k := by
      have := List.find?_some hk; simp at this; exact this
    have hbe' : b' = (↑k, ↑j) := by
      have := List.find?_some hb; simp at this; exact Prod.ext this.1 this.2
    subst hke' hbe'
    rw [finishAcceptGdhC_eval S K smV bStV _ st (by gdh_simp [hsm]) (by gdh_simp [hbSt]) hB
      false xV _ _ _ _ _ _ _ _
      (.recvNoOPK k j l) k.val j.val l.val ⟨ikA, ekA, sId, none, pqId, ct⟩ kE bE
      none
      st.base.opkEntries
      st.base.usedRecvOPK
      ((k.val, j.val, l.val) :: st.base.usedRecvNoOPK)
      (checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val pqId sId ekA).2
      drKey fgL' (by gdh_simp [hx]) rfl rfl rfl
      rfl
      (by gdh_simp [hbSt])
      (by gdh_simp [hbSt])
      (by gdh_simp [hbSt, hx, List.map_cons])
      (by gdh_simp [kyberCheck_eval_eq])
      rfl]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    rfl

end BranchEval

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
