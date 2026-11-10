/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEnc
import VCVio.EvalDist.Monad.Basic

/-!
# Evaluation of the Multi-Key Game Steps

Proves that `hmKeyC`, `hmEncPreC`, `encPostC`, and `hmForgeC` evaluate to `hmKeyP`, `hmEncPre`,
`HmEncCont.post`, and `hmForgeP`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthAead
open SignalPqxdh.Security.ReductionDsl.AuthPrf hiding queryPrim_eval
open FgGapDh
open OracleSpec OracleComp

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

theorem find_natKey_map {α β : Type} (f : α → β) (xs : List (Nat × α)) (i : Nat) :
    (xs.map (fun e => (e.1, f e.2))).find? (fun e => e.1 == i) =
      (xs.lookup i).map (fun a => (i, f a)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, a⟩
    by_cases h : k = i
    · subst h
      simp only [List.map_cons, List.find?_cons, beq_self_eq_true, List.lookup, Option.map_some]
    · have h' : (i == k) = false := beq_false_of_ne (Ne.symm h)
      have h'' : (k == i) = false := beq_false_of_ne h
      simp only [List.map_cons, List.find?_cons, h'', List.lookup, h']
      exact ih

theorem find_natKey {α : Type} (xs : List (Nat × α)) (i : Nat) :
    xs.find? (fun e => e.1 == i) = (xs.lookup i).map (fun a => (i, a)) := by
  simpa using find_natKey_map id xs i

theorem foldr_ite_filter {α : Type} (p : α → Bool) (l : List α) :
    l.foldr (fun x acc => if p x then acc else x :: acc) [] = l.filter (fun x => !p x) := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : p x <;> simp [h, ih]

@[simp] theorem muStToVal_keys (st : PrfHmacMuState) :
    (muStToVal st).1 =
      st.keys.map (fun e => ((.inr e.1 : muKeyIdTy.denote), (e.2.1, msgKeysToVal e.2.2))) := rfl
@[simp] theorem muStToVal_chal (st : PrfHmacMuState) :
    (muStToVal st).2.1 = st.chal.map (fun e => ((.inr e.1 : muKeyIdTy.denote), e.2)) := rfl
@[simp] theorem muStToVal_pending (st : PrfHmacMuState) : (muStToVal st).2.2.1 = st.pending := rfl
@[simp] theorem muStToVal_bad (st : PrfHmacMuState) : (muStToVal st).2.2.2 = st.bad := rfl

@[simp] theorem muStToValS_keys (S : Setup) (st : PrfHmacMuState) :
    (muStToValS S st).1 =
      st.keys.map (fun e => (natToMuKeyIdVal S e.1, (e.2.1, msgKeysToVal e.2.2))) := rfl
@[simp] theorem muStToValS_chal (S : Setup) (st : PrfHmacMuState) :
    (muStToValS S st).2.1 = st.chal.map (fun e => (natToMuKeyIdVal S e.1, e.2)) := rfl
@[simp] theorem muStToValS_pending (S : Setup) (st : PrfHmacMuState) :
    (muStToValS S st).2.2.1 = st.pending := rfl
@[simp] theorem muStToValS_bad (S : Setup) (st : PrfHmacMuState) :
    (muStToValS S st).2.2.2 = st.bad := rfl

def sidEqVal : sessionIdTy.denote → sessionIdTy.denote → Bool
  | .inl a, .inl b => (a.1 == b.1) && (a.2 == b.2)
  | .inr (.inl a), .inr (.inl b) => (a.1 == b.1) && (a.2 == b.2)
  | .inr (.inr (.inl a)), .inr (.inr (.inl b)) =>
      (a.1 == b.1) && ((a.2.1 == b.2.1) && (a.2.2 == b.2.2))
  | .inr (.inr (.inr a)), .inr (.inr (.inr b)) =>
      (a.1 == b.1) && ((a.2.1 == b.2.1) && (a.2.2 == b.2.2))
  | _, _ => false

def muKeyIdEqVal : muKeyIdTy.denote → muKeyIdTy.denote → Bool
  | .inl x, .inl y => sidEqVal x y
  | .inr x, .inr y => x == y
  | _, _ => false

@[simp] theorem muKeyIdEq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ muKeyIdTy) (env : Env Γ) :
    (muKeyIdEq a b).eval env = muKeyIdEqVal (a.eval env) (b.eval env) := by
  simp only [muKeyIdEq, sidEq, eLet2, eLet, eCaseSum, v, nat2Eq_eval, nat3Eq_eval, natEq_eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]
  rcases a.eval env with (x | x | x | x) | x <;>
    rcases b.eval env with (y | y | y | y) | y <;>
    rfl

theorem muKeyIdEqVal_iff (x y : muKeyIdTy.denote) :
    muKeyIdEqVal x y = true ↔ x = y := by
  rcases x with (⟨x1, x2⟩ | ⟨x1, x2⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩) | x <;>
    rcases y with (⟨y1, y2⟩ | ⟨y1, y2⟩ | ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩) | y <;>
    simp [muKeyIdEqVal, sidEqVal, Bool.and_eq_true, beq_iff_eq]

theorem natToMuKeyIdVal_inj (S : Setup) : Function.Injective (natToMuKeyIdVal S) := by
  intro i₁ i₂ h
  unfold natToMuKeyIdVal at h
  by_cases h1a : i₁ < S.N_send_opk_tot
  · by_cases h2a : i₂ < S.N_send_opk_tot
    · simp only [h1a, h2a, ↓reduceIte, Sum.inl.injEq, Prod.mk.injEq] at h
      have d1 := Nat.div_add_mod i₁ S.N_send_opk
      have d2 := Nat.div_add_mod i₂ S.N_send_opk
      rw [h.1, h.2] at d1
      omega
    · by_cases h2b : i₂ < S.N_send_tot <;> simp [h1a, h2a, h2b] at h
  · by_cases h1b : i₁ < S.N_send_tot
    · by_cases h2a : i₂ < S.N_send_opk_tot
      · simp [h1a, h1b, h2a] at h
      · by_cases h2b : i₂ < S.N_send_tot
        · simp [h1a, h1b, h2a, h2b] at h
          have d1 := Nat.div_add_mod (i₁ - S.N_send_opk_tot) S.N_send_no_opk
          have d2 := Nat.div_add_mod (i₂ - S.N_send_opk_tot) S.N_send_no_opk
          rw [h.1, h.2] at d1
          omega
        · simp [h1a, h1b, h2a, h2b] at h
    · have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
      by_cases h2a : i₂ < S.N_send_opk_tot
      · simp [h1a, h1b, h2a] at h
      · by_cases h2b : i₂ < S.N_send_tot
        · simp [h1a, h1b, h2a, h2b] at h
        · simp only [h1a, h1b, h2a, h2b, ite_false] at h
          have h' : i₁ - S.N_send_tot = i₂ - S.N_send_tot := Sum.inr.inj h
          omega

theorem natToMuKeyIdVal_add_send_tot (S : Setup) (rc : Nat) :
    natToMuKeyIdVal S (S.N_send_tot + rc) = .inr rc := by
  unfold natToMuKeyIdVal
  have hLe : S.N_send_opk_tot ≤ S.N_send_tot := Nat.le_add_right _ _
  have h1 : ¬ (S.N_send_tot + rc < S.N_send_opk_tot) := by omega
  have h2 : ¬ (S.N_send_tot + rc < S.N_send_tot) := by omega
  simp [h1, h2]

theorem find_injKey_map {κ α β : Type} (encodeKey : Nat → κ)
    (hInj : Function.Injective encodeKey)
    (eqK : κ → κ → Bool) (heqK : ∀ x y, eqK x y = true ↔ x = y)
    (f : α → β) (xs : List (Nat × α)) (i : Nat) :
    (xs.map (fun e => (encodeKey e.1, f e.2))).find? (fun e => eqK e.1 (encodeKey i)) =
      (xs.lookup i).map (fun a => (encodeKey i, f a)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, a⟩
    by_cases h : k = i
    · subst h
      have ht : eqK (encodeKey k) (encodeKey k) = true := (heqK _ _).mpr rfl
      simp only [List.map_cons, List.find?_cons, ht, List.lookup, beq_self_eq_true, Option.map_some]
    · have h' : (i == k) = false := beq_false_of_ne (Ne.symm h)
      have hf : eqK (encodeKey k) (encodeKey i) = false := by
        rw [← Bool.not_eq_true, heqK]
        exact fun he => h (hInj he)
      simp only [List.map_cons, List.find?_cons, hf, List.lookup, h']
      exact ih

theorem hm_bind_congr_leaves {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : α → Prop} {m : OracleComp spec α} {f g : α → OracleComp spec β}
    (hm : AllLeaves P m) (h : ∀ a, P a → f a = g a) : m >>= f = m >>= g := by
  induction m using OracleComp.inductionOn with
  | pure a => exact h a hm
  | query_bind q k ih =>
    simp only [bind_assoc]
    exact bind_congr fun u => ih u (hm u)

theorem hmKeyP_frame (i : Nat) (st : PrfHmacMuState) :
    AllLeaves (fun r : (ℕ × MessageKeys) × PrfHmacMuState => r.2.chal = st.chal ∧
      r.2.pending = st.pending ∧ r.2.bad = st.bad ∧ r.2.keys.length ≤ st.keys.length + 1)
      (hmKeyP i st) := by
  unfold hmKeyP
  split
  · exact AllLeaves.pure ⟨rfl, rfl, rfl, Nat.le_succ _⟩
  · exact AllLeaves.bind_const _ fun _ => AllLeaves.pure ⟨rfl, rfl, rfl, by simp⟩

@[simp] theorem bytesTake_eval {Γ : List PT} (w : ℕ+)
    (n : Expr pqxdhOps Γ .nat) (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (bytesTake w n x).eval env = (x.eval env).take (n.eval env) := rfl

@[simp] theorem bytesDrop_eval {Γ : List PT} (w : ℕ+)
    (n : Expr pqxdhOps Γ .nat) (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (bytesDrop w n x).eval env = (x.eval env).drop (n.eval env) := rfl

@[simp] theorem etmBodyE_eval (ct : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (etmBodyE ct).eval env = etmBody (ct.eval env) := rfl

@[simp] theorem etmBody24E_eval (ct : Expr pqxdhOps Δ (B 24)) (env : Env Δ) :
    (etmBody24E ct).eval env = etmBody (ct.eval env) := rfl

@[simp] theorem etmTagE_eval (ct : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (etmTagE ct).eval env = etmTag (ct.eval env) := rfl

@[simp] theorem macInputE_eval (ad : Expr pqxdhOps Δ (B 158)) (ct : Expr pqxdhOps Δ (B 32)) (env : Env Δ) :
    (macInputE ad ct).eval env = aeadMacInput (ad.eval env) (ct.eval env) := rfl

@[simp] theorem queryHmacEval_eval (x : Expr pqxdhOps Δ (B 359)) (env : Env Δ) :
    (queryHmacEval x).eval env = prfHmacEvalQ (x.eval env) := by
  simp [queryHmacEval, Comp.eval, pqPrfHmacIface, pqChalIface, hmacPrfOracle, prfHmacEvalQ]
  rfl

@[simp] theorem liftPrimComp_prfHmac_eval {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (liftPrimComp (C := hmacPrfOracle) c).eval env =
      embedPrim (spec := prfHmacSpec) (c.eval env) :=
  eval_liftPrimComp c env

theorem hmContX0E_eval {S : Setup} (e : Expr pqxdhOps Δ hmSendContTy) (env : Env Δ) (c : HmSendCont S)
    (he : e.eval env = hmSendContToVal c) :
    (hmContX0E e).eval env = c.enc.x0 := by
  change aeadMacInput (e.eval env).2.2.2.2.2.2.2.1
    (etmBody (e.eval env).2.2.2.2.2.2.2.2.1) = c.enc.x0
  rw [he]
  rfl

private def muStToValWith (encodeKey : Nat → muKeyIdTy.denote) (st : PrfHmacMuState) :
    muStTy.denote :=
  (st.keys.map (fun e => (encodeKey e.1, (e.2.1, msgKeysToVal e.2.2))),
    (st.chal.map (fun e => (encodeKey e.1, e.2)), (st.pending, st.bad)))

private def encContToValWith (encodeKey : Nat → muKeyIdTy.denote) (c : HmEncCont) :
    encContTy.denote :=
  (encodeKey c.i, (c.r, (c.ad, (c.ct, muStToValWith encodeKey c.st))))

private def encPreToValWith (encodeKey : Nat → muKeyIdTy.denote) :
    (Option Bytes × PrfHmacMuState) ⊕ HmEncCont → encPreTy.denote
  | .inl (ct?, st) => .inl (ct?, muStToValWith encodeKey st)
  | .inr c => .inr (encContToValWith encodeKey c)

private theorem find_injKey {κ α : Type} (encodeKey : Nat → κ)
    (hInj : Function.Injective encodeKey)
    (eqK : κ → κ → Bool) (heqK : ∀ x y, eqK x y = true ↔ x = y)
    (xs : List (Nat × α)) (i : Nat) :
    (xs.map (fun e => (encodeKey e.1, e.2))).find? (fun e => eqK e.1 (encodeKey i)) =
      (xs.lookup i).map (fun a => (encodeKey i, a)) :=
  find_injKey_map encodeKey hInj eqK heqK id xs i

private theorem hmKeyIdC_eval_gen (encodeKey : Nat → muKeyIdTy.denote)
    (hInj : Function.Injective encodeKey)
    (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) (env : Env Δ) (i : Nat)
    (st : PrfHmacMuState) (ha : a.eval env = (encodeKey i, muStToValWith encodeKey st))
    (hK : st.keys.length ≤ K) :
    (hmKeyIdC K a).eval env =
      (fun r => ((r.1.1, msgKeysToVal r.1.2), muStToValWith encodeKey r.2)) <$> hmKeyP i st := by
  have hT : (st.keys.map (fun e => (encodeKey e.1, (e.2.1, msgKeysToVal e.2.2)))).take K =
      st.keys.map (fun e => (encodeKey e.1, (e.2.1, msgKeysToVal e.2.2))) :=
    List.take_of_length_le (by simpa using hK)
  have hF := find_injKey_map encodeKey hInj muKeyIdEqVal muKeyIdEqVal_iff
    (fun p : ℕ × MessageKeys => (p.1, msgKeysToVal p.2)) st.keys i
  simp only [hmKeyIdC, letV_eval, caseOptV_eval, bindV_eval, eFind, v, muKeys, muChal, muPend,
    muBad, muMk, muKeyIdEq_eval, samplePrim_msgKeys80_eval, Comp.eval, Expr.eval, Ext.step_wk,
    Ext.refl_wk, Env.get_succ, Env.get_zero, ha, muStToValWith, hT, hF, List.length_map]
  unfold hmKeyP
  rcases h : st.keys.lookup i with _ | e
  · simp [map_eq_bind_pure_comp]
  · simp

theorem hmKeyIdC_eval (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) (env : Env Δ) (i : Nat)
    (st : PrfHmacMuState) (ha : a.eval env = (natToMuKeyIdVal S i, muStToValS S st))
    (hK : st.keys.length ≤ K) :
    (hmKeyIdC K a).eval env =
      (fun r => ((r.1.1, msgKeysToVal r.1.2), muStToValS S r.2)) <$> hmKeyP i st :=
  hmKeyIdC_eval_gen K (natToMuKeyIdVal S) (natToMuKeyIdVal_inj S) a env i st ha hK

theorem hmKeyC_eval (a : Expr pqxdhOps Δ (.prod .nat muStTy)) (env : Env Δ) (i : Nat)
    (st : PrfHmacMuState) (ha : a.eval env = (i, muStToVal st)) (hK : st.keys.length ≤ K) :
    (hmKeyC K a).eval env =
      (fun r => ((r.1.1, msgKeysToVal r.1.2), muStToVal r.2)) <$> hmKeyP i st := by
  simp only [hmKeyC, letV_eval]
  exact hmKeyIdC_eval_gen K Sum.inr (fun _ _ h => Sum.inr.inj h) _ _ i st
    (by simp [v, Expr.eval, Env.get_zero, ha, muStToVal, muStToValWith]) hK

private theorem encPostC_eval_gen (encodeKey : Nat → muKeyIdTy.denote)
    (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) (env : Env Δ) (c : HmEncCont)
    (t : Bytes) (ha : a.eval env = (encContToValWith encodeKey c, t))
    (hP : c.st.pending.length ≤ K) :
    (encPostC K a).eval env = pure (Prod.map id (muStToValWith encodeKey) (c.post t)) := by
  have hT : c.st.pending.take K = c.st.pending := List.take_of_length_le hP
  simp only [encPostC, letV_eval, v, muKeys, muChal, muPend, muBad, muMk, pendFilterE, pendHitE,
    eAny, natEq_eval, bytesBeq_eval, boolOr_eval, catB_eval, takeKB_eval, bytesTake_eval,
    etmBody24E_eval, macInputE_eval, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha, encContToValWith, muStToValWith, hT,
    foldr_ite_filter, PNat.val_ofNat]
  rfl

theorem encPostIdC_eval (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) (env : Env Δ) (c : HmEncCont)
    (t : Bytes) (ha : a.eval env = (encContToValS S c, t)) (hP : c.st.pending.length ≤ K) :
    (encPostC K a).eval env = pure (Prod.map id (muStToValS S) (c.post t)) :=
  encPostC_eval_gen K (natToMuKeyIdVal S) a env c t ha hP

theorem encPostC_eval (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) (env : Env Δ) (c : HmEncCont)
    (t : Bytes) (ha : a.eval env = (encContToVal c, t)) (hP : c.st.pending.length ≤ K) :
    (encPostC K a).eval env = pure (Prod.map id muStToVal (c.post t)) :=
  encPostC_eval_gen K Sum.inr a env c t ha hP

private theorem hmEncPreIdC_eval_gen (encodeKey : Nat → muKeyIdTy.denote)
    (hInj : Function.Injective encodeKey)
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad pt : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (encodeKey i, (ad, (pt, muStToValWith encodeKey st)))))
    (hB : MuBounded K st) :
    (hmEncPreIdC K a).eval env = encPreToValWith encodeKey <$> hmEncPre jt i ad pt st := by
  have hT : (st.chal.map (fun e => (encodeKey e.1, e.2))).take K =
      st.chal.map (fun e => (encodeKey e.1, e.2)) :=
    List.take_of_length_le (by simpa using hB.chal_le)
  have hF := find_injKey encodeKey hInj muKeyIdEqVal muKeyIdEqVal_iff st.chal i
  simp only [hmEncPreIdC, letV_eval, caseOptV_eval, eFind, v, muChal, muKeyIdEq_eval, Comp.eval,
    Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha, muStToValWith, hT, hF]
  unfold hmEncPre
  rcases h : st.chal.lookup i with _ | e
  · simp only [Option.map_none, bindV_eval]
    rw [hmKeyIdC_eval_gen K encodeKey hInj _ _ i st (by simp [Expr.eval, muStToValWith]) hB.keys_le]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    refine hm_bind_congr_leaves (hmKeyP_frame i st) fun kr hkr => ?_
    rcases kr with ⟨⟨r, mk⟩, st'⟩
    obtain ⟨-, hpend, -, -⟩ := hkr
    simp only [letV_eval, bindV_eval, queryPrim_eval, queryPrim_aeadEnc_eval,
       valToMsgKeys_msgKeysToVal, Comp.eval, Expr.eval, Env.get_succ, Env.get_zero]
    refine bind_congr fun ct => ?_
    by_cases hlt : r < jt
    · simp only [natLt_expr_eval, samplePrim_bytes32_eval, Expr.eval,
        Env.get_succ, Env.get_zero, hlt,
        decide_true, ite_true, bind_assoc, pure_bind, Function.comp]
      refine bind_congr fun t => ?_
      rw [encPostC_eval_gen K encodeKey _ _ ⟨i, r, ad, ct, st'⟩ t rfl ?_]
      · simp [encPreToValWith, HmEncCont.post]
      · have hp : st'.pending = st.pending := hpend
        rw [hp]; exact hB.pending_le
    · by_cases heq : r = jt
      · subst heq
        simp [natLt_expr_eval, natEq_eval, encPreToValWith, encContToValWith, Expr.eval]
      · have hgt : (r == jt) = false := beq_false_of_ne heq
        simp [natLt_expr_eval, natEq_eval, hlt, heq, hgt, encPreToValWith, muStToValWith,
          muKeys, muPend, muBad, Expr.eval]
        rfl
  · simp [encPreToValWith, muStToValWith]

theorem hmEncPreIdC_eval
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad pt : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (natToMuKeyIdVal S i, (ad, (pt, muStToValS S st)))))
    (hB : MuBounded K st) :
    (hmEncPreIdC K a).eval env = encPreToValS S <$> hmEncPre jt i ad pt st := by
  have h := hmEncPreIdC_eval_gen K (natToMuKeyIdVal S) (natToMuKeyIdVal_inj S) a env jt i ad pt st ha hB
  have hEq : encPreToValWith (natToMuKeyIdVal S) = encPreToValS S := by
    funext x; rcases x with ⟨_, _⟩ | _ <;> rfl
  rwa [hEq] at h

theorem hmEncPreC_eval
    (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad pt : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (i, (ad, (pt, muStToVal st))))) (hB : MuBounded K st) :
    (hmEncPreC K a).eval env = encPreToVal <$> hmEncPre jt i ad pt st := by
  simp only [hmEncPreC, letV_eval]
  have hEq : encPreToVal = encPreToValWith Sum.inr := by
    funext x; rcases x with ⟨_, _⟩ | _ <;> rfl
  rw [hEq]
  exact hmEncPreIdC_eval_gen K Sum.inr (fun _ _ h => Sum.inr.inj h) _ _ jt i ad pt st
    (by simp [v, Expr.eval, Env.get_zero, ha, muStToVal, muStToValWith]) hB

@[simp] theorem natLe_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (natLe a b).eval env = decide (a.eval env ≤ b.eval env) := by
  simp only [natLe, Expr.eval, ← decide_not, Nat.not_lt]

set_option hygiene false in
local macro "forge_tail_gen" : tactic =>
  `(tactic| (
    rw [bindV_eval, hmKeyIdC_eval_gen K encodeKey hInj _ _ i st
      (by simp [Expr.eval, muStToValWith]) hB.keys_le]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    refine hm_bind_congr_leaves (hmKeyP_frame i st) fun kr hkr => ?_
    rcases kr with ⟨⟨r, mk⟩, st'⟩
    obtain ⟨hchal, -, -, -⟩ := hkr
    have hchal' : st'.chal = st.chal := hchal
    simp only [letV_eval, bindV_eval, eCaseOpt, eFind, muKeyIdEq_eval, natLe_eval, bytesBeq_eval,
      bytesLen_eval, queryPrim_eval, queryPrim_aeadDec_eval, valToMsgKeys_msgKeysToVal, boolOr_eval,
      isSomeE_eval, Comp.eval, Expr.eval, v, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
      muStToValWith, hchal', hT, hF, hl, macInputE_eval, etmBodyE_eval, etmTagE_eval,
      Option.map_none, Option.map_some]
    rcases mk with ⟨ck, mkk, iv⟩
    by_cases hg : 24 ≤ ct.length <;> by_cases hr : r ≤ jt <;>
      simp [hg, hr, muMk, muKeys, muChal, muPend, muBad, muStToValWith, Expr.eval, isSomeE_eval,
        bindV_eval, queryPrim_eval, queryPrim_aeadDec_eval, hchal'] <;>
      first
        | rfl
        | (split_ifs <;> simp [muStToValWith, hchal'])
        | (congr 1; funext x; rcases x <;> rfl)
        | (split_ifs
           · simp [muStToValWith, hchal']
           · rw [← map_eq_bind_pure_comp, Functor.map_map]
             congr 1; funext x; rcases x <;> rfl)))

private theorem hmForgeIdC_eval_gen (encodeKey : Nat → muKeyIdTy.denote)
    (hInj : Function.Injective encodeKey)
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad ct : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (encodeKey i, (ad, (ct, muStToValWith encodeKey st)))))
    (hB : MuBounded K st) :
    (hmForgeIdC K a).eval env =
      (fun r => muStToValWith encodeKey r.2) <$> hmForgeP jt i ad ct st := by
  have hT : (st.chal.map (fun e => (encodeKey e.1, e.2))).take K =
      st.chal.map (fun e => (encodeKey e.1, e.2)) :=
    List.take_of_length_le (by simpa using hB.chal_le)
  have hF := find_injKey encodeKey hInj muKeyIdEqVal muKeyIdEqVal_iff st.chal i
  simp only [hmForgeIdC, letV_eval, eCaseOpt, eFind, v, muChal, muKeyIdEq_eval, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, ha,
    muStToValWith, hT, hF]
  unfold hmForgeP
  rcases hl : st.chal.lookup i with _ | ⟨a0, c0⟩
  · simp only [Option.map_none, Bool.false_eq_true, ite_false, reduceCtorEq, beq_iff_eq]
    forge_tail_gen
  · simp only [Option.map_some, Option.some.injEq, beq_iff_eq]
    by_cases hm : a0 = ad ∧ c0 = ct
    · obtain ⟨rfl, rfl⟩ := hm
      simp
    · have hm' : ¬ ((a0, c0) = (ad, ct)) := by simpa using hm
      have hb : (a0 == ad && c0 == ct) = false := by
        by_cases h1 : a0 = ad <;> simp_all
      simp only [hb, hm', Bool.false_eq_true, ite_false]
      forge_tail_gen

theorem hmForgeIdC_eval
    (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad ct : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (natToMuKeyIdVal S i, (ad, (ct, muStToValS S st)))))
    (hB : MuBounded K st) :
    (hmForgeIdC K a).eval env = (fun r => muStToValS S r.2) <$> hmForgeP jt i ad ct st :=
  hmForgeIdC_eval_gen K (natToMuKeyIdVal S) (natToMuKeyIdVal_inj S) a env jt i ad ct st ha hB

theorem hmForgeC_eval
    (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))))
    (env : Env Δ) (jt i : Nat) (ad ct : Bytes) (st : PrfHmacMuState)
    (ha : a.eval env = (jt, (i, (ad, (ct, muStToVal st))))) (hB : MuBounded K st) :
    (hmForgeC K a).eval env = (fun r => muStToVal r.2) <$> hmForgeP jt i ad ct st := by
  simp only [hmForgeC, letV_eval]
  exact hmForgeIdC_eval_gen K Sum.inr (fun _ _ h => Sum.inr.inj h) _ _ jt i ad ct st
    (by simp [v, Expr.eval, Env.get_zero, ha, muStToVal, muStToValWith]) hB

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
