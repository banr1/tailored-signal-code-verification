/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore
import VCVio.EvalDist.Monad.Basic

/-!
# Simulation Lemmas for `KeyIndCore`

Connects evaluation of the `ReductionDsl` branches in `KeyIndCore` to the reference `OracleComp`
handler `pqxdhKeyIndImplPrim` when all game-state lists lie within the loop bound `K`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

@[simp] theorem Ext.step_wk' {Γ Δ : List PT} {σ τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ)).wk x = .succ (h.wk x) := rfl
@[simp] theorem Ext.refl_wk' {Γ : List PT} {τ : PT} (x : Var Γ τ) :
    (Ext.refl).wk x = x := rfl

@[simp] theorem Env.get_zero' {Γ : List PT} {τ : PT} (x : τ.denote) (env : Env Γ) :
    (Env.cons x env).get Var.zero = x := rfl
@[simp] theorem Env.get_succ' {Γ : List PT} {τ σ : PT} (i : Var Γ τ) (x : σ.denote) (env : Env Γ) :
    (Env.cons x env).get (Var.succ i) = env.get i := rfl

@[simp] theorem litB_eval (w : ℕ+) (bs : Bytes) {Γ : List PT} (env : Env Γ) :
    (litB w bs).eval env = bs := rfl
@[simp] theorem catB_eval {m n : ℕ+} {Γ : List PT} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n))
    (env : Env Γ) : (catB a b).eval env = a.eval env ++ b.eval env := rfl
@[simp] theorem consB_eval {w : ℕ+} {Γ : List PT} (b : UInt8) (a : Expr pqxdhOps Γ (B w))
    (env : Env Γ) : (consB b a).eval env = b :: a.eval env := rfl
@[simp] theorem widenB_eval (w d : ℕ+) {Γ : List PT} (a : Expr pqxdhOps Γ (B w))
    (env : Env Γ) : (widenB w d a).eval env = a.eval env := rfl
@[simp] theorem takeKB_eval (w k : ℕ+) {Γ : List PT} (a : Expr pqxdhOps Γ (B w))
    (env : Env Γ) : (takeKB w k a).eval env = (a.eval env).take k := rfl
@[simp] theorem dropB_eval {w : ℕ+} {Γ : List PT} (n : Expr pqxdhOps Γ .nat) (a : Expr pqxdhOps Γ (B w))
    (env : Env Γ) : (dropB n a).eval env = (a.eval env).drop (n.eval env) := rfl
@[simp] theorem lenB_eval {w : ℕ+} {Γ : List PT} (a : Expr pqxdhOps Γ (B w))
    (env : Env Γ) : (lenB a).eval env = (a.eval env).length := rfl
@[simp] theorem eqB_eval {m n : ℕ+} {Γ : List PT} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n))
    (env : Env Γ) : (eqB a b).eval env = (a.eval env == b.eval env) := rfl
@[simp] theorem u32OfNat_eval {Γ : List PT} (n : Expr pqxdhOps Γ .nat)
    (env : Env Γ) : (u32OfNat n).eval env = UInt32.ofNat (n.eval env) := rfl
@[simp] theorem eqU32_eval {Γ : List PT} (a b : Expr pqxdhOps Γ U32)
    (env : Env Γ) : (eqU32 a b).eval env = (a.eval env == b.eval env) := rfl

@[simp] theorem letV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ₁ τ₂ : PT} (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by
  simp [letV, Comp.eval]

@[simp] theorem orE_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) (env : Env Γ) :
    (orE a b).eval env = (a.eval env || b.eval env) := by
  simp only [orE, Expr.eval]; cases a.eval env <;> rfl

@[simp] theorem mulRight_eval {Γ : List PT} (a : Expr pqxdhOps Γ .nat) (k : ℕ) (env : Env Γ) :
    (mulRight a k).eval env = a.eval env * k := by
  simp only [mulRight, Expr.eval, Nat.mul_comm]

@[simp] theorem natEq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (natEq a b).eval env = (a.eval env == b.eval env) := by
  simp only [natEq, Expr.eval]; cases h : a.eval env == b.eval env <;> simp_all

@[simp] theorem sBool_eval {Γ : List PT} (env : Env Γ) :
    (sBool).eval env = SignalPqxdh.Security.embedUnif ($ᵗ Bool) := rfl

@[simp] theorem sBytes32_eval {Γ : List PT} (env : Env Γ) :
    (sBytes32).eval env = SignalPqxdh.Security.embedUnif sampleBytes32 := rfl

@[simp] theorem sRandom64_eval {Γ : List PT} (env : Env Γ) :
    (sRandom64).eval env = SignalPqxdh.Security.embedUnif sampleRandom64 := rfl

@[simp] theorem sDrKey96_eval {Γ : List PT} (env : Env Γ) :
    (sDrKey96).eval env = drKeyToVal <$> SignalPqxdh.Security.embedUnif sampleDRKey96 := by
  simp only [sDrKey96, Comp.eval, Iface.liftP, pqPrimIface, pqSamplers, PSamp.run, simulateQ_map]
  rfl

@[simp] theorem sIndex_eval (N : ℕ) {Γ : List PT} (env : Env Γ) :
    (sIndex N).eval env = SignalPqxdh.Security.embedUnif (sampleIndexRange N) := rfl

@[simp] theorem qX25519_eval {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) (env : Env Γ) :
    (qX25519 e).eval env = primQ (.x25519 (e.eval env).1 (e.eval env).2) := by
  simp [qX25519, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qX25519Base_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (qX25519Base e).eval env = primQ (.x25519Base (e.eval env)) := by
  simp [qX25519Base, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qIsCanonical_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (qIsCanonical e).eval env = primQ (.isCanonical (e.eval env)) := by
  simp [qIsCanonical, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qPow8_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (qPow8 e).eval env = primQ (.pow8 (e.eval env)) := by
  simp [qPow8, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qSigPkGen_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (qSigPkGen e).eval env = primQ (.sigPkGen (e.eval env)) := by
  simp [qSigPkGen, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qSigSign_eval (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) (env : Env Γ) :
    (qSigSign m e).eval env =
      primQ (.sigSign (e.eval env).1 (e.eval env).2.1 (e.eval env).2.2) := by
  simp [qSigSign, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qSigVerify_eval (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) (env : Env Γ) :
    (qSigVerify m e).eval env =
      primQ (.sigVerify (e.eval env).1 (e.eval env).2.1 (e.eval env).2.2) := by
  simp [qSigVerify, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qKemKeyGen_eval {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) (env : Env Γ) :
    (qKemKeyGen e).eval env = primQ (.kemKeyGen (e.eval env)) := by
  simp [qKemKeyGen, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qKemEncaps_eval {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) (env : Env Γ) :
    (qKemEncaps e).eval env = primQ (.kemEncaps (e.eval env).1 (e.eval env).2) := by
  simp [qKemEncaps, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qKemDecaps_eval {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) (env : Env Γ) :
    (qKemDecaps e).eval env = primQ (.kemDecaps (e.eval env).1 (e.eval env).2) := by
  simp [qKemDecaps, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem qHkdfDerive96_eval (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (qHkdfDerive96 w e).eval env = drKeyToVal <$> primQ (.hkdfDerive96 (e.eval env)) := by
  simp [qHkdfDerive96, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec, primQ]

@[simp] theorem findML_prim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (L : List α) :
    findML p L = findMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [findML, findMPrim, ih]

@[simp] theorem anyML_prim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) (L : List α) :
    anyML p L = anyMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [anyML, anyMPrim, ih]

theorem findML_map {ι : Type} {T : OracleSpec ι} {α β : Type} (f : α → β)
    (p : β → OracleComp T Bool) (L : List α) :
    findML p (L.map f) = (Option.map f) <$> findML (fun x => p (f x)) L := by
  induction L with
  | nil => simp [findML]
  | cons x xs ih =>
    simp only [List.map_cons, findML, ih, map_eq_bind_pure_comp, bind_assoc]
    congr 1; funext b; cases b <;> simp

theorem anyML_map {ι : Type} {T : OracleSpec ι} {α β : Type} (f : α → β)
    (p : β → OracleComp T Bool) (L : List α) :
    anyML p (L.map f) = anyML (fun x => p (f x)) L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, anyML, ih]

theorem findMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    findMPrim p (L.map f) = (Option.map f) <$> findMPrim (fun x => p (f x)) L := by
  simp only [← findML_prim, findML_map]

theorem anyMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    anyMPrim p (L.map f) = anyMPrim (fun x => p (f x)) L := by
  simp only [← anyML_prim, anyML_map]

def sidEqV : sessionIdTy.denote → sessionIdTy.denote → Bool
  | .inl a, .inl b => a.1 == b.1 && a.2 == b.2
  | .inr (.inl a), .inr (.inl b) => a.1 == b.1 && a.2 == b.2
  | .inr (.inr (.inl a)), .inr (.inr (.inl b)) => a.1 == b.1 && (a.2.1 == b.2.1 && a.2.2 == b.2.2)
  | .inr (.inr (.inr a)), .inr (.inr (.inr b)) => a.1 == b.1 && (a.2.1 == b.2.1 && a.2.2 == b.2.2)
  | _, _ => false

@[simp] theorem sidEq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ) :
    (sidEq a b).eval env = sidEqV (a.eval env) (b.eval env) := by
  simp only [sidEq, eLet2, eLet, eCaseSum, v, nat2Eq, nat3Eq, natEq_eval, Expr.eval, Env.get,
    Ext.step_wk', Ext.refl_wk']
  generalize a.eval env = x; generalize b.eval env = y
  rcases x with x | x | x | x <;> rcases y with y | y | y | y <;> rfl

@[simp] theorem sidEqV_enc {S : Setup} (x y : SessionId S) :
    sidEqV (sessionIdToVal x) (sessionIdToVal y) = (x == y) := by
  cases x <;> cases y <;> (rw [Bool.eq_iff_iff]; simp [sidEqV, sessionIdToVal, sidV, Fin.ext_iff])

@[simp] theorem encEC_eval {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (encEC pk).eval env = encodeEC (pk.eval env) := rfl

@[simp] theorem encKEM_eval {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) (env : Env Γ) :
    (encKEM pk).eval env = encodeKEM (pk.eval env) := rfl

@[simp] theorem buildSecretsE_eval {Γ : List PT} (d1 d2 d3 ss : Expr pqxdhOps Γ (B 32))
    (d4 : Expr pqxdhOps Γ (.opt (B 32))) (env : Env Γ) :
    (buildSecretsE d1 d2 d3 d4 ss).eval env =
      buildSecrets (d1.eval env) (d2.eval env) (d3.eval env) (d4.eval env) (ss.eval env) := by
  simp only [buildSecretsE, buildSecrets, eLet2, eLet, eCaseOpt, v,
    Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
  cases d4.eval env <;> rfl

syntax "core_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| core_simp [$xs,*]) =>
    `(tactic| simp only [Comp.eval, Expr.eval,
      litB_eval, catB_eval, consB_eval, widenB_eval, takeKB_eval,
      dropB_eval, lenB_eval, eqB_eval, 
      u32OfNat_eval, eqU32_eval,
      Env.get, Ext.step_wk',
      Ext.refl_wk', keyIndStateToVal, natEq_eval, orE_eval, mulRight_eval, letV_eval,
      sBool_eval, sBytes32_eval, sRandom64_eval, sDrKey96_eval, sIndex_eval,
      qX25519_eval, qX25519Base_eval, qIsCanonical_eval, qPow8_eval, qSigPkGen_eval,
      qSigSign_eval, qSigVerify_eval, qKemKeyGen_eval, qKemEncaps_eval, qKemDecaps_eval,
      qHkdfDerive96_eval, findML_prim, anyML_prim,
      ↓reduceIte, ite_true, ite_false, List.any_map, List.find?_map, List.map_map,
      Function.comp_def, Env.get_zero', Env.get_succ', List.length_map,
      keyIndSessionEntryToVal, keyIndRespEntryToVal, sidEq_eval, sidEqV_enc,
      v, bindV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
      eLet, eLet2, eCaseOpt, eCaseSum, eFind, eAny, eMap,
      nat2Eq, nat3Eq, optBytesEq, optU32Eq, kyberEq, nonZero32,
      buildSecretsE_eval, encEC_eval, encKEM_eval,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      stMk, stUpd, peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
      oeOpkSk, oeOpkPk, oeConsumed, oeMk, oeUpd,
      seSid, seHonestPeer, sePeerIk, sePeerSpk, sePeerOpk, sePeerPqspk,
      seSpkHon, seOpkHon, sePqspkHon, seEkASk, seFresh, seDrReal, seDrRand,
      seHdr, seTested, seRevealed, seMk, seUpd,
      reSid, reRespIk, reSpk, reOpk, rePqspk, reHdr, reSenderHonest,
      reDrReal, reDrRand, reTested, reRevealed, reMk, reUpd,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
      rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rDh, rSpkSk,
      isSomeE, getDBytes, optFst, optSnd, dhOptNZ, guardE, rs, kyberCheckE, freshE, emptyStE,
      aiIkSk, aiSpkSk, aiOpkSk, aiPqSk, aiReplay, aiHdr, qK, qJ, qO, qHdr, qKJO, initSidE, $xs,*])

structure KeyIndListsBounded {S : Setup} (st : KeyIndState S) (n : Nat) : Prop where
  principals_le       : st.principals.length ≤ n
  spkBundles_le       : st.spkBundles.length ≤ n
  opkEntries_le       : st.opkEntries.length ≤ n
  sessions_le         : st.sessions.length ≤ n
  respSessions_le     : st.respSessions.length ≤ n
  usedRecvOPK_le      : st.usedRecvOPK.length ≤ n
  usedRecvNoOPK_le    : st.usedRecvNoOPK.length ≤ n
  usedKyberTriples_le : st.seenKyberBaseKeys.length ≤ n
  roCache_le          : st.roCache.length ≤ n
  advKeys_le          : st.advKeys.length ≤ n

theorem nat3_beq (x : ℕ × ℕ × ℕ) (a b c : ℕ) :
    (x == (a, b, c)) = (x.1 == a && (x.2.1 == b && x.2.2 == c)) := by
  rcases x with ⟨p, q, r⟩; rfl

theorem nat2_beq (x : ℕ × ℕ) (a b : ℕ) :
    (x == (a, b)) = (x.1 == a && x.2 == b) := by
  rcases x with ⟨p, q⟩; rfl

def encRS {S : Setup} (p : KeyIndResponse × KeyIndState S) : RS.denote :=
  (keyIndRespToVal p.1, keyIndStateToVal p.2)

def decPrin (l : List (Nat × principalEntryTy.denote)) : List (Nat × PrincipalEntry) :=
  l.map (Prod.map id valToPrincipalEntry)
def decSpks (l : List ((Nat × Nat) × spkBundleEntryTy.denote)) :
    List ((Nat × Nat) × SpkBundleEntry) := l.map (Prod.map id valToSpkBundleEntry)
def decOpks (l : List ((Nat × Nat × Nat) × opkEntryTy.denote)) :
    List ((Nat × Nat × Nat) × OpkEntry) := l.map (Prod.map id valToOpkEntry)

@[simp] theorem decPrin_enc (l : List (Nat × PrincipalEntry)) :
    decPrin (l.map (Prod.map id principalEntryToVal)) = l := by
  simp [decPrin, List.map_map]; exact List.map_id'' (fun _ => rfl) l
@[simp] theorem decSpks_enc (l : List ((Nat × Nat) × SpkBundleEntry)) :
    decSpks (l.map (Prod.map id spkBundleEntryToVal)) = l := by
  simp [decSpks, List.map_map]; exact List.map_id'' (fun _ => rfl) l
@[simp] theorem decOpks_enc (l : List ((Nat × Nat × Nat) × OpkEntry)) :
    decOpks (l.map (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal)) = l := by
  simp [decOpks, List.map_map]; exact List.map_id'' (fun _ => rfl) l

theorem ite_unit_bind {α : Type} (c : Prop) [Decidable c] (f : Unit → Option α) :
    (if c then some () else none).bind f = if c then f () else none := by split <;> rfl
theorem ite_none_unit_bind {α : Type} (c : Prop) [Decidable c] (f : Unit → Option α) :
    (if c then none else some ()).bind f = if c then none else f () := by split <;> rfl

@[simp] theorem decOpks_enc' (l : List ((Nat × Nat × Nat) × OpkEntry)) :
    decOpks (l.map (Prod.map (fun x => (x.1, x.2.1, x.2.2)) opkEntryToVal)) = l := by
  simp [decOpks, List.map_map]; exact List.map_id'' (fun _ => rfl) l

@[simp] theorem findMPrim_take_map {α β : Type} (f : α → β) (p : β → OracleComp PrimBaseSpec Bool)
    (n : Nat) (L : List α) :
    findMPrim p ((L.map f).take n) = Option.map f <$> findMPrim (fun x => p (f x)) (L.take n) := by
  rw [← List.map_take, findMPrim_map]

section Helpers
variable (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy) (env : Env Δ)

theorem take_minK {α : Type} (K N : Nat) (l : List α) :
    l.take (min K N) = (l.take K).take N := by
  rw [List.take_take, Nat.min_comm]

theorem bind_congr2 {m : Type → Type} [Monad m] {α β : Type} {a b : m α} {f g : α → m β}
    (h : a = b) (h' : ∀ x, f x = g x) : a >>= f = b >>= g := by
  subst h; exact congrArg _ (funext h')

@[simp] theorem findHonestC_eval (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).eval env =
      Option.map (Prod.map id principalEntryToVal) <$>
        findHonestPrincipalPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K) (ik.eval env) := by
  unfold findHonestC findHonestPrincipalPrim
  core_simp []
  generalize (env.get (Ext.wk st)).2.1 = l
  have hl : l = (decPrin l).map (Prod.map id principalEntryToVal) := by
    simp only [decPrin, List.map_map]; exact (List.map_id'' (fun _ => rfl) l).symm
  conv_lhs => rw [hl]
  rw [take_minK, ← List.map_take, ← List.map_take, findMPrim_map]
  rfl

theorem decSpks_rt (l : (Ty.list (.prod (.prod .nat .nat) spkBundleEntryTy)).denote) :
    l = (decSpks l).map (Prod.map id spkBundleEntryToVal) := by
  simp only [decSpks, List.map_map]; exact (List.map_id'' (fun _ => rfl) l).symm
theorem decOpks_rt (l : (Ty.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)).denote) :
    l = (decOpks l).map (Prod.map id opkEntryToVal) := by
  simp only [decOpks, List.map_map]; exact (List.map_id'' (fun _ => rfl) l).symm

@[simp] theorem isAdvRegC_eval (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).eval env =
      isAdvRegisteredPrim ((env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.2.take K) (pk.eval env) := by
  unfold isAdvRegC isAdvRegisteredPrim
  core_simp []

@[simp] theorem isGameSpkC_eval (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).eval env =
      isGameSpkPrim S ((decSpks (env.get (Ext.wk st)).2.2.1).take K) (pk.eval env) := by
  unfold isGameSpkC isGameSpkPrim
  core_simp []
  generalize (env.get (Ext.wk st)).2.2.1 = l
  conv_lhs => rw [decSpks_rt l]
  rw [take_minK, ← List.map_take, ← List.map_take, anyMPrim_map]
  rfl

@[simp] theorem isGameOpkC_eval (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).eval env =
      isGameOpkPrim S ((decOpks (env.get (Ext.wk st)).2.2.2.1).take K) (pk.eval env) := by
  unfold isGameOpkC isGameOpkPrim
  core_simp []
  generalize (env.get (Ext.wk st)).2.2.2.1 = l
  conv_lhs => rw [decOpks_rt l]
  rw [take_minK, ← List.map_take, ← List.map_take, anyMPrim_map]
  rfl

@[simp] theorem resolveSigPkC_eval (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).eval env =
      resolveSigPkPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K) (ik.eval env) := by
  unfold resolveSigPkC resolveSigPkPrim
  simp only [letV_eval, bindV, Comp.eval, findHonestC_eval]
  core_simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1; funext o; cases o <;> rfl

@[simp] theorem honestPeerC_eval (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).eval env =
      isHonestUncorruptedPeerPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K) (ik.eval env) := by
  unfold honestPeerC isHonestUncorruptedPeerPrim
  simp only [bindV, Comp.eval, findHonestC_eval]
  core_simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1; funext o; rcases o with _ | ⟨k, e⟩
  · rfl
  · cases e.corrupted <;> rfl

@[simp] theorem koskSenderOkC_eval (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).eval env =
      koskSenderOkPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K)
        ((env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.2.take K) (ik.eval env) := by
  unfold koskSenderOkC koskSenderOkPrim isGameIdKeyPrim
  simp only [letV_eval, bindV, Comp.eval, findHonestC_eval, isAdvRegC_eval]
  core_simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1; funext o; congr 1; funext b; cases o <;> rfl

@[simp] theorem koskBundleOkC_eval {Γ₂ : List PT} [Ext Γ₂ Δ] (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkC S K st bu).eval env =
      koskBundleOkPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K)
        ((decSpks (env.get (Ext.wk st)).2.2.1).take K)
        ((decOpks (env.get (Ext.wk st)).2.2.2.1).take K)
        ((env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.2.take K)
        (valToPreKeyBundle (env.get (Ext.wk bu))) := by
  unfold koskBundleOkC koskBundleOkPrim isGameIdKeyPrim
  simp only [bindV, caseOptV, Comp.eval, findHonestC_eval, isAdvRegC_eval, isGameSpkC_eval,
    isGameOpkC_eval]
  core_simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [valToPreKeyBundle, bundleOfV]
  congr 1; funext x; congr 1; funext a; congr 1; funext b; congr 1; funext c
  rcases (env.get (Ext.wk bu)).2.2.2.2.1 with _ | ⟨f, pk⟩
  · cases x <;> rfl
  · cases x <;> rfl

def decRo (l : List (Bytes × drKeyTy.denote)) : List (Bytes × DRKey) :=
  l.map (Prod.map id valToDrKey)
@[simp] theorem decRo_enc (l : List (Bytes × DRKey)) :
    decRo (l.map (Prod.map id drKeyToVal)) = l := by
  simp [decRo, List.map_map]; exact List.map_id'' (fun _ => rfl) l
theorem decRo_rt (l : (Ty.list (.prod (B 192) drKeyTy)).denote) :
    l = (decRo l).map (Prod.map id drKeyToVal) := by
  simp only [decRo, drKeyToVal, valToDrKey, List.map_map]
  exact (List.map_id'' (fun _ => rfl) l).symm

def evalHkdfOrRoK (K : Nat) (useRo : Bool) (roCache : List (Bytes × DRKey)) (secrets : Bytes) :
    OracleComp PrimBaseSpec (DRKey × List (Bytes × DRKey)) := do
  if !useRo then
    let dk ← primQ (.hkdfDerive96 secrets)
    return (dk, roCache)
  else
    match (roCache.take K).find? (fun (inp, _) => inp == secrets) with
    | some (_, dk) => return (dk, roCache)
    | none =>
      let dk ← embedUnif sampleDRKey96
      return (dk, (secrets, dk) :: roCache)

@[simp] theorem evalHkdfOrRoK_eq (K : Nat) (useRo : Bool) (roCache : List (Bytes × DRKey))
    (secrets : Bytes) (h : roCache.length ≤ K) :
    evalHkdfOrRoK K useRo roCache secrets = evalHkdfOrRoPrim useRo roCache secrets := by
  unfold evalHkdfOrRoK evalHkdfOrRoPrim
  rw [List.take_of_length_le h]
  cases useRo
  · rfl
  · rcases hf : roCache.find? (fun x => x.1 == secrets) with _ | ⟨a, b⟩ <;> simp [hf]

@[simp] theorem hkdfOrRoC_eval (useRo : Bool) (sec : Expr pqxdhOps Δ (B 192)) :
    (hkdfOrRoC K useRo st sec).eval env =
      (fun p => (drKeyToVal p.1, p.2.map (Prod.map id drKeyToVal))) <$>
        evalHkdfOrRoK K useRo (decRo (env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.1) (sec.eval env) := by
  unfold hkdfOrRoC evalHkdfOrRoK
  cases useRo
  · core_simp [Bool.false_eq_true]
    generalize (env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.1 = l
    conv_lhs => rw [decRo_rt l]
    simp
  · core_simp []
    generalize (env.get (Ext.wk st)).2.2.2.2.2.2.2.2.2.1 = l
    conv_lhs => rw [decRo_rt l]
    simp only [← List.map_take, List.find?_map, Function.comp_def]
    rcases hf : (List.take K (decRo l)).find? (fun x => x.1 == sec.eval env) with _ | ⟨a, b⟩
    · simp [hf]
    · simp [hf]

def acceptKeysV (ikSk spkSk : Bytes) (opkSk : Option Bytes) (pqSk : Bytes) (replay : Bool)
    (hdr : HandshakeHdr) : OracleComp PrimBaseSpec (Option DRKey) :=
  acceptKeysPrim ⟨ikSk, [], spkSk, [], opkSk, pqSk, [], true, replay, hdr⟩

@[simp] theorem acceptKeysPrim_eq (a b c d : Bytes) (e : Option Bytes) (f g : Bytes) (r : Bool)
    (h : HandshakeHdr) :
    acceptKeysPrim ⟨a, b, c, d, e, f, g, true, r, h⟩ = acceptKeysV a c e f r h := rfl

private theorem opt_map_ite {α β : Type} (f : α → β) (c : Prop) [Decidable c]
    (a b : Option α) :
    Option.map f (if c then a else b) = if c then Option.map f a else Option.map f b := by
  split_ifs <;> rfl

omit [Ext Γ Δ] in
set_option maxHeartbeats 1000000 in
@[simp] theorem acceptKeysC_eval (inp : Expr pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).eval env =
      Option.map drKeyToVal <$> acceptKeysV (inp.eval env).1 (inp.eval env).2.1
        (inp.eval env).2.2.1 (inp.eval env).2.2.2.1 (inp.eval env).2.2.2.2.1
        (valToHandshakeHdr (inp.eval env).2.2.2.2.2) := by
  unfold acceptKeysC acceptKeysV acceptKeysPrim
  core_simp [buildSecretsE_eval]
  generalize inp.eval env = i
  rcases i with ⟨a, b, o, p, r, h1, h2, h3, h4, h5, h6⟩
  simp only [valToHandshakeHdr, hdrOfV, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  cases o <;> cases h4 <;>
  · simp only [Option.getD_none, Option.getD_some]
    refine bind_congr fun canon => ?_; refine bind_congr fun d1 => ?_
    refine bind_congr fun d2 => ?_; refine bind_congr fun d3 => ?_
    refine bind_congr fun d4 => ?_; refine bind_congr fun ss => ?_
    cases ss <;> cases r <;> cases canon <;>
      simp [buildSecrets, _root_.guard, dhOptNonZero, ite_unit_bind, ite_none_unit_bind, opt_map_ite] <;>
      rfl

def checkProvK (S : Setup) (K : Nat) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec (Bool × Bool × Bool) := do
  match ← findHonestPrincipalPrim S (principals.take K) bundle.ikB with
  | none => return (false, false, false)
  | some (k, _) =>
    let spkHon ← anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && p1 == p2)) ((spkBundles.take K).take S.N_dh)
    let pqspkHon := (spkBundles.take K).any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon ← match bundle.opkB? with
      | none => pure false
      | some (_, opkPk) =>
        anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) ((opkEntries.take K).take S.N_dh)
    return (spkHon, opkHon, pqspkHon)

@[simp] theorem checkProvK_eq (K : Nat) (pr : List (Nat × PrincipalEntry))
    (sp : List ((Nat × Nat) × SpkBundleEntry)) (op : List ((Nat × Nat × Nat) × OpkEntry))
    (b : PreKeyBundleInput) (hp : pr.length ≤ K) (h : sp.length ≤ K) (ho : op.length ≤ K) :
    checkProvK S K pr sp op b = checkBundleProvenancePrim S pr sp op b := by
  unfold checkProvK checkBundleProvenancePrim
  rw [List.take_of_length_le hp, List.take_of_length_le h, List.take_of_length_le ho]
  rfl

@[simp] theorem checkProvC_eval {Γ₂ : List PT} [Ext Γ₂ Δ] (bu : Var Γ₂ preKeyBundleTy) :
    (checkProvC S K st bu).eval env =
      checkProvK S K (decPrin (env.get (Ext.wk st)).2.1) (decSpks (env.get (Ext.wk st)).2.2.1)
        (decOpks (env.get (Ext.wk st)).2.2.2.1) (valToPreKeyBundle (env.get (Ext.wk bu))) := by
  unfold checkProvC checkProvK
  simp only [bindV, caseOptV, letV_eval, Comp.eval, findHonestC_eval]
  core_simp [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp only [valToPreKeyBundle, bundleOfV]
  refine bind_congr fun f => ?_
  generalize (env.get (Ext.wk st)).2.2.1 = ls
  generalize (env.get (Ext.wk st)).2.2.2.1 = lo
  conv_lhs => rw [decSpks_rt ls, decOpks_rt lo]
  simp only [take_minK, ← List.map_take, anyMPrim_map, List.any_map, Function.comp_def]
  rcases f with _ | ⟨k, e⟩
  · rfl
  · simp only [Option.map_some, Prod.map, id]
    refine bind_congr fun a => ?_
    rcases (env.get (Ext.wk bu)).2.2.2.2.1 with _ | ⟨f, pk⟩
    · simp
    · rfl

end Helpers

section
variable (useRo : Bool) (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
  (st : Var Γ₁ keyIndStateTy) (env : Env Δ) (s : KeyIndState S)
  (hs : env.get (Ext.wk st) = keyIndStateToVal s) (hB : KeyIndListsBounded s K)
include hs hB

theorem initPrinB_eval (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (initPrinB K st uV).eval env = encRS <$> (pqxdhKeyIndImplPrim useRo S (.initPrin u)).run s := by
  unfold initPrinB
  core_simp [hs, hu, List.take_of_length_le, hB.principals_le]
  simp only [pqxdhKeyIndImplPrim]
  by_cases h : (s.principals.any fun x => x.1 == ↑u) = true
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]
  · simp [h, encRS, keyIndRespToVal, keyIndRenc, liftM, sampleScalar32]

theorem genOpkB_eval (xV : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hx : env.get (Ext.wk xV) = (u.val, (j.val, o.val))) :
    (genOpkB K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.genOPK u j o)).run s := by
  unfold genOpkB
  core_simp [hs, hx, List.take_of_length_le, hB.opkEntries_le]
  simp only [pqxdhKeyIndImplPrim, nat3_beq]
  by_cases h : (s.opkEntries.any fun x => x.1.1 == ↑u && (x.1.2.1 == ↑j && x.1.2.2 == ↑o)) = true
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]
  · simp [h, encRS, keyIndRespToVal, keyIndRenc, liftM, sampleScalar32]

theorem corruptB_eval (uV : Var Γ₂ .nat) (u : Fin S.N_id) (hu : env.get (Ext.wk uV) = u.val) :
    (corruptB K st uV).eval env = encRS <$> (pqxdhKeyIndImplPrim useRo S (.corruptIK u)).run s := by
  unfold corruptB
  core_simp [hs, hu, List.take_of_length_le, hB.principals_le]
  simp only [pqxdhKeyIndImplPrim]
  rcases hf : s.principals.find? (fun x => x.1 == ↑u) with _ | ⟨i, e⟩
  · simp [hf, encRS, keyIndRespToVal, keyIndRenc]
  · simp [Function.comp_def, hf, encRS, keyIndRespToVal, keyIndRenc, List.map_map]
    intro a b _; split_ifs <;> rfl

omit hB in
theorem registerB_eval (skV : Var Γ₂ (B 32)) (sk : Bytes) (hsk : env.get (Ext.wk skV) = sk) :
    (registerB st skV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.registerKey sk)).run s := by
  unfold registerB
  core_simp [hs, hsk]
  erw [hsk]
  simp only [pqxdhKeyIndImplPrim]
  by_cases h : sk.length = 32
  · simp [h, encRS, keyIndRespToVal, keyIndRenc, liftM]
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]

theorem genSpkB_eval (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (genSpkB K st xV).eval env = encRS <$> (pqxdhKeyIndImplPrim useRo S (.genSPK u j)).run s := by
  unfold genSpkB
  core_simp [hs, hx, List.take_of_length_le, hB.principals_le, hB.spkBundles_le]
  simp only [pqxdhKeyIndImplPrim, nat2_beq]
  by_cases h : (s.spkBundles.any fun x => x.1.1 == ↑u && x.1.2 == ↑j) = true
  · simp [h, encRS, keyIndRespToVal, keyIndRenc]
  · rcases hf : s.principals.find? (fun x => x.1 == ↑u) with _ | ⟨i, e⟩
    · simp [h, hf, encRS, keyIndRespToVal, keyIndRenc]
    · simp [h, hf, encRS, keyIndRespToVal, keyIndRenc, bundleV, liftM, sampleScalar32,
        sampleKemKeyGenPrim, encodeEC, encodeKEM]

theorem revealSpkB_eval (xV : Var Γ₂ (.prod .nat .nat)) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hx : env.get (Ext.wk xV) = (u.val, j.val)) :
    (revealSpkB K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.revealSpkSk u j)).run s := by
  unfold revealSpkB
  core_simp [hs, hx, List.take_of_length_le, hB.spkBundles_le]
  simp only [pqxdhKeyIndImplPrim, nat2_beq]
  rcases hf : s.spkBundles.find? (fun x => x.1.1 == ↑u && x.1.2 == ↑j) with _ | ⟨i, e⟩
  · simp [hf, encRS, keyIndRespToVal, keyIndRenc]
  · simp [hf, encRS, keyIndRespToVal, keyIndRenc]
    intro a b c _; split_ifs <;> rfl

theorem roB_eval (secV : Var Γ₂ (B 192)) (sec : Bytes) (hsec : env.get (Ext.wk secV) = sec) :
    (roB useRo K st secV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.roQuery sec)).run s := by
  unfold roB
  cases useRo
  · simp [Comp.eval, Expr.eval, rs, rNone, v, hs, pqxdhKeyIndImplPrim, encRS,
      keyIndRespToVal, keyIndRenc]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    unfold hkdfOrRoC
    core_simp [hs, hsec, List.take_of_length_le, hB.roCache_le]
    simp only [pqxdhKeyIndImplPrim, evalHkdfOrRoPrim]
    rcases hf : s.roCache.find? (fun x => x.1 == sec) with _ | ⟨i, e⟩
    · simp [hf, encRS, keyIndRespToVal, keyIndRenc, drKeyV]
    · simp [hf, encRS, keyIndRespToVal, keyIndRenc, drKeyV]

theorem revealDhB_eval :
    (revealDhB useRo K st).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S .revealDhSecrets).run s := by
  unfold revealDhB
  cases useRo
  · simp only [Bool.false_eq_true, ↓reduceIte]
    core_simp [hs, List.take_of_length_le, hB.principals_le, hB.spkBundles_le, hB.opkEntries_le,
      hB.sessions_le]
    simp [pqxdhKeyIndImplPrim, encRS, keyIndRespToVal, keyIndRenc]
  · simp [Comp.eval, Expr.eval, rs, rNone, v, hs, pqxdhKeyIndImplPrim, encRS,
      keyIndRespToVal, keyIndRenc]

theorem testB_eval (sidV : Var Γ₂ sessionIdTy) (sid : SessionId S)
    (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid) :
    (testB K st sidV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.testSession sid)).run s := by
  unfold testB
  core_simp [hs, hsid, List.take_of_length_le, hB.sessions_le, hB.respSessions_le]
  simp only [pqxdhKeyIndImplPrim, isKeyIndSessionTestable]
  rcases h1 : s.sessions.find? (fun e => e.sid == sid) with _ | e
  · rcases h2 : s.respSessions.find? (fun r => r.sid == sid) with _ | r
    · simp [h1, h2, encRS, keyIndRespToVal, keyIndRenc]
    · simp [h1, h2]
      cases hf : r.senderHonest <;> cases ht : r.tested <;> cases hr : r.revealed <;>
        simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV]
      all_goals (try (refine ⟨by split_ifs <;> rfl, fun x _ => by split_ifs <;> rfl⟩))
  · simp [h1]
    cases hf : e.fresh <;> cases ht : e.tested <;> cases hr : e.revealed <;>
      simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV]
    all_goals (try (refine ⟨by split_ifs <;> rfl, fun x _ => by split_ifs <;> rfl⟩))

theorem revealB_eval (sidV : Var Γ₂ sessionIdTy) (sid : SessionId S)
    (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid) :
    (revealB K st sidV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.revealSessionKey sid)).run s := by
  unfold revealB
  core_simp [hs, hsid, List.take_of_length_le, hB.sessions_le, hB.respSessions_le]
  simp only [pqxdhKeyIndImplPrim]
  rcases h1 : s.sessions.find? (fun e => e.sid == sid) with _ | e
  · rcases h2 : s.respSessions.find? (fun r => r.sid == sid) with _ | r
    · simp [h1, h2, encRS, keyIndRespToVal, keyIndRenc]
    · simp [h1, h2]
      cases ht : r.tested <;> simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV]
      all_goals (try (intro x _; split_ifs <;> rfl))
  · simp [h1]
    cases ht : e.tested <;> simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV]
    all_goals (try (intro x _; split_ifs <;> rfl))

set_option maxHeartbeats 1000000 in
theorem initiateOpkB_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (initiateOpkB useRo S K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.initiateOPK u i b)).run s := by
  unfold initiateOpkB initiateC initFinishC
  simp only [bindV, letV_eval, caseOptV, Comp.eval, koskBundleOkC_eval, resolveSigPkC_eval,
    hkdfOrRoC_eval, honestPeerC_eval, checkProvC_eval, findHonestC_eval]
  core_simp [hs, hx, take_minK, hB.opkEntries_le, hB.respSessions_le, List.take_of_length_le, hB.principals_le, hB.sessions_le, hB.roCache_le,
    hB.spkBundles_le, hB.advKeys_le, decPrin_enc, decSpks_enc, decOpks_enc, decRo_enc,
    evalHkdfOrRoK_eq, checkProvK_eq]
  rw [decPrin_enc, decSpks_enc, decOpks_enc']
  have hsid : (s.sessions.any fun x => sidEqV (sessionIdToVal x.sid) (.inl (u.val, i.val))) =
      s.sessions.any (fun e => e.sid == .sendOPK u i) := by
    congr 1; funext x; exact sidEqV_enc x.sid (.sendOPK u i)
  erw [hsid]
  rw [decRo_enc]
  core_simp [partnerC, take_minK, List.take_of_length_le, hB.principals_le, hB.opkEntries_le, preKeyBundleToVal, bundleV, evalHkdfOrRoK_eq, hB.roCache_le, checkProvK_eq,
    hB.spkBundles_le]
  simp only [pqxdhKeyIndImplPrim]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  · by_cases h1 : ∃ x ∈ s.sessions, x.sid = .sendOPK u i
    · simp [hb, h1, runKeyIndInitiatePrim, encRS, keyIndRespToVal, keyIndRenc]
    · rcases hf : s.principals.find? (fun x => x.1 == u.val) with _ | ⟨k, e⟩
      · simp [hb, h1, hf, runKeyIndInitiatePrim, encRS, keyIndRespToVal, keyIndRenc]
      · obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
        simp only at hb; subst hb
        simp [h1, hf, runKeyIndInitiatePrim, liftM, sampleScalar32, sampleCoins32,
          encodeEC, encodeKEM, keyIndPartnerPrim, buildSecrets]
        refine bind_congr fun v => ?_
        cases v
        · simp [encRS, keyIndRespToVal, keyIndRenc]
        · simp [StateT.run_bind, StateT.run_monadLift]
          refine bind_congr fun a => ?_
          refine bind_congr fun a1 => ?_
          refine bind_congr fun a2 => ?_
          refine bind_congr fun a3 => ?_
          refine bind_congr fun a4 => ?_
          by_cases hc : a3 = false ∨ a4 = false
          · simp [hc, encRS, keyIndRespToVal, keyIndRenc]
          · simp [hc]
            refine bind_congr fun kr => ?_
            rcases kr with _ | ⟨ss, kemCt⟩
            · simp [encRS, keyIndRespToVal, keyIndRenc]
            · simp
              refine bind_congr fun a5 => ?_
              refine bind_congr fun a6 => ?_
              refine bind_congr fun a7 => ?_
              refine bind_congr fun a8 => ?_
              refine bind_congr fun a9 => ?_
              refine bind_congr fun a10 => ?_
              refine bind_congr fun a11 => ?_
              refine bind_congr fun a12 => ?_
              refine bind_congr2 ?_ fun a13 => ?_
              · refine congrArg (fun p => findMPrim p _) (funext fun r => ?_)
                refine bind_congr fun b1 => ?_
                refine bind_congr fun b2 => ?_
                refine bind_congr fun b3 => ?_
                refine bind_congr fun b4 => ?_
                refine bind_congr fun b5 => ?_
                refine bind_congr fun b6 => ?_
                refine bind_congr fun b7 => ?_
                cases hr : r.opkPk? <;> simp [hdrV]
              · rcases a13 with _ | r
                · simp
                  refine bind_congr fun d => ?_
                  rw [map_eq_bind_pure_comp]
                  refine bind_congr fun h => ?_
                  cases h <;> cases a11 <;>
                    simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
                      keyIndSessionEntryToVal, sidV]
                · simp
                  rw [map_eq_bind_pure_comp]
                  refine bind_congr fun h => ?_
                  cases h <;> cases a11 <;>
                    simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
                      keyIndSessionEntryToVal, sidV]

set_option maxHeartbeats 1000000 in
theorem initiateNoOpkB_eval (xV : Var Γ₂ initQTy) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (b : PreKeyBundleInput) (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal b))) :
    (initiateNoOpkB useRo S K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.initiateNoOPK u i b)).run s := by
  unfold initiateNoOpkB initiateC initFinishC initSidE
  simp only [Bool.false_eq_true, ↓reduceIte, bindV, letV_eval, caseOptV, Comp.eval,
    koskBundleOkC_eval, resolveSigPkC_eval, hkdfOrRoC_eval, honestPeerC_eval, checkProvC_eval,
    findHonestC_eval]
  core_simp [hs, hx, take_minK, hB.opkEntries_le, hB.respSessions_le, List.take_of_length_le, hB.principals_le, hB.sessions_le, hB.roCache_le,
    hB.spkBundles_le, hB.advKeys_le, decPrin_enc, decSpks_enc, decOpks_enc, decRo_enc,
    evalHkdfOrRoK_eq, checkProvK_eq]
  rw [decPrin_enc, decSpks_enc, decOpks_enc']
  have hsid :
      (s.sessions.any fun x => sidEqV (sessionIdToVal x.sid) (.inr (.inl (u.val, i.val)))) =
        s.sessions.any (fun e => e.sid == .sendNoOPK u i) := by
    congr 1; funext x; exact sidEqV_enc x.sid (.sendNoOPK u i)
  erw [hsid]
  rw [decRo_enc]
  core_simp [partnerC, take_minK, List.take_of_length_le, hB.principals_le, hB.opkEntries_le, preKeyBundleToVal, bundleV, evalHkdfOrRoK_eq, hB.roCache_le, checkProvK_eq,
    hB.spkBundles_le]
  simp only [pqxdhKeyIndImplPrim]
  rcases hb : b.opkB? with _ | ⟨oid, opk⟩
  · by_cases h1 : ∃ x ∈ s.sessions, x.sid = .sendNoOPK u i
    · simp [hb, h1, runKeyIndInitiatePrim, encRS, keyIndRespToVal, keyIndRenc]
    · rcases hf : s.principals.find? (fun x => x.1 == u.val) with _ | ⟨k, e⟩
      · simp [hb, h1, hf, runKeyIndInitiatePrim, encRS, keyIndRespToVal, keyIndRenc]
      · obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
        simp only at hb; subst hb
        simp [h1, hf, runKeyIndInitiatePrim, liftM, sampleScalar32, sampleCoins32,
          encodeEC, encodeKEM, keyIndPartnerPrim, buildSecrets]
        refine bind_congr fun v => ?_
        cases v
        · simp [encRS, keyIndRespToVal, keyIndRenc]
        · simp [StateT.run_bind, StateT.run_monadLift]
          refine bind_congr fun a => ?_
          refine bind_congr fun a1 => ?_
          refine bind_congr fun a2 => ?_
          refine bind_congr fun a3 => ?_
          refine bind_congr fun a4 => ?_
          by_cases hc : a3 = false ∨ a4 = false
          · simp [hc, encRS, keyIndRespToVal, keyIndRenc]
          · simp [hc]
            refine bind_congr fun kr => ?_
            rcases kr with _ | ⟨ss, kemCt⟩
            · simp [encRS, keyIndRespToVal, keyIndRenc]
            · simp
              refine bind_congr fun a5 => ?_
              refine bind_congr fun a6 => ?_
              refine bind_congr fun a7 => ?_
              refine bind_congr fun a8 => ?_
              refine bind_congr fun a9 => ?_
              refine bind_congr fun a10 => ?_
              refine bind_congr fun a11 => ?_
              refine bind_congr fun a12 => ?_
              refine bind_congr2 ?_ fun a13 => ?_
              · refine congrArg (fun p => findMPrim p _) (funext fun r => ?_)
                refine bind_congr fun b1 => ?_
                refine bind_congr fun b2 => ?_
                refine bind_congr fun b3 => ?_
                refine bind_congr fun b4 => ?_
                refine bind_congr fun b5 => ?_
                refine bind_congr fun b6 => ?_
                refine bind_congr fun b7 => ?_
                cases hr : r.opkPk? <;> simp [hdrV]
              · rcases a13 with _ | r
                · simp
                  refine bind_congr fun d => ?_
                  rw [map_eq_bind_pure_comp]
                  refine bind_congr fun h => ?_
                  cases h <;> cases a11 <;>
                    simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
                      keyIndSessionEntryToVal, sidV]
                · simp
                  rw [map_eq_bind_pure_comp]
                  refine bind_congr fun h => ?_
                  cases h <;> cases a11 <;>
                    simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
                      keyIndSessionEntryToVal, sidV]
  · simp [encRS, keyIndRespToVal, keyIndRenc]

set_option maxHeartbeats 1000000 in
theorem acceptOpkB_eval (xV : Var Γ₂ accQTy) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (h : HandshakeHdr) (hx : env.get (Ext.wk xV) = (k.val, (j.val, (o.val, handshakeHdrToVal h)))) :
    (acceptOpkB useRo S K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.acceptOPK k j o h)).run s := by
  unfold acceptOpkB recordRespC
  simp only [bindV, letV_eval, caseOptV, Comp.eval, koskSenderOkC_eval, acceptKeysC_eval,
    hkdfOrRoC_eval, findHonestC_eval]
  core_simp [hs, hx, take_minK, hB.opkEntries_le, hB.respSessions_le, List.take_of_length_le, hB.principals_le, hB.spkBundles_le, hB.opkEntries_le,
    hB.usedRecvOPK_le, hB.usedKyberTriples_le, hB.roCache_le, hB.advKeys_le, decPrin_enc,
    decRo_enc, evalHkdfOrRoK_eq, acceptKeysPrim_eq]
  erw [hx]
  rw [decPrin_enc, decRo_enc]
  core_simp [partnerC, take_minK, hB.respSessions_le, hB.principals_le, evalHkdfOrRoK_eq, hB.roCache_le, findMPrim_take_map,
    List.take_of_length_le, hB.sessions_le]
  obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := h
  simp only [pqxdhKeyIndImplPrim, handshakeHdrToVal, hdrV, valToHandshakeHdr, hdrOfV]
  have hu : (s.usedRecvOPK.any fun x => ↑k == x.1 && (↑j == x.2.1 && ↑o == x.2.2)) =
      s.usedRecvOPK.contains (↑k, ↑j, ↑o) := by
    rw [List.contains_eq_any_beq]; congr 1
  simp only [hu]
  rcases oId with _ | oid
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  by_cases hg : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j && oid == UInt32.ofNat ↑o &&
      ikA.length == 32 && ekA.length == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, encRS, keyIndRespToVal, keyIndRenc]
  by_cases h1 : (↑k, ↑j, ↑o) ∈ s.usedRecvOPK
  · simp [hg, h1, encRS, keyIndRespToVal, keyIndRenc]
  simp [hg, h1, liftM]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  rcases hk : s.principals.find? (fun x => x.1 == ↑k) with _ | ⟨k', kE⟩
  · simp [hk, encRS, keyIndRespToVal, keyIndRenc]
  rcases hb : s.spkBundles.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) with _ | ⟨b', bE⟩
  · simp [hk, hb, nat2_beq, encRS, keyIndRespToVal, keyIndRenc]
  rcases ho : s.opkEntries.find? (fun x => x.1.1 == ↑k && (x.1.2.1 == ↑j && x.1.2.2 == ↑o))
    with _ | ⟨o', oE⟩
  · simp [hk, hb, ho, nat2_beq, nat3_beq, encRS, keyIndRespToVal, keyIndRenc]
  simp [hk, hb, ho, nat2_beq, nat3_beq]
  by_cases hc : oE.consumed = true
  · simp [hc, encRS, keyIndRespToVal, keyIndRenc]
  simp [hc, StateT.run_bind, StateT.run_monadLift, recordKeyIndRespPrim, liftM,
    checkAndMarkKyberBaseKeySeen]
  refine bind_congr fun acc => ?_
  rcases acc with _ | acc
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  simp
  refine bind_congr fun ss => ?_
  rcases ss with _ | ss
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  simp [buildSecrets]
  refine bind_congr fun d1 => ?_
  refine bind_congr fun d2 => ?_
  refine bind_congr fun d3 => ?_
  refine bind_congr fun d4 => ?_
  refine bind_congr fun dr => ?_
  refine bind_congr fun fh => ?_
  refine bind_congr2 ?_ fun fd => ?_
  · refine congrArg (fun p => findMPrim p _) (funext fun r => ?_)
    simp only [keyIndPartnerPrim]
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    cases hr : r.peerOpkPk? <;> simp [map_eq_bind_pure_comp]
  · rcases fd with _ | r
    · simp
      refine bind_congr fun d => ?_
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun h => ?_
      cases h <;> cases fh <;>
        simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
          keyIndRespEntryToVal, sidV]
      all_goals (try (intro a a_1 b b_1 _; split_ifs <;> rfl))
    · simp
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun h => ?_
      cases h <;> cases fh <;>
        simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
          keyIndRespEntryToVal, sidV]
      all_goals (try (intro a a_1 b b_1 _; split_ifs <;> rfl))

set_option maxHeartbeats 1000000 in
theorem acceptNoOpkB_eval (xV : Var Γ₂ accQTy) (k : Fin S.N_id) (j : Fin S.N_recv)
    (l : Fin S.N_no_opk) (h : HandshakeHdr)
    (hx : env.get (Ext.wk xV) = (k.val, (j.val, (l.val, handshakeHdrToVal h)))) :
    (acceptNoOpkB useRo S K st xV).eval env =
      encRS <$> (pqxdhKeyIndImplPrim useRo S (.acceptNoOPK k j l h)).run s := by
  unfold acceptNoOpkB recordRespC
  simp only [bindV, letV_eval, caseOptV, Comp.eval, koskSenderOkC_eval, acceptKeysC_eval,
    hkdfOrRoC_eval, findHonestC_eval]
  core_simp [hs, hx, take_minK, hB.opkEntries_le, hB.respSessions_le, List.take_of_length_le, hB.principals_le, hB.spkBundles_le,
    hB.usedRecvNoOPK_le, hB.usedKyberTriples_le, hB.roCache_le, hB.advKeys_le, decPrin_enc,
    decRo_enc, evalHkdfOrRoK_eq, acceptKeysPrim_eq]
  erw [hx]
  rw [decPrin_enc, decRo_enc]
  core_simp [partnerC, take_minK, hB.respSessions_le, hB.principals_le, evalHkdfOrRoK_eq, hB.roCache_le, findMPrim_take_map,
    List.take_of_length_le, hB.sessions_le]
  obtain ⟨ikA, ekA, sId, oId, pqId, ct⟩ := h
  simp only [pqxdhKeyIndImplPrim, handshakeHdrToVal, hdrV, valToHandshakeHdr, hdrOfV]
  have hu : (s.usedRecvNoOPK.any fun x => ↑k == x.1 && (↑j == x.2.1 && ↑l == x.2.2)) =
      s.usedRecvNoOPK.contains (↑k, ↑j, ↑l) := by
    rw [List.contains_eq_any_beq]; congr 1
  simp only [hu]
  rcases oId with _ | oid
  swap
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  by_cases hg : (sId == UInt32.ofNat ↑j && pqId == UInt32.ofNat ↑j &&
      ikA.length == 32 && ekA.length == 32) = true
  swap
  · simp only [Bool.not_eq_true] at hg
    simp [hg, encRS, keyIndRespToVal, keyIndRenc]
  by_cases h1 : (↑k, ↑j, ↑l) ∈ s.usedRecvNoOPK
  · simp [hg, h1, encRS, keyIndRespToVal, keyIndRenc]
  simp [hg, h1, liftM]
  refine bind_congr fun ok => ?_
  cases ok
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  rcases hk : s.principals.find? (fun x => x.1 == ↑k) with _ | ⟨k', kE⟩
  · simp [hk, encRS, keyIndRespToVal, keyIndRenc]
  rcases hb : s.spkBundles.find? (fun x => x.1.1 == ↑k && x.1.2 == ↑j) with _ | ⟨b', bE⟩
  · simp [hk, hb, nat2_beq, encRS, keyIndRespToVal, keyIndRenc]
  simp [hk, hb, nat2_beq, StateT.run_bind, StateT.run_monadLift, recordKeyIndRespPrim,
    liftM, checkAndMarkKyberBaseKeySeen]
  refine bind_congr fun acc => ?_
  rcases acc with _ | acc
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  simp
  refine bind_congr fun ss => ?_
  rcases ss with _ | ss
  · simp [encRS, keyIndRespToVal, keyIndRenc]
  simp [buildSecrets]
  refine bind_congr fun d1 => ?_
  refine bind_congr fun d2 => ?_
  refine bind_congr fun d3 => ?_
  refine bind_congr fun dr => ?_
  refine bind_congr fun fh => ?_
  refine bind_congr2 ?_ fun fd => ?_
  · refine congrArg (fun p => findMPrim p _) (funext fun r => ?_)
    simp only [keyIndPartnerPrim]
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    refine bind_congr fun _ => ?_
    cases hr : r.peerOpkPk? <;> simp [map_eq_bind_pure_comp]
  · rcases fd with _ | r
    · simp
      refine bind_congr fun d => ?_
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun h => ?_
      cases h <;> cases fh <;>
        simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
          keyIndRespEntryToVal, sidV]
    · simp
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun h => ?_
      cases h <;> cases fh <;>
        simp [encRS, keyIndRespToVal, keyIndRenc, drKeyV, hdrV,
          keyIndRespEntryToVal, sidV]

end

end SignalPqxdh.Security.ReductionDsl.KeyInd
