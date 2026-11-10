/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3E -- shake: keep
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh -- shake: keep

/-!
# Shared Evaluation and Leaf-Invariant Lemmas for `Auth` PRF Reductions

Proves shared expression and computation evaluation lemmas and list-length leaf invariants
(`AllLeaves`, `AuthListsBounded`, `PreparedRecvBounded`, `RecvTagBounded`) for the `Auth` PRF
reductions.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 100000
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

/-! ## Binder, Combinator, Op, Sampler, and Query Lemmas -/

@[simp] theorem Ext.step_wk {Γ Δ : List PT} {σ τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ) (Γ := Γ) (Δ := Δ)).wk x = .succ (h.wk x) := rfl

@[simp] theorem Ext.refl_wk {Γ : List PT} {τ : PT} (x : Var Γ τ) :
    (Ext.refl (Γ := Γ)).wk x = x := rfl

@[simp] theorem Env.get_succ {Γ : List PT} {σ τ : PT} (x : Var Γ τ) (a : σ.denote)
    (env : Env Γ) : Env.get (.cons a env) (.succ x) = Env.get env x := rfl

@[simp] theorem Env.get_zero {Γ : List PT} {σ : PT} (a : σ.denote) (env : Env Γ) :
    Env.get (.cons a env) .zero = a := rfl

@[simp] theorem eval_letC {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (e : Expr pqxdhOps Γ a) (k : Comp pqxdhOps I (a :: Γ) b) (env : Env Γ) :
    (Comp.letC e k).eval env = k.eval (.cons (e.eval env) env) := by
  simp [Comp.letC, Comp.eval]

@[simp] theorem mapML_eq_mapMPrim {α β : Type}
    (f : α → OracleComp PrimBaseSpec β) (xs : List α) :
    _root_.ReductionDsl.mapML f xs = SignalPqxdh.Security.mapMPrim f xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp only [_root_.ReductionDsl.mapML, SignalPqxdh.Security.mapMPrim, ih]

@[simp] theorem findML_eq_findMPrim {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (xs : List α) :
    _root_.ReductionDsl.findML p xs = SignalPqxdh.Security.findMPrim p xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp only [_root_.ReductionDsl.findML, SignalPqxdh.Security.findMPrim, ih]

@[simp] theorem anyML_eq_anyMPrim {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (xs : List α) :
    _root_.ReductionDsl.anyML p xs = SignalPqxdh.Security.anyMPrim p xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp only [_root_.ReductionDsl.anyML, SignalPqxdh.Security.anyMPrim, ih]

@[simp] theorem consumeFirstML_eq_consumeFirstMPrim {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (mark : α → α) (xs : List α) :
    _root_.ReductionDsl.consumeFirstML p mark xs =
      AuthSubHops1to3.consumeFirstMPrim p mark xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [_root_.ReductionDsl.consumeFirstML, AuthSubHops1to3.consumeFirstMPrim, ih]

@[simp] theorem authSubHops1to3_mapMPrim_eq {α β : Type}
    (f : α → OracleComp PrimBaseSpec β) (xs : List α) :
    AuthSubHops1to3.mapMPrim f xs = SignalPqxdh.Security.mapMPrim f xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp only [AuthSubHops1to3.mapMPrim, SignalPqxdh.Security.mapMPrim, ih]

@[simp] theorem boolOr_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) (env : Env Γ) :
    (boolOr a b).eval env = (a.eval env || b.eval env) := by
  simp only [boolOr, Expr.eval]
  cases a.eval env <;> rfl

@[simp] theorem boolBeq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .bool) (env : Env Γ) :
    (boolBeq a b).eval env = (a.eval env == b.eval env) := by
  simp only [boolBeq, Expr.eval]
  cases a.eval env <;> cases b.eval env <;> rfl

@[simp] theorem litB_eval {Γ : List PT} (w : ℕ+) (bs : Bytes) (env : Env Γ) :
    (litB w bs).eval env = bs := rfl

@[simp] theorem catB_eval {Γ : List PT} (m n : ℕ+)
    (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) (env : Env Γ) :
    (catB m n a b).eval env = a.eval env ++ b.eval env := rfl

@[simp] theorem bytesCons_eval {Γ : List PT} (b : UInt8) (w : ℕ+)
    (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (bytesCons b w x).eval env = b :: x.eval env := rfl

@[simp] theorem widenB_eval {Γ : List PT} (w d : ℕ+)
    (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (widenB w d x).eval env = x.eval env := rfl

@[simp] theorem takeKB_eval {Γ : List PT} (w k : ℕ+)
    (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (takeKB w k x).eval env = (x.eval env).take k.val := rfl

@[simp] theorem bytesLen_eval {Γ : List PT} (w : ℕ+)
    (x : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (bytesLen w x).eval env = (x.eval env).length := rfl

@[simp] theorem bytesBeq_eval {Γ : List PT} (w : ℕ+)
    (a b : Expr pqxdhOps Γ (B w)) (env : Env Γ) :
    (bytesBeq w a b).eval env = (a.eval env == b.eval env) := rfl

@[simp] theorem bytesVarint_eval {Γ : List PT}
    (n : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (bytesVarint n).eval env = pbVarint (n.eval env) := rfl

@[simp] theorem u32OfNat_eval {Γ : List PT}
    (n : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (u32OfNat n).eval env = UInt32.ofNat (n.eval env) := rfl

@[simp] theorem u32Beq_eval {Γ : List PT}
    (a b : Expr pqxdhOps Γ U32) (env : Env Γ) :
    (u32Beq a b).eval env = (a.eval env == b.eval env) := rfl

@[simp] theorem fgGapDh_embedUnif_eq {α : Type} (p : ProbComp α) :
    FgGapDh.embedUnif p = embedUnif p := rfl

@[simp] theorem pqPrimIface_liftP_eq {α : Type} (p : ProbComp α) :
    pqPrimIface.liftP p = embedUnif p := rfl

@[simp] theorem sampleIndex_eq_sampleIndexRange (N : ℕ) :
    sampleIndex N = RoKem.sampleIndexRange N := rfl

@[simp] theorem samplePrim_bool_eval {Γ : List PT} (env : Env Γ) :
    (samplePrim .bool).eval env = embedUnif ($ᵗ Bool) := rfl

@[simp] theorem samplePrim_bytes32_eval {Γ : List PT} (env : Env Γ) :
    (samplePrim .bytes32).eval env = embedUnif sampleBytes32 := rfl

@[simp] theorem samplePrim_random64_eval {Γ : List PT} (env : Env Γ) :
    (samplePrim .random64).eval env = embedUnif sampleRandom64 := rfl

@[simp] theorem samplePrim_drKey96_eval {Γ : List PT} (env : Env Γ) :
    (samplePrim .drKey96).eval env = drKeyToVal <$> embedUnif sampleDRKey96 := by
  simp only [samplePrim, Comp.eval, pqPrimIface, pqSamplers, PSamp.run, Iface.liftP,
    embedUnif, liftComp, simulateQ_map]
  rfl

@[simp] theorem samplePrim_msgKeys80_eval {Γ : List PT} (env : Env Γ) :
    (samplePrim .msgKeys80).eval env = msgKeysToVal <$> embedUnif sampleMessageKeys80 := by
  simp only [samplePrim, Comp.eval, pqPrimIface, pqSamplers, PSamp.run, Iface.liftP,
    embedUnif, liftComp, simulateQ_map]
  rfl

@[simp] theorem samplePrim_index_eval {Γ : List PT} (N : ℕ) (env : Env Γ) :
    (samplePrim (.index N)).eval env = embedUnif (RoKem.sampleIndexRange N) := rfl

@[reducible] def evalPrimOp : (t : PTag) → t.dom.denote → OracleComp PrimBaseSpec t.cod.denote
  | .x25519 => fun x => primQ (.x25519 x.1 x.2)
  | .x25519Base => fun sk => primQ (.x25519Base sk)
  | .isCanonical => fun pk => primQ (.isCanonical pk)
  | .pow8 => fun pk => primQ (.pow8 pk)
  | .sigPkGen => fun sk => primQ (.sigPkGen sk)
  | .sigSign _ => fun x => primQ (.sigSign x.1 x.2.1 x.2.2)
  | .sigVerify _ => fun x => primQ (.sigVerify x.1 x.2.1 x.2.2)
  | .kemKeyGen => fun coins => primQ (.kemKeyGen coins)
  | .kemEncaps => fun x => primQ (.kemEncaps x.1 x.2)
  | .kemDecaps => fun x => primQ (.kemDecaps x.1 x.2)
  | .hkdfDerive96 _ => fun bytes => drKeyToVal <$> primQ (.hkdfDerive96 bytes)
  | .rootCreateChain => fun x => primQ (.rootCreateChain x.1 x.2)
  | .chainKdfSeed => fun ck => primQ (.chainKdfSeed ck)
  | .chainKdfNext => fun ck => primQ (.chainKdfNext ck)
  | .spqrInitSend _ _ => fun x => primQ (.spqrInitSend x.1 x.2)
  | .spqrInitRecv _ _ => fun x => primQ (.spqrInitRecv x.1 x.2)
  | .deriveMsgKeys _ => fun x => msgKeysToVal <$> primQ (.deriveMsgKeys x.1 x.2)
  | .aeadEnc _ _ _ => fun x => primQ (.aeadEnc (valToMsgKeys x.1) x.2.1 x.2.2)
  | .aeadDec _ _ _ => fun x => primQ (.aeadDec (valToMsgKeys x.1) x.2.1 x.2.2)

@[simp] def evalPrimQ {τ₁ τ₂ : PT} (f : τ₁.denote → OracleComp PrimBaseSpec τ₂.denote)
    (x : τ₁.denote) : OracleComp PrimBaseSpec τ₂.denote :=
  f x

@[simp] theorem queryPrim_eval {Γ : List PT} (t : PTag) (e : Expr pqxdhOps Γ t.dom) (env : Env Γ) :
    (queryPrim t e).eval env = evalPrimQ (evalPrimOp t) (e.eval env) := by
  cases t <;>
    simp only [queryPrim, evalPrimQ, evalPrimOp, Comp.eval, pqPrimIface, SignalPqxdh.LegacyCosted.PTag.enc, SignalPqxdh.LegacyCosted.PTag.dec]
  all_goals rfl

@[simp] theorem pair_beq_split {α β : Type} [BEq α] [BEq β] (p : α × β) (c : α) (d : β) :
    (p == (c, d)) = (p.1 == c && p.2 == d) := by
  rcases p with ⟨a, b⟩; rfl

@[simp] theorem map_nat3Tuple_id (l : List (Nat × Nat × Nat)) :
    l.map (fun (k, j, o) => (k, (j, o))) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨k, j, o⟩; simp [ih]

@[simp] theorem prod_map_nat3_id {α β : Type} (f : α → β) :
    Prod.map (fun (p : Nat × Nat × Nat) => (p.1, (p.2.1, p.2.2))) f = Prod.map id f := rfl

@[simp] theorem natEq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (natEq a b).eval env = (a.eval env == b.eval env) := by
  simp [natEq, Expr.eval, BEq.beq]

@[simp] theorem natLt_expr_eval {Γ : List PT} (a b : Expr pqxdhOps Γ .nat) (env : Env Γ) :
    (natLt a b).eval env = decide (a.eval env < b.eval env) := rfl

@[simp] theorem nat2Eq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat .nat)) (env : Env Γ) :
    (nat2Eq a b).eval env = (a.eval env == b.eval env) := by
  simp only [nat2Eq, natEq_eval, Expr.eval]
  rcases a.eval env with ⟨a1, a2⟩; rcases b.eval env with ⟨b1, b2⟩; rfl

@[simp] theorem nat3Eq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ (.prod .nat (.prod .nat .nat)))
    (env : Env Γ) :
    (nat3Eq a b).eval env = (a.eval env == b.eval env) := by
  simp only [nat3Eq, nat2Eq_eval, natEq_eval, Expr.eval]
  rcases a.eval env with ⟨a1, a2, a3⟩; rcases b.eval env with ⟨b1, b2, b3⟩; rfl

@[simp] theorem optU32Eq_eval {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt U32)) (env : Env Γ) :
    (optU32Eq a b).eval env = (a.eval env == b.eval env) := by
  simp only [optU32Eq, eLet2, eLet, eCaseOpt, v, Expr.eval, Ext.wk,
    Env.get_succ, Env.get_zero, u32Beq_eval]
  cases a.eval env <;> cases b.eval env <;> rfl

theorem sidEq_eval {S : Setup} {Γ : List PT} (a b : Expr pqxdhOps Γ sessionIdTy) (env : Env Γ)
    (s1 s2 : SessionId S) (ha : a.eval env = sessionIdToVal s1)
    (hb : b.eval env = sessionIdToVal s2) :
    (sidEq a b).eval env = (s1 == s2) := by
  simp only [sidEq, eLet2, eLet, eCaseSum, nat2Eq_eval, nat3Eq_eval, v, Expr.eval,
    Ext.wk, Env.get_succ, Env.get_zero, ha, hb]
  cases s1 <;> cases s2 <;> simp only [sessionIdToVal, sidV] <;>
    first | rfl | (rw [Bool.eq_iff_iff]; simp [Fin.ext_iff])

theorem saltBytesE_eval {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) (env : Env Γ) :
    (saltBytesE o).eval env = (effectiveHkdfSaltBytes (o.eval env)).toList := by
  simp only [saltBytesE, eCaseOpt, v, Expr.eval]
  cases o.eval env with
  | none => rfl
  | some s =>
    change List.take 32 (s ++ List.replicate 32 0) =
      List.take 32 s ++ List.replicate (32 - s.length) 0
    rw [List.take_append, List.take_replicate, Nat.min_eq_left (by omega)]

theorem sameSaltKeyE_eval {Γ : List PT} (a b : Expr pqxdhOps Γ (.opt (B 32))) (env : Env Γ) :
    (sameSaltKeyE a b).eval env = sameSaltKey (a.eval env) (b.eval env) := by
  simp only [sameSaltKeyE, bytesBeq_eval, saltBytesE_eval, sameSaltKey]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => List.Vector.eq _ _ h, fun h => h ▸ rfl⟩

@[simp] theorem isSomeE_eval {Γ : List PT} {τ : PT} (o : Expr pqxdhOps Γ (.opt τ)) (env : Env Γ) :
    (isSomeE o).eval env = (o.eval env).isSome := by
  simp only [isSomeE, Expr.eval]
  cases o.eval env <;> rfl

@[simp] theorem optSnd_eval {Γ : List PT} {τ₁ τ₂ : PT} (o : Expr pqxdhOps Γ (.opt (.prod τ₁ τ₂)))
    (env : Env Γ) :
    (optSnd o).eval env = (o.eval env).map Prod.snd := by
  simp only [optSnd, eCaseOpt, v, Expr.eval, Ext.wk, Env.get_zero]
  cases o.eval env <;> rfl

@[simp] theorem encEC_eval {Γ : List PT} (pk : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (encEC pk).eval env = encodeEC (pk.eval env) := rfl

@[simp] theorem encKEM_eval {Γ : List PT} (pk : Expr pqxdhOps Γ (B 1568)) (env : Env Γ) :
    (encKEM pk).eval env = encodeKEM (pk.eval env) := rfl

theorem firstMsgAD_split (ikA ikB ephAPk pq : Bytes) :
    firstMsgAD ikA ikB ephAPk pq =
      encodeEC ikA ++ encodeEC ikB ++ [0x44] ++
        ((8 * 1 + 2 : Nat).toUInt8 :: (pbVarint (encodeEC ephAPk).length ++ encodeEC ephAPk)) ++
        [0x10, 0x00, 0x18, 0x00] ++
        (if (pq.length == 0) = true then []
         else (8 * 5 + 2 : Nat).toUInt8 :: (pbVarint pq.length ++ pq)) := by
  cases pq <;> rfl

@[simp] theorem firstMsgADE_eval {Γ : List PT} (ikA ikB eph pq : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (firstMsgADE ikA ikB eph pq).eval env =
      firstMsgAD (ikA.eval env) (ikB.eval env) (eph.eval env) (pq.eval env) := by
  rw [firstMsgAD_split]; rfl

/-- Argument congruence for `primQ (.aeadEnc ..)` (the dependent result type blocks `simp`). -/
theorem primQ_aeadEnc_args_eq {mk mk' : MessageKeys} {ad ad' pt pt' : Bytes} (h1 : mk = mk')
    (h2 : ad = ad') (h3 : pt = pt') : primQ (.aeadEnc mk ad pt) = primQ (.aeadEnc mk' ad' pt') := by
  subst h1 h2 h3; rfl

theorem primQ_aeadDec_args_eq {mk mk' : MessageKeys} {ad ad' ct ct' : Bytes} (h1 : mk = mk')
    (h2 : ad = ad') (h3 : ct = ct') : primQ (.aeadDec mk ad ct) = primQ (.aeadDec mk' ad' ct') := by
  subst h1 h2 h3; rfl

@[simp] theorem buildSecretsE_eval {Γ : List PT} (dh1 dh2 dh3 : Expr pqxdhOps Γ (B 32))
    (dh4? : Expr pqxdhOps Γ (.opt (B 32))) (ss : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    (buildSecretsE dh1 dh2 dh3 dh4? ss).eval env =
      buildSecrets (dh1.eval env) (dh2.eval env) (dh3.eval env) (dh4?.eval env) (ss.eval env) := by
  simp only [buildSecretsE, eLet2, eLet, eCaseOpt, v, Expr.eval, Ext.wk,
    Env.get_succ, Env.get_zero]
  cases dh4?.eval env <;> rfl

theorem kyberCheckE_eval {Γ : List PT} (K : Nat)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (env : Env Γ) (hU : (used.eval env).length ≤ K) :
    (kyberCheckE K used entry).eval env =
      checkAndMarkKyberBaseKeySeen (used.eval env) (entry.eval env).1 (entry.eval env).2.1
        (entry.eval env).2.2.1 (entry.eval env).2.2.2 := by
  simp only [kyberCheckE, eLet2, eLet, eAny, kyberEq, natEq_eval, u32Beq_eval, bytesBeq_eval,
    v, Expr.eval, Ext.wk, Env.get_succ, Env.get_zero,
    List.take_of_length_le hU, checkAndMarkKyberBaseKeySeen]
  have hContains :
      ((used.eval env).any fun x =>
        (entry.eval env).1 == x.1 &&
          ((entry.eval env).2.1 == x.2.1 &&
            ((entry.eval env).2.2.1 == x.2.2.1 && (entry.eval env).2.2.2 == x.2.2.2))) =
      (used.eval env).contains
        ((entry.eval env).1, (entry.eval env).2.1, (entry.eval env).2.2.1,
          (entry.eval env).2.2.2) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_exists_mem_beq]
    refine exists_congr (fun x => and_congr_right' ?_)
    rcases x with ⟨x1, x2, x3, x4⟩
    rcases entry.eval env with ⟨e1, e2, e3, e4⟩
    rfl
  rw [hContains]

theorem sessionSlotIndexE_eval {S : Setup} {Γ : List PT} (sid : Expr pqxdhOps Γ sessionIdTy)
    (env : Env Γ) (s : SessionId S) (hs : sid.eval env = sessionIdToVal s) :
    (sessionSlotIndexE S sid).eval env = sessionSlotIndex s := by
  simp only [sessionSlotIndexE, eCaseSum, v, Expr.eval, Ext.refl_wk,
    Env.get_zero, hs]
  cases s with
  | sendOPK u i =>
    have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
    simp [sessionIdToVal, sidV, sessionSlotIndex, hN, Nat.mul_comm]
  | sendNoOPK u i =>
    have hN : S.N_id ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt u.isLt)
    simp [sessionIdToVal, sidV, sessionSlotIndex, hN, Nat.mul_comm]
  | recvOPK _ _ _ => rfl
  | recvNoOPK _ _ _ => rfl

theorem bindV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (bindV m k).eval env = (m.eval env >>= fun x => (k .zero).eval (.cons x env)) := rfl

theorem letV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by
  simp [letV]

theorem letV_eval_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ)
    (val : τ₁.denote) (h : e.eval env = val) :
    (letV e k).eval env = (k .zero).eval (.cons val env) := by
  rw [letV_eval, h]

theorem caseOptV_eval {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (caseOptV o kn ks).eval env =
      match o.eval env with
      | none => kn.eval env
      | some a => (ks .zero).eval (.cons a env) := by
  simp only [caseOptV, Comp.eval]
  cases o.eval env <;> rfl

@[simp] theorem valToMsgKeys_msgKeysToVal (k : MessageKeys) :
    valToMsgKeys (msgKeysToVal k) = k := rfl

theorem findMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.findMPrim p (L.map f) =
      Option.map f <$> SignalPqxdh.Security.findMPrim (fun x => p (f x)) L := by
  induction L with
  | nil => simp [SignalPqxdh.Security.findMPrim]
  | cons x xs ih =>
    simp only [List.map_cons, SignalPqxdh.Security.findMPrim, ih,
      map_eq_bind_pure_comp, bind_assoc]
    congr 1; funext b; cases b <;> simp

theorem anyMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.anyMPrim p (L.map f) =
      SignalPqxdh.Security.anyMPrim (fun x => p (f x)) L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, SignalPqxdh.Security.anyMPrim, ih]

theorem mapMPrim_map {α β γ : Type} (f : α → β)
    (g : β → OracleComp PrimBaseSpec γ) (L : List α) :
    SignalPqxdh.Security.mapMPrim g (L.map f) =
      SignalPqxdh.Security.mapMPrim (fun x => g (f x)) L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, SignalPqxdh.Security.mapMPrim, ih]

theorem consumeFirstMPrim_map {α β : Type} (f : α → β)
    (p : β → OracleComp PrimBaseSpec Bool) (markB : β → β) (markA : α → α)
    (hMark : ∀ a, markB (f a) = f (markA a)) (L : List α) :
    AuthSubHops1to3.consumeFirstMPrim p markB (L.map f) =
      Prod.map id (List.map f) <$>
        AuthSubHops1to3.consumeFirstMPrim (fun a => p (f a)) markA L := by
  induction L with
  | nil => simp [AuthSubHops1to3.consumeFirstMPrim]
  | cons x xs ih =>
    simp only [List.map_cons, AuthSubHops1to3.consumeFirstMPrim, ih,
      map_eq_bind_pure_comp, bind_assoc]
    congr 1; funext b
    cases b with
    | true => simp [Prod.map, hMark x]
    | false => simp [Prod.map]

theorem list_any_beq_eq_contains {α : Type} [BEq α] (xs : List α) (a : α) :
    xs.any (fun x => a == x) = xs.contains a := by
  simp only [List.contains]
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.any_cons, List.elem]
    cases a == b <;> simp [ih]

@[simp] theorem embedPrim_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    FgGapDh.embedPrim (spec := spec) (Pure.pure a) = Pure.pure a := rfl

@[simp] theorem embedPrim_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (m : OracleComp PrimBaseSpec α) (k : α → OracleComp PrimBaseSpec β) :
    FgGapDh.embedPrim (spec := spec) (m >>= k) =
      FgGapDh.embedPrim (spec := spec) m >>= fun a => FgGapDh.embedPrim (spec := spec) (k a) := by
  induction m using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    change (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => FgGapDh.embedPrim (spec := spec) (r u >>= k)) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => FgGapDh.embedPrim (spec := spec) (r u)) >>=
          fun a => FgGapDh.embedPrim (spec := spec) (k a)
    rw [bind_assoc]
    congr 1; funext u
    exact ih u

@[simp] theorem embedPrim_map {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (f : α → β) (m : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) (f <$> m) = f <$> FgGapDh.embedPrim (spec := spec) m := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, embedPrim_bind]
  rfl

@[simp] theorem pqChalIface_liftP_eq {C : ChallengerOracle} {α : Type} (p : ProbComp α) :
    (pqChalIface C).liftP p = FgGapDh.embedPrim (spec := C.spec) (embedUnif p) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    change (query (spec := PrimBaseSpec + C.spec) (.inl (.inl t)) >>=
        fun u => (pqChalIface C).liftP (mx u)) =
      FgGapDh.embedPrim (spec := C.spec)
        (query (spec := PrimBaseSpec) (.inl t) >>= fun u => embedUnif (mx u))
    rw [embedPrim_bind]
    congr 1; funext u
    exact ih u

private theorem embedPrim_iterM {C : ChallengerOracle} {α : Type}
    (f : α → OracleComp PrimBaseSpec α) (n : ℕ) (a : α) :
    iterM (fun x => FgGapDh.embedPrim (spec := C.spec) (f x)) n a =
      FgGapDh.embedPrim (spec := C.spec) (iterM f n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [iterM, embedPrim_bind]
    congr 1; funext x; exact ih x

private theorem embedPrim_findML {C : ChallengerOracle} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (xs : List α) :
    findML (fun x => FgGapDh.embedPrim (spec := C.spec) (p x)) xs =
      FgGapDh.embedPrim (spec := C.spec) (findML p xs) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [findML, embedPrim_bind]
    congr 1; funext b; cases b <;> simp [ih]

private theorem embedPrim_anyML {C : ChallengerOracle} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (xs : List α) :
    anyML (fun x => FgGapDh.embedPrim (spec := C.spec) (p x)) xs =
      FgGapDh.embedPrim (spec := C.spec) (anyML p xs) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [anyML, embedPrim_bind]
    congr 1; funext b; cases b <;> simp [ih]

private theorem embedPrim_mapML {C : ChallengerOracle} {α β : Type}
    (f : α → OracleComp PrimBaseSpec β) (xs : List α) :
    mapML (fun x => FgGapDh.embedPrim (spec := C.spec) (f x)) xs =
      FgGapDh.embedPrim (spec := C.spec) (mapML f xs) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [mapML, embedPrim_bind, embedPrim_pure]
    congr 1; funext y; simp [ih]

private theorem embedPrim_consumeFirstML {C : ChallengerOracle} {α : Type}
    (p : α → OracleComp PrimBaseSpec Bool) (mk : α → α) (xs : List α) :
    consumeFirstML (fun x => FgGapDh.embedPrim (spec := C.spec) (p x)) mk xs =
      FgGapDh.embedPrim (spec := C.spec) (consumeFirstML p mk xs) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [consumeFirstML, embedPrim_bind]
    congr 1; funext b; cases b <;> simp [ih]

private theorem embedPrim_foldML {C : ChallengerOracle} {α β : Type}
    (f : α → β → OracleComp PrimBaseSpec β) (b : β) (xs : List α) :
    foldML (fun x acc => FgGapDh.embedPrim (spec := C.spec) (f x acc)) b xs =
      FgGapDh.embedPrim (spec := C.spec) (foldML f b xs) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x tl ih =>
    simp only [foldML, embedPrim_bind]
    congr 1; funext b'; exact ih b'

@[simp] theorem eval_liftPrimComp {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) (env : Env Γ) :
    (liftPrimComp (C := C) c).eval env =
      FgGapDh.embedPrim (spec := C.spec) (c.eval env) := by
  induction c with
  | ret e => rfl
  | bind m k ihm ihk =>
    simp only [liftPrimComp, Comp.eval, ihm, embedPrim_bind]
    congr 1; funext x; exact ihk (.cons x env)
  | ite b t e iht ihe =>
    simp only [liftPrimComp, Comp.eval]
    split
    · exact iht env
    · exact ihe env
  | caseOpt e n s ihn ihs =>
    simp only [liftPrimComp, Comp.eval]
    cases e.eval env with
    | none => exact ihn env
    | some x => exact ihs (.cons x env)
  | caseSum e l r ihl ihr =>
    simp only [liftPrimComp, Comp.eval]
    cases e.eval env with
    | inl x => exact ihl (.cons x env)
    | inr y => exact ihr (.cons y env)
  | sample s e =>
    simp only [liftPrimComp, Comp.eval, pqChalIface_liftP_eq, pqPrimIface_liftP_eq]
    rfl
  | query g e =>
    simp only [liftPrimComp, Comp.eval, pqChalIface, pqPrimIface]
    rfl
  | iter n init body ihb =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_iterM]
    congr 1; funext a; exact ihb (.cons a env)
  | findM K l p ihp =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_findML]
    congr 1; funext x; exact ihp (.cons x env)
  | anyM K l p ihp =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_anyML]
    congr 1; funext x; exact ihp (.cons x env)
  | mapM K l f ihf =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_mapML]
    congr 1; funext x; exact ihf (.cons x env)
  | consumeFirstM K l p mk ihp =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_consumeFirstML]
    congr 2; funext x; exact ihp (.cons x env)
  | foldM K l init step ihs =>
    simp only [liftPrimComp, Comp.eval, ← embedPrim_foldML]
    congr 2; funext x acc; exact ihs (.cons x (.cons acc env))

@[simp] theorem sampleChal_eval {C : ChallengerOracle} {Γ : List PT} (s : PSamp) (env : Env Γ) :
    (sampleChal (C := C) s).eval env =
      FgGapDh.embedPrim (spec := C.spec) ((samplePrim s).eval env) := by
  simp only [sampleChal, samplePrim, Comp.eval, pqChalIface_liftP_eq, pqPrimIface_liftP_eq]
  rfl

/-- Bounds the lengths of all state lists in `AuthHybridState S` by `n`. -/
structure AuthHybridListsBounded {S : Setup} (n : Nat) (hst : AuthHybridState S) : Prop where
  principals_le       : hst.base.principals.length ≤ n
  spkBundles_le       : hst.base.spkBundles.length ≤ n
  opkEntries_le       : hst.base.opkEntries.length ≤ n
  sessions_le         : hst.base.sessions.length ≤ n
  usedSendSessions_le : hst.base.usedSendSessions.length ≤ n
  usedRecvOPK_le      : hst.base.usedRecvOPK.length ≤ n
  usedRecvNoOPK_le    : hst.base.usedRecvNoOPK.length ≤ n
  usedKyberTriples_le : hst.base.seenKyberBaseKeys.length ≤ n
  roCache_le          : hst.base.roCache.length ≤ n
  rootRoCache_le      : hst.base.rootRoCache.length ≤ n
  advKeys_le          : hst.base.advKeys.length ≤ n
  initKemRecs_le      : hst.initKemRecs.length ≤ n
  recvKemRecs_le      : hst.recvKemRecs.length ≤ n
  sentOPKEvents_le    : hst.base.sentOPKEvents.length ≤ n
  sentNoOPKEvents_le  : hst.base.sentNoOPKEvents.length ≤ n
  idealSessions_le    : hst.idealSessions.length ≤ n

/-- Bounds the lengths of all state lists in `AuthHybridStateFixed S` by `n`. -/
structure AuthListsBounded {S : Setup} (n : Nat) (hst : AuthHybridStateFixed S) : Prop extends
    AuthHybridListsBounded n hst.toAuthHybridState where
  mkSaltCache_le : hst.mkSaltCache.length ≤ n

theorem AuthHybridListsBounded.mono {S : Setup} {n m : Nat} {hst : AuthHybridState S}
    (h : n ≤ m) (hB : AuthHybridListsBounded n hst) : AuthHybridListsBounded m hst where
  principals_le       := Nat.le_trans hB.principals_le h
  spkBundles_le       := Nat.le_trans hB.spkBundles_le h
  opkEntries_le       := Nat.le_trans hB.opkEntries_le h
  sessions_le         := Nat.le_trans hB.sessions_le h
  usedSendSessions_le := Nat.le_trans hB.usedSendSessions_le h
  usedRecvOPK_le      := Nat.le_trans hB.usedRecvOPK_le h
  usedRecvNoOPK_le    := Nat.le_trans hB.usedRecvNoOPK_le h
  usedKyberTriples_le := Nat.le_trans hB.usedKyberTriples_le h
  roCache_le          := Nat.le_trans hB.roCache_le h
  rootRoCache_le      := Nat.le_trans hB.rootRoCache_le h
  advKeys_le          := Nat.le_trans hB.advKeys_le h
  initKemRecs_le      := Nat.le_trans hB.initKemRecs_le h
  recvKemRecs_le      := Nat.le_trans hB.recvKemRecs_le h
  sentOPKEvents_le    := Nat.le_trans hB.sentOPKEvents_le h
  sentNoOPKEvents_le  := Nat.le_trans hB.sentNoOPKEvents_le h
  idealSessions_le    := Nat.le_trans hB.idealSessions_le h

theorem AuthListsBounded.mono {S : Setup} {n m : Nat} {hst : AuthHybridStateFixed S}
    (h : n ≤ m) (hB : AuthListsBounded n hst) : AuthListsBounded m hst where
  toAuthHybridListsBounded := hB.toAuthHybridListsBounded.mono h
  mkSaltCache_le           := Nat.le_trans hB.mkSaltCache_le h

theorem authListsBounded_empty (S : Setup) (secb : Bool) :
    AuthListsBounded 0 (AuthHybridStateFixed.empty S secb) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [AuthHybridStateFixed.empty, AuthHybridState.empty, AuthState.empty]

/-! ## Finalization Evaluation Lemmas -/

theorem mapMPrim_length_le_take {α β : Type} (f : α → OracleComp PrimBaseSpec β)
    (K : Nat) (xs : List α) :
    HoldsOnLeaves (fun ys => ys.length ≤ K) (AuthSubHops1to3.mapMPrim f (xs.take K)) := by
  suffices ∀ l : List α,
      HoldsOnLeaves (fun ys => ys.length = l.length) (AuthSubHops1to3.mapMPrim f l) by
    exact (this (xs.take K)).mono (fun ys h => by rw [h]; exact List.length_take_le K xs)
  intro l
  induction l with
  | nil => exact HoldsOnLeaves.pure rfl
  | cons x tl ih =>
    exact HoldsOnLeaves.bind_const (f x) (fun y =>
      HoldsOnLeaves.bind ih (fun ys hys =>
        HoldsOnLeaves.pure (by simp [hys])))

private theorem take_min_of_le' {α : Type} {K N : Nat} (l : List α) (hl : l.length ≤ K) :
    l.take (min K N) = l.take N := by
  rw [← List.take_take]
  exact List.take_of_length_le (by simp only [List.length_take]; omega)

private theorem allHonestEcPksAuthPrim_length_le_min (S : Setup) (K : Nat) (st : AuthState S)
    (hP : st.principals.length ≤ K) (hS : st.spkBundles.length ≤ K)
    (hO : st.opkEntries.length ≤ K) (hSe : st.sessions.length ≤ K) :
    HoldsOnLeaves (fun ecPks => ecPks.length ≤ 4 * min K S.N_dh)
      (AuthSubHops1to3.allHonestEcPksAuthPrim S st) := by
  unfold AuthSubHops1to3.allHonestEcPksAuthPrim
  rw [← take_min_of_le' (N := S.N_dh) st.principals hP,
      ← take_min_of_le' (N := S.N_dh) st.spkBundles hS,
      ← take_min_of_le' (N := S.N_dh) st.opkEntries hO,
      ← take_min_of_le' (N := S.N_dh) st.sessions hSe]
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ (min K S.N_dh) st.principals) (fun p1 hp1 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ (min K S.N_dh) st.spkBundles) (fun p2 hp2 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ (min K S.N_dh) st.opkEntries) (fun p3 hp3 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ (min K S.N_dh) st.sessions) (fun p4 hp4 => ?_)
  exact HoldsOnLeaves.pure (by simp only [List.length_append]; omega)

private theorem allHonestEcPksAuthDslK_eval (S : Setup) (K : Nat) {Γ : List PT}
    (st : AuthState S) (env : Env Γ)
    (hP : st.principals.length ≤ K) (hS : st.spkBundles.length ≤ K)
    (hO : st.opkEntries.length ≤ K) (hSe : st.sessions.length ≤ K) :
    (allHonestEcPksAuthDslK S K).eval (.cons (authStateToVal st) env) =
    AuthSubHops1to3.allHonestEcPksAuthPrim S st := by
  simp only [AuthSubHops1to3.allHonestEcPksAuthPrim,
    mapML_eq_mapMPrim, authSubHops1to3_mapMPrim_eq, Comp.eval, Expr.eval, Env.get,
    asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    peIkAPk, sbSpkPk, oeOpkPk, aseEkASk, authStateToVal,
    queryPrim_eval, evalPrimQ, ← List.map_take, mapMPrim_map,
    Prod.map, id_eq, principalEntryToVal, spkBundleEntryToVal,
    opkEntryToVal, authSessionEntryToVal]
  rw [take_min_of_le' (N := S.N_dh) st.principals hP,
      take_min_of_le' (N := S.N_dh) st.spkBundles hS,
      take_min_of_le' (N := S.N_dh) st.opkEntries hO,
      take_min_of_le' (N := S.N_dh) st.sessions hSe]
  have h1 := mapMPrim_length_le_take
    (fun (x : Nat × PrincipalEntry) => primQ (.pow8 x.2.ikAPk)) (min K S.N_dh) st.principals
  have h2 := mapMPrim_length_le_take
    (fun (x : (Nat × Nat) × SpkBundleEntry) => primQ (.pow8 x.2.spkPk)) (min K S.N_dh) st.spkBundles
  have h3 := mapMPrim_length_le_take
    (fun (x : (Nat × Nat × Nat) × OpkEntry) => primQ (.pow8 x.2.opkPk)) (min K S.N_dh) st.opkEntries
  have h4 := mapMPrim_length_le_take
    (fun (s : AuthInitiatorEntry S) => primQ (.x25519Base s.ekASk) >>= fun pk => primQ (.pow8 pk))
    (min K S.N_dh) st.sessions
  rw [take_min_of_le' (N := S.N_dh) st.principals hP] at h1
  rw [take_min_of_le' (N := S.N_dh) st.spkBundles hS] at h2
  rw [take_min_of_le' (N := S.N_dh) st.opkEntries hO] at h3
  rw [take_min_of_le' (N := S.N_dh) st.sessions hSe] at h4
  rw [authSubHops1to3_mapMPrim_eq] at h1 h2 h3 h4
  refine h1.bind_congr _ _ (fun p1 hp1 => ?_)
  refine h2.bind_congr _ _ (fun p2 hp2 => ?_)
  refine h3.bind_congr _ _ (fun p3 hp3 => ?_)
  refine h4.bind_congr _ _ (fun p4 hp4 => ?_)
  have h12 : (p1 ++ p2).length ≤ 4 * min K S.N_dh := by simp [List.length_append]; omega
  have h123 : (p1 ++ p2 ++ p3).length ≤ 4 * min K S.N_dh := by simp [List.length_append]; omega
  have h1234 : (p1 ++ p2 ++ p3 ++ p4).length ≤ 4 * min K S.N_dh := by simp [List.length_append]; omega
  rw [List.take_of_length_le h12, List.take_of_length_le h123, List.take_of_length_le h1234]

theorem allHonestEcPksAuthPrim_length_le (S : Setup) (st : AuthState S) :
    HoldsOnLeaves (fun ecPks => ecPks.length ≤ 4 * S.N_dh)
      (AuthSubHops1to3.allHonestEcPksAuthPrim S st) := by
  unfold AuthSubHops1to3.allHonestEcPksAuthPrim
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ S.N_dh st.principals) (fun p1 hp1 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ S.N_dh st.spkBundles) (fun p2 hp2 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ S.N_dh st.opkEntries) (fun p3 hp3 => ?_)
  refine HoldsOnLeaves.bind (mapMPrim_length_le_take _ S.N_dh st.sessions) (fun p4 hp4 => ?_)
  exact HoldsOnLeaves.pure (by simp only [List.length_append]; omega)

theorem allHonestEcPksAuthDsl_eval (S : Setup) {Γ : List PT}
    (st : AuthState S) (env : Env Γ) :
    (allHonestEcPksAuthDsl S).eval (.cons (authStateToVal st) env) =
    AuthSubHops1to3.allHonestEcPksAuthPrim S st := by
  simp only [allHonestEcPksAuthDsl, AuthSubHops1to3.allHonestEcPksAuthPrim,
    mapML_eq_mapMPrim, authSubHops1to3_mapMPrim_eq, Comp.eval, Expr.eval, Env.get,
    asPrincipals, asSpkBundles, asOpkEntries, asSessions,
    peIkAPk, sbSpkPk, oeOpkPk, aseEkASk, authStateToVal,
    queryPrim_eval, evalPrimQ, ← List.map_take, mapMPrim_map,
    Prod.map, id_eq, principalEntryToVal, spkBundleEntryToVal,
    opkEntryToVal, authSessionEntryToVal]
  have h1 := mapMPrim_length_le_take
    (fun (x : Nat × PrincipalEntry) => primQ (.pow8 x.2.ikAPk)) S.N_dh st.principals
  have h2 := mapMPrim_length_le_take
    (fun (x : (Nat × Nat) × SpkBundleEntry) => primQ (.pow8 x.2.spkPk)) S.N_dh st.spkBundles
  have h3 := mapMPrim_length_le_take
    (fun (x : (Nat × Nat × Nat) × OpkEntry) => primQ (.pow8 x.2.opkPk)) S.N_dh st.opkEntries
  have h4 := mapMPrim_length_le_take
    (fun (s : AuthInitiatorEntry S) => primQ (.x25519Base s.ekASk) >>= fun pk => primQ (.pow8 pk))
    S.N_dh st.sessions
  rw [authSubHops1to3_mapMPrim_eq] at h1 h2 h3 h4
  refine h1.bind_congr _ _ (fun p1 hp1 => ?_)
  refine h2.bind_congr _ _ (fun p2 hp2 => ?_)
  refine h3.bind_congr _ _ (fun p3 hp3 => ?_)
  refine h4.bind_congr _ _ (fun p4 hp4 => ?_)
  have h12 : (p1 ++ p2).length ≤ 4 * S.N_dh := by simp [List.length_append]; omega
  have h123 : (p1 ++ p2 ++ p3).length ≤ 4 * S.N_dh := by simp [List.length_append]; omega
  have h1234 : (p1 ++ p2 ++ p3 ++ p4).length ≤ 4 * S.N_dh := by simp [List.length_append]; omega
  rw [List.take_of_length_le h12, List.take_of_length_le h123, List.take_of_length_le h1234]

private theorem foldr_hasDuplicateBytes_aux (K : Nat) (l : List Bytes) (hLen : l.length ≤ K) :
    l.foldr (fun x (acc : Bool × List Bytes) =>
      ((acc.2.take K).any (fun y => x == y) || acc.1, x :: acc.2)) (false, []) =
    (hasDuplicateBytes l, l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hxs : xs.length ≤ K := by simp at hLen; omega
    rw [List.foldr_cons, ih hxs]
    simp only [List.take_of_length_le hxs, hasDuplicateBytes, list_any_beq_eq_contains]

theorem hasDuplicateBytesDsl_eval (w : ℕ+) (K : Nat) {Γ : List PT}
    (xs : Expr pqxdhOps Γ (.list (B w))) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K) :
    (hasDuplicateBytesDsl w K xs).eval env = hasDuplicateBytes (xs.eval env) := by
  simp only [hasDuplicateBytesDsl, boolOr_eval, bytesBeq_eval, Expr.eval, Env.get,
    List.take_of_length_le hLen, foldr_hasDuplicateBytes_aux K (xs.eval env) hLen]

theorem hasBadSigAuthDsl_eval (K : Nat) {S : Setup} {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) (env : Env Γ) (finalSt : AuthHybridState S)
    (hHst : hst.eval env = authHybridStateToVal finalSt)
    (hSess : finalSt.base.sessions.length ≤ K) :
    (hasBadSigAuthDsl K hst).eval env = hasBadSigAuth finalSt := by
  have hTake : (finalSt.base.sessions.map authSessionEntryToVal).take K =
      finalSt.base.sessions.map authSessionEntryToVal := by
    apply List.take_of_length_le; simpa using hSess
  simp only [hasBadSigAuthDsl, hasBadSigAuth, HasAuthState.toAuthState,
    boolOr_eval, Expr.eval, Env.get, ahsBase, asSessions, aseFresh, aseSpkHonest, asePqspkHonest,
    hHst, authHybridStateToVal, authStateToVal, hTake, List.any_map,
    Function.comp_def, authSessionEntryToVal]

theorem hasKemPkCollisionAuthDsl_eval (K : Nat) {S : Setup} {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) (env : Env Γ) (finalSt : AuthHybridState S)
    (hHst : hst.eval env = authHybridStateToVal finalSt)
    (hSpk : finalSt.base.spkBundles.length ≤ K) :
    (hasKemPkCollisionAuthDsl K hst).eval env = hasKemPkCollisionAuth finalSt := by
  have hTake : (finalSt.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      finalSt.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hSpk
  have hMapEq :
      ((Expr.mapB K (asSpkBundles (ahsBase hst)) (sbPqspkPk (.snd (.var .zero)))).eval env) =
      allHonestKemPksAuth finalSt := by
    simp only [allHonestKemPksAuth, HasAuthState.toAuthState, Expr.eval, Env.get,
      ahsBase, asSpkBundles, sbPqspkPk, hHst, authHybridStateToVal, authStateToVal,
      hTake, List.map_map, Function.comp_def, Prod.map, id_eq, spkBundleEntryToVal]
  rw [hasKemPkCollisionAuthDsl, hasDuplicateBytesDsl_eval 1568 K _ env
      (by rw [hMapEq]; simpa [allHonestKemPksAuth, HasAuthState.toAuthState] using hSpk),
      hMapEq, hasKemPkCollisionAuth]

theorem hasBadKemShCrRecordsDsl_eval (K : Nat) {S : Setup} {Γ : List PT}
    (hst : Expr pqxdhOps Γ authHybridStateTy) (env : Env Γ) (finalSt : AuthHybridState S)
    (hHst : hst.eval env = authHybridStateToVal finalSt)
    (hInit : finalSt.initKemRecs.length ≤ K)
    (hRecv : finalSt.recvKemRecs.length ≤ K) :
    (hasBadKemShCrRecordsDsl K hst).eval env =
      AuthSubHops1to3.hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs := by
  have hTakeI : (finalSt.initKemRecs.map initKemRecordToVal).take K =
      finalSt.initKemRecs.map initKemRecordToVal := by
    apply List.take_of_length_le; simpa using hInit
  have hTakeR : (finalSt.recvKemRecs.map recvKemRecordToVal).take K =
      finalSt.recvKemRecs.map recvKemRecordToVal := by
    apply List.take_of_length_le; simpa using hRecv
  simp only [hasBadKemShCrRecordsDsl, AuthSubHops1to3.hasBadKemShCrRecordsPure,
    eLet, eAny, v, Ext.step_wk, Ext.refl_wk, boolOr_eval, bytesBeq_eval,
    Expr.eval, Env.get, ahsInitKemRecs, ahsRecvKemRecs,
    rkrKemSs, ikrKemSs, rkrKemCt, ikrKemCt, ikrPqspkPk, rkrPqspkPk,
    hHst, authHybridStateToVal, hTakeI, hTakeR, List.any_map,
    Function.comp_def, initKemRecordToVal, recvKemRecordToVal, bne]

theorem notAllChallengedCleanDsl_eval (K : Nat) {S : Setup} {Γ : List PT}
    (st : Expr pqxdhOps Γ authStateTy) (env : Env Γ) (baseSt : AuthState S)
    (hSt : st.eval env = authStateToVal baseSt)
    (hSess : baseSt.sessions.length ≤ K) :
    (notAllChallengedCleanDsl K st).eval env =
      !AuthSubHops1to3.allChallengedCleanPure baseSt := by
  have hTake : (baseSt.sessions.map authSessionEntryToVal).take K =
      baseSt.sessions.map authSessionEntryToVal := by
    apply List.take_of_length_le; simpa using hSess
  simp only [notAllChallengedCleanDsl, AuthSubHops1to3.allChallengedCleanPure,
    List.all_eq_not_any_not, boolOr_eval, Expr.eval, Env.get,
    asSessions, aseChallenged, aseFresh, asePqspkHonest,
    hSt, authStateToVal, hTake, List.any_map, Function.comp_def, authSessionEntryToVal]

theorem finalizeAuthFixedDsl_eval (S : Setup) (K : Nat) {Γ : List PT}
    (secb b' : Bool) (finalSt : AuthHybridState S) (env : Env Γ)
    (hB : AuthHybridListsBounded K finalSt) :
    (finalizeAuthFixedDsl S K).eval
      (.cons (authHybridStateToVal finalSt) (.cons b' (.cons secb env))) =
    finalizeAuthFixedPrim S secb b' finalSt := by
  let env0 : Env (authStateTy :: authHybridStateTy :: .bool :: .bool :: Γ) :=
    .cons (authStateToVal finalSt.base)
      (.cons (authHybridStateToVal finalSt) (.cons b' (.cons secb env)))
  have hBody : ∀ ecPks : List Bytes, ecPks.length ≤ 4 * min K S.N_dh →
      ((finalizeAuthFixedBodyDsl S K).eval (@Env.cons _ _ (.list (B 32)) ecPks env0) :
        OracleComp PrimBaseSpec Bool) =
      (if (hasDuplicateBytes ecPks || hasBadSigAuth finalSt || hasKemPkCollisionAuth finalSt ||
            AuthSubHops1to3.hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs) =
            true then
          embedUnif ($ᵗ Bool)
        else if finalSt.base.hasWonAuth = true then pure true
        else if (!AuthSubHops1to3.allChallengedCleanPure finalSt.base) = true then
          embedUnif ($ᵗ Bool)
        else pure (b' == secb)) := by
    intro ecPks hEcLen
    let env1 : Env (.list (B 32) :: authStateTy :: authHybridStateTy :: .bool :: .bool :: Γ) :=
      .cons ecPks env0
    have hDup := hasDuplicateBytesDsl_eval 32 (4 * min K S.N_dh) (.var .zero) env1 hEcLen
    simp only [env1, Expr.eval, Env.get_zero] at hDup
    have hSig := hasBadSigAuthDsl_eval K (.var (.succ (.succ .zero))) env1 finalSt
      rfl hB.sessions_le
    have hKem := hasKemPkCollisionAuthDsl_eval K (.var (.succ (.succ .zero))) env1 finalSt
      rfl hB.spkBundles_le
    have hShCr := hasBadKemShCrRecordsDsl_eval K (.var (.succ (.succ .zero))) env1 finalSt rfl
      hB.initKemRecs_le hB.recvKemRecs_le
    have hClean := notAllChallengedCleanDsl_eval K (.var (.succ .zero)) env1 finalSt.base
      rfl hB.sessions_le
    have hCond :
        (boolOr
          (boolOr
            (boolOr
              (hasDuplicateBytesDsl 32 (4 * min K S.N_dh) (.var .zero))
              (hasBadSigAuthDsl K (.var (.succ (.succ .zero)))))
            (hasKemPkCollisionAuthDsl K (.var (.succ (.succ .zero)))))
          (hasBadKemShCrRecordsDsl K (.var (.succ (.succ .zero))))).eval env1 =
        (hasDuplicateBytes ecPks || hasBadSigAuth finalSt || hasKemPkCollisionAuth finalSt ||
          AuthSubHops1to3.hasBadKemShCrRecordsPure finalSt.initKemRecs finalSt.recvKemRecs) := by
      simp only [boolOr_eval]
      rw [hDup, hSig, hKem, hShCr]
    simp only [finalizeAuthFixedBodyDsl, Comp.eval, samplePrim_bool_eval, boolBeq_eval]
    rw [hCond, hClean]
    rfl
  have hLhs :
      ((finalizeAuthFixedDsl S K).eval
        (.cons (authHybridStateToVal finalSt) (.cons b' (.cons secb env))) :
        OracleComp PrimBaseSpec Bool) =
      (AuthSubHops1to3.allHonestEcPksAuthPrim S finalSt.base >>= fun ecPks : List Bytes =>
        ((finalizeAuthFixedBodyDsl S K).eval (@Env.cons _ _ (.list (B 32)) ecPks env0) :
          OracleComp PrimBaseSpec Bool)) := by
    have hBaseEq :
        (ahsBase (.var .zero) :
          Expr pqxdhOps (authHybridStateTy :: .bool :: .bool :: Γ) authStateTy).eval
          (.cons (authHybridStateToVal finalSt) (.cons b' (.cons secb env))) =
        authStateToVal finalSt.base := rfl
    unfold finalizeAuthFixedDsl
    rw [eval_letC, hBaseEq, Comp.eval,
      allHonestEcPksAuthDslK_eval S K finalSt.base _
        hB.principals_le hB.spkBundles_le hB.opkEntries_le hB.sessions_le]
  rw [hLhs]
  unfold finalizeAuthFixedPrim
  exact (allHonestEcPksAuthPrim_length_le_min S K finalSt.base
    hB.principals_le hB.spkBundles_le hB.opkEntries_le hB.sessions_le).bind_congr _ _ hBody

/-! ## Shared Helper Evaluation Lemmas -/

section SharedHelperEval

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List PT}

theorem take_min_of_le {α : Type} {K N : Nat} (l : List α) (hl : l.length ≤ K) :
    l.take (min K N) = l.take N := by
  rw [← List.take_take]
  exact List.take_of_length_le (by simp only [List.length_take]; omega)

theorem take_min_map_of_le {α β : Type} {K N : Nat} (f : α → β) (l : List α)
    (hl : l.length ≤ K) : (l.map f).take (min K N) = (l.map f).take N :=
  take_min_of_le _ (by simpa using hl)

variable {K} in
theorem findHonestC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hPrin : s.principals.length ≤ K) :
    (findHonestC S K st ik).eval env =
      Option.map (Prod.map id principalEntryToVal) <$>
        findHonestPrincipalPrim S s.principals (ik.eval env) := by
  simp only [findHonestC, letV, findMV, bindV, v, asPrincipals, peIkAPk,
    eval_letC, findML_eq_findMPrim, queryPrim_eval, evalPrimQ, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, take_min_map_of_le _ _ hPrin, ← List.map_take, findMPrim_map]
  rfl

theorem isAdvRegC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hAdv : s.advKeys.length ≤ K) :
    (isAdvRegC K st pk).eval env = isAdvRegisteredPrim s.advKeys (pk.eval env) := by
  simp only [isAdvRegC, bindV, eAny, v, asAdvKeys, queryPrim_eval, evalPrimQ, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, List.take_of_length_le hAdv, isAdvRegisteredPrim]

variable {K} in
theorem isGameSpkC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hSpk : s.spkBundles.length ≤ K) :
    (isGameSpkC S K st pk).eval env = isGameSpkPrim S s.spkBundles (pk.eval env) := by
  simp only [isGameSpkC, letV, anyMV, bindV, v, asSpkBundles, sbSpkPk,
    eval_letC, anyML_eq_anyMPrim, queryPrim_eval, evalPrimQ, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, take_min_map_of_le _ _ hSpk, ← List.map_take, anyMPrim_map]
  rfl

variable {K} in
theorem isGameOpkC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hOpk : s.opkEntries.length ≤ K) :
    (isGameOpkC S K st pk).eval env = isGameOpkPrim S s.opkEntries (pk.eval env) := by
  simp only [isGameOpkC, letV, anyMV, bindV, v, asOpkEntries, oeOpkPk,
    eval_letC, anyML_eq_anyMPrim, queryPrim_eval, evalPrimQ, bytesBeq_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, take_min_map_of_le _ _ hOpk, ← List.map_take, anyMPrim_map]
  rfl

theorem koskSenderOkC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hAdv : s.advKeys.length ≤ K) (hPrin : s.principals.length ≤ K) :
    (koskSenderOkC S K st ik).eval env =
      koskSenderOkPrim S s.principals s.advKeys (ik.eval env) := by
  simp only [koskSenderOkC, letV, bindV, eval_letC, Comp.eval]
  rw [findHonestC_eval S st _ (.cons (ik.eval env) env) s (by simp [hst]) hPrin]
  simp only [v, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_zero,
    map_eq_bind_pure_comp, bind_assoc]
  unfold koskSenderOkPrim isGameIdKeyPrim
  simp only [bind_assoc, pure_bind]
  refine congrArg (fun k => findHonestPrincipalPrim S s.principals (ik.eval env) >>= k)
    (funext fun hp => ?_)
  simp only [Function.comp_apply, pure_bind]
  rw [isAdvRegC_eval S K st _ _ s (by simp [hst]) hAdv]
  simp only [boolOr_eval, isSomeE_eval, Expr.eval, Env.get_succ, Env.get_zero]
  cases hp <;> rfl

theorem koskBundleOkC_eval (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (s : AuthState S) (bundle : PreKeyBundleInput)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hbu : Env.get env (h₂.wk bu) = preKeyBundleToVal bundle)
    (hAdv : s.advKeys.length ≤ K) (hPrin : s.principals.length ≤ K)
    (hSpk : s.spkBundles.length ≤ K) (hOpk : s.opkEntries.length ≤ K) :
    (koskBundleOkC S K st bu).eval env =
      koskBundleOkPrim S s.principals s.spkBundles s.opkEntries s.advKeys bundle := by
  simp only [koskBundleOkC, bindV, caseOptV, Comp.eval]
  rw [findHonestC_eval S st _ env s hst hPrin]
  simp only [pkbIkB, v, Expr.eval, Ext.step_wk, Ext.refl_wk, hbu, preKeyBundleToVal, bundleV,
    map_eq_bind_pure_comp, bind_assoc]
  unfold koskBundleOkPrim isGameIdKeyPrim
  simp only [bind_assoc, pure_bind]
  refine congrArg (fun k => findHonestPrincipalPrim S s.principals bundle.ikB >>= k)
    (funext fun hp => ?_)
  simp only [Function.comp_apply, pure_bind]
  rw [isAdvRegC_eval S K st _ _ s (by simp [hst]) hAdv]
  simp only [Expr.eval, Env.get_succ, hbu, preKeyBundleToVal, bundleV]
  refine congrArg (fun k => isAdvRegisteredPrim s.advKeys bundle.ikB >>= k)
    (funext fun idA => ?_)
  rw [isGameSpkC_eval S st _ _ s (by simp [hst]) hSpk]
  simp only [pkbSpkB, Expr.eval, Env.get_succ, hbu, preKeyBundleToVal, bundleV]
  refine congrArg (fun k => isGameSpkPrim S s.spkBundles bundle.spkB >>= k)
    (funext fun gSpk => ?_)
  rw [isAdvRegC_eval S K st _ _ s (by simp [hst]) hAdv]
  simp only [Expr.eval, Env.get_succ, hbu, preKeyBundleToVal, bundleV]
  refine congrArg (fun k => isAdvRegisteredPrim s.advKeys bundle.spkB >>= k)
    (funext fun spkA => ?_)
  simp only [pkbOpkB?, Expr.eval, Env.get_succ, hbu, preKeyBundleToVal, bundleV]
  cases bundle.opkB? with
  | none =>
    cases hp <;> simp [boolOr_eval, isSomeE_eval, Expr.eval]
  | some opkP =>
    rcases opkP with ⟨opkId, opkPk⟩
    simp only [Option.map]
    rw [isGameOpkC_eval S st _ _ s (by simp [hst]) hOpk]
    simp only [Expr.eval, Env.get_zero]
    refine congrArg (fun k => isGameOpkPrim S s.opkEntries opkPk >>= k)
      (funext fun gOpk => ?_)
    rw [isAdvRegC_eval S K st _ _ s (by simp [hst]) hAdv]
    simp only [boolOr_eval, isSomeE_eval, Expr.eval, Env.get_succ, Env.get_zero]
    refine congrArg (fun k => isAdvRegisteredPrim s.advKeys opkPk >>= k)
      (funext fun opkA => ?_)
    cases hp <;> rfl

variable {K} in
theorem resolveSigPkC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hPrin : s.principals.length ≤ K) :
    (resolveSigPkC S K st ik).eval env = resolveSigPkPrim S s.principals (ik.eval env) := by
  simp only [resolveSigPkC, letV, bindV, eCaseOpt, eval_letC, Comp.eval]
  rw [findHonestC_eval S st _ (.cons (ik.eval env) env) s (by simp [hst]) hPrin]
  simp only [v, peIkSignPk, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    map_eq_bind_pure_comp, bind_assoc]
  unfold resolveSigPkPrim
  refine congrArg (fun k => findHonestPrincipalPrim S s.principals (ik.eval env) >>= k)
    (funext fun hp => ?_)
  cases hp <;> rfl

theorem hkdfRoC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (sec : Expr pqxdhOps Δ (B 192))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hRo : s.roCache.length ≤ K) :
    (hkdfRoC K st sec).eval env =
      Prod.map drKeyToVal (List.map (Prod.map id drKeyToVal)) <$>
        embedUnif (AuthSubHops1to3.evalHkdfRoPure s.roCache (sec.eval env)) := by
  have hTake : (s.roCache.map (Prod.map id drKeyToVal)).take K =
      s.roCache.map (Prod.map id drKeyToVal) := by
    apply List.take_of_length_le; simpa using hRo
  simp only [hkdfRoC, letV, caseOptV, bindV, eFind, v, asRoCache,
    eval_letC, bytesBeq_eval, samplePrim_drKey96_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, hTake, List.find?_map]
  unfold AuthSubHops1to3.evalHkdfRoPure
  have hPred :
      ((fun x : Bytes × drKeyTy.denote => x.1 == sec.eval env) ∘ Prod.map id drKeyToVal) =
      (fun (k, _) => k == sec.eval env) := rfl
  rw [hPred]
  cases s.roCache.find? (fun (k, _) => k == sec.eval env) with
  | none =>
    simp [embedUnif, liftComp, map_eq_bind_pure_comp, bind_assoc]
  | some p =>
    rcases p with ⟨k, dk⟩
    simp [embedUnif, liftComp]

theorem rootRoC_eval (st : Var Γ authStateTy) [h : Ext Γ Δ] (rk dh : Expr pqxdhOps Δ (B 32))
    (env : Env Δ) (s : AuthState S) (hst : Env.get env (h.wk st) = authStateToVal s)
    (hRoot : s.rootRoCache.length ≤ K) :
    (rootRoC K st rk dh).eval env =
      embedUnif (AuthSubHops1to3.evalRootKdfRoPure s.rootRoCache (rk.eval env) (dh.eval env)) := by
  simp only [rootRoC, letV, caseOptV, bindV, eFind, bytes2Eq, v, asRootRoCache,
    eval_letC, bytesBeq_eval, samplePrim_bytes32_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hst, authStateToVal, List.take_of_length_le hRoot]
  unfold AuthSubHops1to3.evalRootKdfRoPure
  have hPred : (fun x : (Bytes × Bytes) × (Bytes × Bytes) =>
      x.1.1 == rk.eval env && x.1.2 == dh.eval env) =
      (fun (k, _) => k == (rk.eval env, dh.eval env)) := funext fun ⟨⟨_, _⟩, _⟩ => rfl
  rw [hPred]
  cases s.rootRoCache.find? (fun (k, _) => k == (rk.eval env, dh.eval env)) with
  | none =>
    simp [embedUnif, liftComp, map_eq_bind_pure_comp]
  | some p =>
    rcases p with ⟨k, out⟩
    simp [embedUnif, liftComp]

theorem checkBundleProvenanceExactC_eval (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (s : AuthState S) (bundle : PreKeyBundleInput)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hbu : Env.get env (h₂.wk bu) = preKeyBundleToVal bundle)
    (hSpk : s.spkBundles.length ≤ K) (hPrin : s.principals.length ≤ K)
    (hOpk : s.opkEntries.length ≤ K) :
    (checkBundleProvenanceExactC S K st bu).eval env =
      checkBundleProvenanceExactPrim S s.principals s.spkBundles s.opkEntries bundle := by
  have hTakeSpk : (s.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      s.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hSpk
  simp only [checkBundleProvenanceExactC, bindV, caseOptV, letV, eAny, anyMV, eval_letC, Comp.eval]
  rw [findHonestC_eval S st _ env s hst hPrin]
  simp only [pkbIkB, v, Expr.eval, Ext.step_wk, Ext.refl_wk, hbu, preKeyBundleToVal, bundleV,
    map_eq_bind_pure_comp, bind_assoc]
  unfold checkBundleProvenanceExactPrim
  refine congrArg (fun k => findHonestPrincipalPrim S s.principals bundle.ikB >>= k)
    (funext fun opt => ?_)
  cases opt with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    simp only [Function.comp_apply, Option.map, Prod.map, id_eq, Expr.eval,
      Env.get_succ, Env.get_zero,
      asSpkBundles, asOpkEntries, sbSpkPk, sbPqspkPk, oeOpkPk,
      pkbSpkB, pkbPqspkB, pkbOpkB?, natEq_eval, bytesBeq_eval,
      hst, hbu, authStateToVal, preKeyBundleToVal, bundleV, hTakeSpk,
      List.any_map, Function.comp_def, spkBundleEntryToVal, pure_bind]
    cases bundle.opkB? with
    | none => simp []
    | some opkP =>
      rcases opkP with ⟨opkId, opkPk⟩
      simp only [anyML_eq_anyMPrim, queryPrim_eval, evalPrimQ, take_min_map_of_le _ _ hOpk,
        ← List.map_take, anyMPrim_map]
      rfl

variable {K} in
theorem checkBundleSpkHonIdealC_eval (st : Var Γ₁ authStateTy) (bu : Var Γ₂ preKeyBundleTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (s : AuthState S) (bundle : PreKeyBundleInput)
    (hst : Env.get env (h₁.wk st) = authStateToVal s)
    (hbu : Env.get env (h₂.wk bu) = preKeyBundleToVal bundle)
    (hPrin : s.principals.length ≤ K) (hSpk : s.spkBundles.length ≤ K) :
    (checkBundleSpkHonIdealC S K st bu).eval env =
      checkBundleSpkHonIdealPrim S s.principals s.spkBundles bundle := by
  simp only [checkBundleSpkHonIdealC, bindV, caseOptV, letV, anyMV, eval_letC, Comp.eval]
  rw [findHonestC_eval S st _ env s hst hPrin]
  simp only [pkbIkB, v, Expr.eval, Ext.step_wk, Ext.refl_wk, hbu, preKeyBundleToVal, bundleV,
    map_eq_bind_pure_comp, bind_assoc]
  unfold checkBundleSpkHonIdealPrim
  refine congrArg (fun k => findHonestPrincipalPrim S s.principals bundle.ikB >>= k)
    (funext fun opt => ?_)
  cases opt with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, pEntry⟩
    simp only [Function.comp_apply, Option.map, Prod.map, id_eq, Expr.eval,
      Env.get_succ, Env.get_zero,
      asSpkBundles, sbSpkPk, pkbSpkB, peCorrupted, natEq_eval, boolOr_eval, bytesBeq_eval,
      hst, hbu, authStateToVal, preKeyBundleToVal, bundleV,
      principalEntryToVal, spkBundleEntryToVal, anyML_eq_anyMPrim, queryPrim_eval, evalPrimQ,
      take_min_map_of_le _ _ hSpk, ← List.map_take, anyMPrim_map, pure_bind]

theorem matchSentOPKC_eval (r : Var Γ₁ recvdOPKEventTy) (s : Var Γ₂ sentOPKEventTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (rv : RecvdOPKEvent) (sv : SentOPKEvent)
    (hr : Env.get env (h₁.wk r) = recvdOPKEventToVal rv)
    (hs : Env.get env (h₂.wk s) = sentOPKEventToVal sv) :
    (matchSentOPKC r s).eval env = matchSentOPKPrim rv sv := by
  simp only [matchSentOPKC, bindV, v, roBCorr, roA0, roB0, roSb, roOb, roA1, roPk1, roCt, roM,
    soA0, soB0, soSb, soOb, soA1, soPk1, soCt, soM, soMatched,
    Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ, boolOr_eval, bytesBeq_eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hr, hs, recvdOPKEventToVal, sentOPKEventToVal, matchSentOPKPrim]

theorem matchSentNoOPKC_eval (r : Var Γ₁ recvdNoOPKEventTy) (s : Var Γ₂ sentNoOPKEventTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ) (rv : RecvdNoOPKEvent) (sv : SentNoOPKEvent)
    (hr : Env.get env (h₁.wk r) = recvdNoOPKEventToVal rv)
    (hs : Env.get env (h₂.wk s) = sentNoOPKEventToVal sv) :
    (matchSentNoOPKC r s).eval env = matchSentNoOPKPrim rv sv := by
  simp only [matchSentNoOPKC, bindV, v, rnoBCorr, rnoA0, rnoB0, rnoSb, rnoA1, rnoPk1, rnoCt, rnoM,
    snoA0, snoB0, snoSb, snoA1, snoPk1, snoCt, snoM, snoMatched,
    Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ, boolOr_eval, bytesBeq_eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hr, hs, recvdNoOPKEventToVal, sentNoOPKEventToVal, matchSentNoOPKPrim]

theorem matchIdealAuthHandshakeC_eval
    (ikB : Var Γ₁ (B 32)) (spkB : Var Γ₂ (B 32)) (opkB? : Var Γ₃ (.opt (B 32)))
    (pqspkB : Var Γ₄ (B 1568)) (hdr : Var Γ₅ handshakeHdrTy) (s : Var Γ₆ idealAuthSessionTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] [h₃ : Ext Γ₃ Δ]
    [h₄ : Ext Γ₄ Δ] [h₅ : Ext Γ₅ Δ] [h₆ : Ext Γ₆ Δ]
    (env : Env Δ) (ikBv spkBv : Bytes) (opkBv? : Option Bytes) (pqspkBv : Bytes)
    (hdrv : HandshakeHdr) (sv : IdealAuthSession S)
    (h1 : Env.get env (h₁.wk ikB) = ikBv) (h2 : Env.get env (h₂.wk spkB) = spkBv)
    (h3 : Env.get env (h₃.wk opkB?) = opkBv?) (h4 : Env.get env (h₄.wk pqspkB) = pqspkBv)
    (h5 : Env.get env (h₅.wk hdr) = handshakeHdrToVal hdrv)
    (h6 : Env.get env (h₆.wk s) = idealAuthSessionToVal sv) :
    (matchIdealAuthHandshakeC ikB spkB opkB? pqspkB hdr s).eval env =
      matchIdealAuthHandshakePrim ikBv spkBv opkBv? pqspkBv hdrv sv := by
  simp only [matchIdealAuthHandshakeC, bindV, caseOptV, v,
    hdrIkAPk, hdrEkAPk, hdrKemCt, iasIkAPk, iasPeerIkPk, iasPeerSpkPk, iasPeerOpkPk?,
    iasEkAPk, iasPeerPqspkPk, iasKemCt,
    Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ, bytesBeq_eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    h1, h2, h3, h4, h5, h6,
    handshakeHdrToVal, hdrV, idealAuthSessionToVal, matchIdealAuthHandshakePrim, sameOpkPkPrim]
  cases opkBv? <;> cases sv.peerOpkPk? <;> simp

theorem initPrinFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (uv : Fin S.N_id)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hu : Env.get env (h₂.wk u) = uv.val)
    (hB : AuthListsBounded K s) :
    (initPrinFixedB K fhst u).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.initPrin uv) s := by
  have hTakeP :
      (s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal)).take K =
      s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  simp only [initPrinFixedB, letV, bindV, eAny, v, ahsBase, ahsfHybrid,
    asHasWonAuth, asPrincipals, aNone, aInitPrin, fhstSetBase, ahsfUpd,
    ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, stUpd, stMk, asSecb, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, peMk, natEq_eval, eval_letC,
    samplePrim_bytes32_eval, queryPrim_eval, evalPrimQ,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hu, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    hTakeP, List.any_map, Function.comp_def, Prod.map, id_eq,
    AuthSubHops1to3.stepAuthOtherPrim, sampleScalar32,
    map_eq_bind_pure_comp]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    cases hAny : s.toAuthHybridState.base.principals.any (fun x => x.1 == uv.val) <;>
      simp [hWon, authRespToVal, authRenc]

private theorem map_corrupt_principals (ps : List (Nat × PrincipalEntry)) (u : Nat) :
    (ps.map (Prod.map id principalEntryToVal)).map
      (fun (x : (Ty.prod .nat principalEntryTy).denote) =>
        if (x.1 == u) = true then (x.1, (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2.1, true)))))
        else x) =
    (ps.map (fun (idx, e) =>
      if idx == u then (idx, { e with corrupted := true }) else (idx, e))).map
      (Prod.map id principalEntryToVal) := by
  rw [List.map_map, List.map_map]
  congr 1; funext ⟨idx, e⟩
  by_cases h : idx = u <;> simp [h, principalEntryToVal, Prod.map]

theorem corruptFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (u : Var Γ₂ .nat)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (uv : Fin S.N_id)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hu : Env.get env (h₂.wk u) = uv.val)
    (hB : AuthListsBounded K s) :
    (corruptFixedB K fhst u).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.corruptIK uv) s := by
  have hTakeP :
      (s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal)).take K =
      s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  simp only [corruptFixedB, letV, caseOptV, eFind, eMap, v, ahsBase, ahsfHybrid,
    asHasWonAuth, asPrincipals, aNone, aCorr, fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, stUpd, stMk, asSecb, asSpkBundles, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, peUpd, peMk, peSecIKA0, peIkAPk,
    peSecIKAsign, peIkSignPk, natEq_eval, eval_letC,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hu, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    hTakeP, List.find?_map, Function.comp_def,
    AuthSubHops1to3.stepAuthOtherPrim]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    cases hFind : s.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == uv.val) with
    | none => simp [hWon, hFind, authRespToVal, authRenc]
    | some p =>
      rcases p with ⟨idx, entry⟩
      simp only [hFind, Bool.false_eq_true, ↓reduceIte, Option.map_some, Prod.map, id_eq,
        principalEntryToVal, authRespToVal, authRenc, map_pure,
        authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
        authHybridStateToVal, authStateToVal]
      rw [map_corrupt_principals]

theorem genSpkFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ (.prod .nat .nat))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (uv : Fin S.N_id) (jv : Fin S.N_recv)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₂.wk x) = (uv.val, jv.val))
    (hB : AuthListsBounded K s) :
    (genSpkFixedB K fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.genSPK uv jv) s := by
  have hTakeP :
      (s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal)).take K =
      s.toAuthHybridState.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  have hTakeS :
      (s.toAuthHybridState.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      s.toAuthHybridState.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.spkBundles_le
  simp only [genSpkFixedB, letV, bindV, caseOptV, eAny, eFind, v, ahsBase, ahsfHybrid,
    asHasWonAuth, asPrincipals, asSpkBundles, aNone, aBundle, fhstSetBase, ahsfUpd,
    ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, stUpd, stMk, asSecb, asOpkEntries, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, buMk, sbMk, peSecIKAsign, peIkAPk,
    encEC_eval, encKEM_eval, nat2Eq_eval, natEq_eval, eval_letC, u32OfNat_eval,
    samplePrim_bytes32_eval, samplePrim_random64_eval,
    queryPrim_eval, evalPrimQ,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hx, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    hTakeP, hTakeS, List.any_map, List.find?_map, Function.comp_def, Prod.map, id_eq,
    AuthSubHops1to3.stepAuthOtherPrim, sampleScalar32, sampleKemKeyGenPrim,
    map_eq_bind_pure_comp, bind_assoc]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    cases hAny :
        s.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (uv.val, jv.val)) with
    | true => simp [hWon, authRespToVal, authRenc]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hFind :
          s.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == uv.val) with
      | none => simp [hWon, authRespToVal, authRenc]
      | some p =>
        rcases p with ⟨idx, uEntry⟩
        simp [principalEntryToVal, spkBundleEntryToVal, bundleV,
          authRespToVal, authRenc]

theorem genOpkFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (uv : Fin S.N_id) (jv : Fin S.N_recv) (ov : Fin S.N_opk)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₂.wk x) = (uv.val, (jv.val, ov.val)))
    (hB : AuthListsBounded K s) :
    (genOpkFixedB K fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.genOPK uv jv ov) s := by
  have hTakeO : (s.toAuthHybridState.base.opkEntries.map
      (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal)).take K =
      s.toAuthHybridState.base.opkEntries.map
      (Prod.map (fun (u, j, o) => (u, (j, o))) opkEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.opkEntries_le
  simp only [genOpkFixedB, letV, bindV, eAny, v, ahsBase, ahsfHybrid,
    asHasWonAuth, asOpkEntries, aNone, aPk, fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache, ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs,
    ahsIdealSessions, stUpd, stMk, asSecb, asPrincipals, asSpkBundles, asSessions,
    asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, oeMk, nat3Eq_eval, eval_letC,
    samplePrim_bytes32_eval, queryPrim_eval, evalPrimQ,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hx, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    hTakeO, List.any_map, Function.comp_def, Prod.map,
    AuthSubHops1to3.stepAuthOtherPrim, sampleScalar32,
    map_eq_bind_pure_comp]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    have hAnyEq :
        (s.toAuthHybridState.base.opkEntries.any fun x =>
          ((x.1.1, x.1.2.1, x.1.2.2) == (uv.val, jv.val, ov.val))) =
        (s.toAuthHybridState.base.opkEntries.any fun (k, _) => k == (uv.val, jv.val, ov.val)) :=
      rfl
    rw [hAnyEq]
    cases hAny :
        s.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (uv.val, jv.val, ov.val)) <;>
      simp [hWon, authRespToVal, authRenc]

theorem roFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (sec : Var Γ₂ (B 192))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (secv : Bytes)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hsec : Env.get env (h₂.wk sec) = secv)
    (hB : AuthListsBounded K s) :
    (roFixedB K fhst sec).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.roQuery secv) s := by
  simp only [roFixedB, letV, bindV, eval_letC, Comp.eval, Expr.eval, v, ahsBase, ahsfHybrid,
    asHasWonAuth, aNone, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal,
    AuthSubHops1to3.stepAuthOtherPrim]
  have hWonEq : (authStateToVal s.toAuthHybridState.base).2.1 =
      s.toAuthHybridState.base.hasWonAuth := rfl
  rw [hWonEq]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true =>
    simp [hWon, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authRespToVal, authRenc]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hkdfRoC_eval S K _ _ _ s.toAuthHybridState.base rfl hB.roCache_le]
    simp only [Expr.eval, Env.get_succ, hsec,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨drk, roC'⟩
    simp only [aDrKey, fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfSlots, ahsfHybrid,
      ahsfRecvCount, ahsfMkSaltCache,
      ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      stUpd, stMk, asSecb, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRootRoCache, asAdvKeys,
      Expr.eval, Env.get_succ, Env.get_zero, hs]
    simp only [authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal,
      authRespToVal, authRenc, drKeyToVal, drKeyV, hWon]

theorem roRootFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy)
    (x : Var Γ₂ (.prod (B 32) (B 32)))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (rkv dhv : Bytes)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hx : Env.get env (h₂.wk x) = (rkv, dhv))
    (hB : AuthListsBounded K s) :
    (roRootFixedB K fhst x).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.roRootQuery rkv dhv) s := by
  simp only [roRootFixedB, letV, bindV, eval_letC, Comp.eval, Expr.eval, v, ahsBase, ahsfHybrid,
    asHasWonAuth, aNone, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal,
    AuthSubHops1to3.stepAuthOtherPrim]
  have hWonEq : (authStateToVal s.toAuthHybridState.base).2.1 =
      s.toAuthHybridState.base.hasWonAuth := rfl
  rw [hWonEq]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true =>
    simp [hWon, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authRespToVal, authRenc]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [rootRoC_eval S K _ _ _ _ s.toAuthHybridState.base rfl hB.rootRoCache_le]
    simp only [Expr.eval, Env.get_succ, hx,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    apply bind_congr; intro ⟨⟨rk1, ck1⟩, rootC'⟩
    simp only [aRootKdf, fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfSlots, ahsfHybrid,
      ahsfRecvCount, ahsfMkSaltCache,
      ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
      stUpd, stMk, asSecb, asPrincipals, asSpkBundles, asOpkEntries,
      asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
      asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
      asRoCache, asAdvKeys,
      Expr.eval, Env.get_succ, Env.get_zero, hs]
    simp only [authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
      authHybridStateToVal, authStateToVal,
      authRespToVal, authRenc, hWon]

theorem registerFixedB_eval (fhst : Var Γ₁ authHybridStateFixedTy) (sk : Var Γ₂ (B 32))
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (s : AuthHybridStateFixed S) (skv : Bytes)
    (hs : Env.get env (h₁.wk fhst) = authHybridStateFixedToVal s)
    (hsk : Env.get env (h₂.wk sk) = skv) :
    (registerFixedB fhst sk).eval env =
      Prod.map authRespToVal authHybridStateFixedToVal <$>
        AuthSubHops1to3.stepAuthOtherPrim S (.registerKey skv) s := by
  simp only [registerFixedB, letV, bindV, v, ahsBase, ahsfHybrid,
    asHasWonAuth, aNone, aPk, fhstSetBase, ahsfUpd, ahsfMkSlots, ahsfSlots,
    ahsfRecvCount, ahsfMkSaltCache,
    ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    stUpd, stMk, asSecb, asPrincipals, asSpkBundles, asOpkEntries,
    asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asRoCache, asRootRoCache, asAdvKeys, natEq_eval, eval_letC, bytesLen_eval,
    Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hs, hsk, authHybridStateFixedToVal, authHybridStateFixedWithSlotsToVal, authSlotStateToVal,
    authHybridStateToVal, authStateToVal,
    AuthSubHops1to3.stepAuthOtherPrim, bne, map_eq_bind_pure_comp]
  cases hWon : s.toAuthHybridState.base.hasWonAuth with
  | true => simp [hWon, authRespToVal, authRenc]
  | false =>
    cases hLen : (skv.length == 32) <;> simp [hWon, authRespToVal, authRenc]

@[simp] def recvFinishTagToVal {S : Setup} : RecvFinishTag S → recvFinishTagTy.denote
  | .opk k j o kE bE oE usedT msg hstDec =>
    .inl ((k.val, (j.val, o.val)),
      (principalEntryToVal kE, (spkBundleEntryToVal bE, (opkEntryToVal oE,
        (usedT.map (fun (k, p, s, e) => (k, (p, (s, e)))),
          (preKeyMsgToVal msg, authHybridStateToVal hstDec))))))
  | .noOpk k j l kE bE usedT msg hstDec =>
    .inr ((k.val, (j.val, l.val)),
      (principalEntryToVal kE, (spkBundleEntryToVal bE,
        (usedT.map (fun (k, p, s, e) => (k, (p, (s, e)))),
          (preKeyMsgToVal msg, authHybridStateToVal hstDec)))))

@[simp] def recvFinishResToVal
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes)))) : recvFinishResTy.denote :=
  res?.map fun (drKey, rk1, ck1_1, pt, roC, rootC) =>
    (drKeyToVal drKey, (rk1, (ck1_1, (pt, (roC.map (Prod.map id drKeyToVal), rootC)))))

private theorem map_consume_opks (os : List ((Nat × Nat × Nat) × OpkEntry)) (k j o : Nat) :
    (os.map (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal)).map
      (fun (e : (Ty.prod (.prod .nat (.prod .nat .nat)) opkEntryTy).denote) =>
        if (e.1 == (k, j, o)) = true
        then (e.1, (e.2.1, (e.2.2.1, true))) else e) =
    (os.map (fun (idx, e) =>
      if idx == (k, j, o) then (idx, { e with consumed := true }) else (idx, e))).map
      (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal) := by
  rw [List.map_map, List.map_map]
  congr 1; funext ⟨⟨u, j', o'⟩, e⟩
  by_cases h1 : u = k <;> by_cases h2 : j' = j <;> by_cases h3 : o' = o <;>
    simp [h1, h2, h3, opkEntryToVal, Prod.map]

theorem consumeFirstMPrim_map_congr {α β : Type} (f : α → β)
    (pB : β → OracleComp PrimBaseSpec Bool) (pA : α → OracleComp PrimBaseSpec Bool)
    (markB : β → β) (markA : α → α) (L : List α)
    (hp : ∀ a, pB (f a) = pA a) (hMark : ∀ a, markB (f a) = f (markA a)) :
    AuthSubHops1to3.consumeFirstMPrim pB markB (L.map f) =
      (Prod.map id (List.map f)) <$> AuthSubHops1to3.consumeFirstMPrim pA markA L := by
  rw [consumeFirstMPrim_map f pB markB markA hMark L, funext hp]

theorem findMPrim_map_congr {α β : Type} (f : α → β)
    (pB : β → OracleComp PrimBaseSpec Bool) (pA : α → OracleComp PrimBaseSpec Bool) (L : List α)
    (hp : ∀ a, pB (f a) = pA a) :
    findMPrim pB (L.map f) = (Option.map f) <$> findMPrim pA L := by
  rw [findMPrim_map f pB L, funext hp]

/-- List-length invariant on a `RecvFinishTag S` prepared from a state bounded by `n`. -/
structure RecvTagBounded {S : Setup} (n : Nat) (tag : RecvFinishTag S) : Prop where
  principals_le       : tag.hstDec.base.principals.length ≤ n
  spkBundles_le       : tag.hstDec.base.spkBundles.length ≤ n
  opkEntries_le       : tag.hstDec.base.opkEntries.length ≤ n
  sessions_le         : tag.hstDec.base.sessions.length ≤ n
  usedSendSessions_le : tag.hstDec.base.usedSendSessions.length ≤ n
  usedRecvOPK_le      : tag.hstDec.base.usedRecvOPK.length ≤ n
  usedRecvNoOPK_le    : tag.hstDec.base.usedRecvNoOPK.length ≤ n
  usedKyberTriples_le : tag.hstDec.base.seenKyberBaseKeys.length ≤ n
  roCache_le          : tag.hstDec.base.roCache.length ≤ n
  rootRoCache_le      : tag.hstDec.base.rootRoCache.length ≤ n
  advKeys_le          : tag.hstDec.base.advKeys.length ≤ n
  initKemRecs_le      : tag.hstDec.initKemRecs.length ≤ n
  recvKemRecs_le      : tag.hstDec.recvKemRecs.length ≤ n + 1
  sentOPKEvents_le    : tag.hstDec.base.sentOPKEvents.length ≤ n
  sentNoOPKEvents_le  : tag.hstDec.base.sentNoOPKEvents.length ≤ n
  idealSessions_le    : tag.hstDec.idealSessions.length ≤ n
  usedTriples'_le     :
    match tag with
    | .opk _ _ _ _ _ _ usedTriples' _ _ => usedTriples'.length ≤ n + 1
    | .noOpk _ _ _ _ _ usedTriples' _ _ => usedTriples'.length ≤ n + 1

/-- List-length invariant on a `PreparedAuthRecvPrim S` produced from a state bounded by `n`. -/
structure PreparedRecvBounded {S : Setup} (n : Nat) (prep : PreparedAuthRecvPrim S) : Prop where
  hstDec_eq   : prep.finishTag.hstDec = prep.hstDec
  tag_bounded : RecvTagBounded n prep.finishTag

private theorem take_min_eq_take {α : Type} (K N : Nat) (xs : List α) (h : xs.length ≤ K) :
    xs.take (min K N) = xs.take N := by
  by_cases hKN : K ≤ N
  · rw [Nat.min_eq_left hKN, List.take_of_length_le h, List.take_of_length_le (Nat.le_trans h hKN)]
  · rw [Nat.min_eq_right (by omega)]

theorem recvFinishTagRunC_eval (tag : Var Γ₁ recvFinishTagTy) (res? : Expr pqxdhOps Δ recvFinishResTy)
    [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (tagv : RecvFinishTag S)
    (resv? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (htag : Env.get env (h₁.wk tag) = recvFinishTagToVal tagv)
    (hres : res?.eval env = recvFinishResToVal resv?)
    (hOpk : tagv.hstDec.base.opkEntries.length ≤ K)
    (hPrin : tagv.hstDec.base.principals.length ≤ K)
    (hSentO : resv?.isSome = true → tagv.hstDec.base.sentOPKEvents.length ≤ K := by
      first
      | simp
      | intro _; exact (‹PreparedRecvBounded _ _›).tag_bounded.sentOPKEvents_le
      | intro _; exact (‹RecvTagBounded _ _›).sentOPKEvents_le
      | intro _; assumption)
    (hSentN : resv?.isSome = true → tagv.hstDec.base.sentNoOPKEvents.length ≤ K := by
      first
      | simp
      | intro _; exact (‹PreparedRecvBounded _ _›).tag_bounded.sentNoOPKEvents_le
      | intro _; exact (‹RecvTagBounded _ _›).sentNoOPKEvents_le
      | intro _; assumption) :
    (recvFinishTagRunC S K tag res?).eval env =
      Prod.map authRespToVal authHybridStateToVal <$>
        RecvFinishTag.runPrim S true tagv resv? := by
  cases tagv with
  | opk k j o kE bE oE usedT msg hstDec =>
    have hTakeO : (hstDec.base.opkEntries.map
        (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal)).take K =
        hstDec.base.opkEntries.map
        (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal) := by
      apply List.take_of_length_le; simpa [RecvFinishTag.hstDec] using hOpk
    cases resv? with
    | none =>
      simp only [recvFinishTagRunC, RecvFinishTag.runPrim, letV, caseSumV, caseOptV, v,
        ahsBase, aNone, eval_letC, Comp.eval, Expr.eval,
        Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        htag, hres, recvFinishTagToVal, recvFinishResToVal, Option.map, map_pure, Prod.map,
        authRespToVal, authRenc]
    | some resv =>
      have hTakeSO : hstDec.base.sentOPKEvents.take (min K S.N_dh) =
          hstDec.base.sentOPKEvents.take S.N_dh :=
        take_min_eq_take K S.N_dh _ (by simpa [RecvFinishTag.hstDec] using hSentO rfl)
      rcases resv with ⟨drKey, rk1, ck1_1, pt, roC, rootC⟩
      simp only [recvFinishTagRunC, RecvFinishTag.runPrim, letV, bindV, caseSumV, caseOptV,
        consumeFirstMV, eMap, v, ahsBase, asOpkEntries, oeUpd, oeMk, oeOpkSk, oeOpkPk,
        pkmHdr, hdrIkAPk, hdrEkAPk, hdrKemCt, nat3Eq_eval, eval_letC,
        Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        htag, hres, recvFinishTagToVal, recvFinishResToVal, Option.map_some, authHybridStateToVal]
      rw [findHonestC_eval S _ _ _ hstDec.base rfl hPrin]
      simp only [Expr.eval, Env.get_succ, Env.get_zero,
        preKeyMsgToVal, preKeyMsgV, hdrV,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      apply bind_congr; intro snd?
      cases snd? with
      | none =>
        simp only [Option.map_none, aRecvUnfresh, ahsInitKemRecs,
          ahsRecvKemRecs, ahsIdealSessions, asSecb, asHasWonAuth, asPrincipals,
          asSpkBundles, asSessions, asUsedSendSessions, asUsedRecvOPK,
          asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents,
          asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
          Expr.eval, Env.get_succ, Env.get_zero]
        simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          drKeyToVal, drKeyV, hTakeO, Prod.map, pure_bind, List.map_cons]
        rw [map_consume_opks]
      | some sndP =>
        rcases sndP with ⟨sndIdx, sndEntry⟩
        simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, peCorrupted,
          Expr.eval, Env.get_succ, Env.get_zero]
        cases hCorr : sndEntry.corrupted with
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, aRecvHonest,
            ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, asSecb,
            asHasWonAuth, asPrincipals, asSpkBundles, asSessions,
            asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
            asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
            asAdvKeys,
            Expr.eval, Env.get_succ, Env.get_zero]
          simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc, hTakeO,
            pure_bind, List.map_cons]
          rw [map_consume_opks]
        | false =>
          simp only [Bool.not_false, ↓reduceIte, Expr.eval,
            consumeFirstML_eq_consumeFirstMPrim,
            peIkAPk, sbSpkPk, sbPqspkPk,
            spkBundleEntryToVal, opkEntryToVal,
            Env.get_succ, Env.get_zero,
            asSentOPKEvents, authStateToVal, hTakeO, ← List.map_take, hTakeSO]
          let recvEv : RecvdOPKEvent := {
            bCorr := kE.corrupted, a0 := msg.hdr.ikAPk, b0 := kE.ikAPk,
            sb := bE.spkPk, ob := oE.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bE.pqspkPk, ct := msg.hdr.kemCt, m := pt
          }
          rw [consumeFirstMPrim_map_congr sentOPKEventToVal _ (matchSentOPKPrim recvEv) _
            (fun s => { s with matched := true })]
          · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_def, Prod.map, id_eq]
            apply bind_congr; intro ⟨matchedOk, sentOPK'⟩
            simp only [aRecvHonest, ahsInitKemRecs, ahsRecvKemRecs,
              ahsIdealSessions, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
              asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
              asSentNoOPKEvents, asRecvdOPKEvents,
              asRecvdNoOPKEvents, asAdvKeys, boolOr_eval,
              Expr.eval, Env.get_succ, Env.get_zero]
            simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
              recvdOPKEventToVal, Bool.true_and, List.map_cons]
            rw [map_consume_opks]
          · intro s
            exact matchSentOPKC_eval .zero .zero _ recvEv s rfl rfl
          · intro s; rfl
  | noOpk k j l kE bE usedT msg hstDec =>
    cases resv? with
    | none =>
      simp only [recvFinishTagRunC, RecvFinishTag.runPrim, letV, caseSumV, caseOptV, v,
        ahsBase, aNone, eval_letC, Comp.eval, Expr.eval,
        Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        htag, hres, recvFinishTagToVal, recvFinishResToVal, Option.map_none, map_pure, Prod.map,
        authRespToVal, authRenc]
    | some resv =>
      have hTakeSN : hstDec.base.sentNoOPKEvents.take (min K S.N_dh) =
          hstDec.base.sentNoOPKEvents.take S.N_dh :=
        take_min_eq_take K S.N_dh _ (by simpa [RecvFinishTag.hstDec] using hSentN rfl)
      rcases resv with ⟨drKey, rk1, ck1_1, pt, roC, rootC⟩
      simp only [recvFinishTagRunC, RecvFinishTag.runPrim, letV, bindV, caseSumV, caseOptV,
        consumeFirstMV, v, ahsBase, pkmHdr, hdrIkAPk, hdrEkAPk, hdrKemCt, eval_letC,
        Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
        htag, hres, recvFinishTagToVal, recvFinishResToVal, Option.map_some, authHybridStateToVal]
      rw [findHonestC_eval S _ _ _ hstDec.base rfl hPrin]
      simp only [Expr.eval, Env.get_succ, Env.get_zero,
        preKeyMsgToVal, preKeyMsgV, hdrV,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      apply bind_congr; intro snd?
      cases snd? with
      | none =>
        simp only [Option.map_none, aRecvUnfresh, ahsInitKemRecs,
          ahsRecvKemRecs, ahsIdealSessions, asSecb, asHasWonAuth, asPrincipals,
          asSpkBundles, asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK,
          asUsedRecvNoOPK, asSentOPKEvents, asSentNoOPKEvents,
          asRecvdOPKEvents, asRecvdNoOPKEvents, asAdvKeys,
          Expr.eval, Env.get_succ, Env.get_zero]
        simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          drKeyToVal, drKeyV, Prod.map, pure_bind, List.map_cons]
      | some sndP =>
        rcases sndP with ⟨sndIdx, sndEntry⟩
        simp only [Option.map_some, Prod.map, id_eq, principalEntryToVal, peCorrupted,
          Expr.eval, Env.get_succ, Env.get_zero]
        cases hCorr : sndEntry.corrupted with
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, aRecvHonest,
            ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions, asSecb,
            asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries, asSessions,
            asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
            asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
            asAdvKeys,
            Expr.eval, Env.get_succ, Env.get_zero]
          simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
            pure_bind, List.map_cons]
        | false =>
          simp only [Bool.not_false, ↓reduceIte, Expr.eval,
            consumeFirstML_eq_consumeFirstMPrim,
            peIkAPk, sbSpkPk, sbPqspkPk,
            spkBundleEntryToVal,
            Env.get_succ, Env.get_zero,
            asSentNoOPKEvents, authStateToVal, ← List.map_take, hTakeSN]
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kE.corrupted, a0 := msg.hdr.ikAPk, b0 := kE.ikAPk,
            sb := bE.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bE.pqspkPk, ct := msg.hdr.kemCt, m := pt
          }
          rw [consumeFirstMPrim_map_congr sentNoOPKEventToVal _ (matchSentNoOPKPrim recvEv) _
            (fun s => { s with matched := true })]
          · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
              Function.comp_def, Prod.map, id_eq]
            apply bind_congr; intro ⟨matchedOk, sentNoOPK'⟩
            simp only [aRecvHonest, ahsInitKemRecs, ahsRecvKemRecs,
              ahsIdealSessions, asSecb, asHasWonAuth, asPrincipals, asSpkBundles,
              asOpkEntries, asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK,
              asSentOPKEvents, asRecvdOPKEvents,
              asRecvdNoOPKEvents, asAdvKeys, boolOr_eval,
              Expr.eval, Env.get_succ, Env.get_zero]
            simp only [authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
              recvdNoOPKEventToVal, Bool.true_and, List.map_cons]
          · intro s
            exact matchSentNoOPKC_eval .zero .zero _ recvEv s rfl rfl
          · intro s; rfl

@[simp] def finishSendArgsToVal {S : Setup}
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) : finishSendArgsTy.denote :=
  (sessionIdToVal sid,
    (principalEntryToVal uEntry,
      (peerPrincipal?.map (Prod.map id principalEntryToVal),
        (isFreshPeer,
          (preKeyBundleToVal bundle,
            ((m0, m1),
              ((ekASk, (ekAPk, (ss, (kemCt, (ephASk, ephAPk))))),
                (drKeyToVal drKey,
                  ((rk1, (ck1_0, (mkSeed, ck1_1))),
                    (spqrSalt?,
                      (pqRatchetMsg,
                        (msgKeysToVal deriveMessageKeys,
                          (ad,
                            (aeadCt,
                              (msgPlain,
                                (roCache'.map (Prod.map id drKeyToVal),
                                  rootRoCache'))))))))))))))))

theorem finishAuthHybridSendC_eval (hst : Var Γ₁ authHybridStateTy)
    (args : Expr pqxdhOps Δ finishSendArgsTy)
    [h₁ : Ext Γ₁ Δ] (env : Env Δ)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hstv : AuthHybridState S)
    (hhst : Env.get env (h₁.wk hst) = authHybridStateToVal hstv)
    (hargs : args.eval env = finishSendArgsToVal sid uEntry peerPrincipal? isFreshPeer bundle
      m0 m1 ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt?
      pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache')
    (hSpk : hstv.base.spkBundles.length ≤ K) (hPrin : hstv.base.principals.length ≤ K)
    (hOpk : hstv.base.opkEntries.length ≤ K) :
    (finishAuthHybridSendC S K hst args).eval env =
      Prod.map authRespToVal authHybridStateToVal <$>
        finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
          ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt?
          pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hstv := by
  unfold finishAuthHybridSendC finishAuthHybridSendPrim
  repeat' (rw [letV_eval]; simp only [v, ahsBase, hdMk, pmMk, peIkAPk, pkbSpkId, pkbOpkB?,
    pkbPqspkId, optFst, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero,
    hhst, hargs, finishSendArgsToVal, authHybridStateToVal])
  simp only [bindV, Comp.eval]
  rw [checkBundleProvenanceExactC_eval S K _ _ _ hstv.base bundle rfl rfl hSpk hPrin hOpk]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr; intro ⟨spkHon, opkHon, pqspkHon⟩
  rw [checkBundleSpkHonIdealC_eval S _ _ _ hstv.base bundle rfl rfl hPrin hSpk]
  simp only []
  apply bind_congr; intro spkHonIdeal
  repeat' (rw [letV_eval]; simp only [v, seMk, pkbIkB, pkbSpkB, pkbPqspkB, optSnd,
    eCaseOpt, snoMk, soMk, ikrMk, isSomeE, iasMk, boolOr_eval, bytesBeq_eval,
    ahsUpd, ahsMk, ahsInitKemRecs, ahsRecvKemRecs, ahsIdealSessions,
    stUpd, stMk, asSecb, asHasWonAuth, asPrincipals, asSpkBundles, asOpkEntries,
    asSessions, asUsedSendSessions, asUsedRecvOPK, asUsedRecvNoOPK, asUsedKyberTriples,
    asSentOPKEvents, asSentNoOPKEvents, asRecvdOPKEvents, asRecvdNoOPKEvents,
    asAdvKeys, aSendFresh, aSendUnfresh,
    Expr.eval, Ext.refl_wk, Env.get_succ, Env.get_zero, hhst])
  simp only [Comp.eval, Expr.eval, Env.get_succ, Env.get_zero]
  cases peerPrincipal? with
  | none =>
    cases hOpkB : bundle.opkB? <;>
      cases isFreshPeer <;>
      simp only [hOpkB, Option.map_none, Option.map_some, Option.isSome, Prod.map,
        Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or, ↓reduceIte, Bool.false_eq_true,
        authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
        sessionIdToVal, sidV, principalEntryToVal, preKeyBundleToVal, bundleV,
        drKeyToVal, drKeyV, msgKeysToVal, msgKeysV,
        authSessionEntryToVal,
        initKemRecordToVal, idealAuthSessionToVal, preKeyMsgV,
        hdrV, bne, pure_bind, Function.comp_def, List.map_cons]
  | some pP =>
    rcases pP with ⟨pIdx, pEntry⟩
    cases hOpkB : bundle.opkB? with
    | none =>
      cases isFreshPeer <;>
        cases spkHonIdeal <;>
        cases pqspkHon <;>
        simp only [hOpkB, Option.map_none, Option.map_some, Option.isSome, Prod.map, id_eq,
          Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or, ↓reduceIte,
          Bool.false_eq_true, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          sessionIdToVal, sidV, principalEntryToVal, preKeyBundleToVal, bundleV,
          drKeyToVal, drKeyV, msgKeysToVal, msgKeysV,
          authSessionEntryToVal, sentNoOPKEventToVal,
          initKemRecordToVal, idealAuthSessionToVal, preKeyMsgV,
          hdrV, bne, pure_bind, Function.comp_def, List.map_cons]
    | some oP =>
      rcases oP with ⟨opkId, opkPk⟩
      cases isFreshPeer <;>
        cases spkHonIdeal <;>
        cases pqspkHon <;>
        simp only [hOpkB, Option.map_some, Option.isSome, Prod.map, id_eq,
          Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or, ↓reduceIte,
          Bool.false_eq_true, authHybridStateToVal, authStateToVal, authRespToVal, authRenc,
          sessionIdToVal, sidV, principalEntryToVal, preKeyBundleToVal, bundleV,
          drKeyToVal, drKeyV, msgKeysToVal, msgKeysV,
          authSessionEntryToVal, sentOPKEventToVal,
          initKemRecordToVal, idealAuthSessionToVal, preKeyMsgV,
          hdrV, bne, pure_bind, Function.comp_def, List.map_cons]

@[simp] def preparedAuthRecvToVal {S : Setup} (p : PreparedAuthRecvPrim S) :
    preparedAuthRecvTy.denote :=
  (principalEntryToVal p.kEntry,
    (spkBundleEntryToVal p.bEntry,
      (p.opkPk?,
        (p.secrets,
          (p.dhRatchet,
            (p.isUncorruptedHonestSender,
              (p.matchedSess?.map idealAuthSessionToVal,
                (p.sameEph,
                  (authHybridStateToVal p.hstDec,
                    recvFinishTagToVal p.finishTag)))))))))

private theorem any_usedRecv_eq_contains (xs : List (Nat × Nat × Nat)) (k j o : Nat) :
    (xs.map (fun (u, j', o') => (u, (j', o')))).any (fun e => e == (k, (j, o))) =
    xs.contains (k, j, o) := by
  rw [Bool.eq_iff_iff, List.any_map, List.any_eq_true, List.contains_iff_exists_mem_beq]
  refine exists_congr (fun ⟨u, j', o'⟩ => and_congr_right' ?_)
  by_cases h1 : u = k <;> by_cases h2 : j' = j <;> by_cases h3 : o' = o <;>
    simp [h1, h2, h3] <;> omega

theorem prepareAuthHybridRecvOPKC_eval (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (hstv : AuthHybridState S) (kv : Fin S.N_id) (jv : Fin S.N_recv) (ov : Fin S.N_opk)
    (msgv : PreKeyMsg)
    (hhst : Env.get env (h₁.wk hst) = authHybridStateToVal hstv)
    (hx : Env.get env (h₂.wk x) = (kv.val, (jv.val, (ov.val, preKeyMsgToVal msgv))))
    (hB : AuthHybridListsBounded K hstv) :
    (prepareAuthHybridRecvC S K true hst x).eval env =
      Option.map preparedAuthRecvToVal <$>
        prepareAuthHybridRecvOPKPrim S kv jv ov msgv hstv := by
  have hTakeUsedO : (hstv.base.usedRecvOPK.map (fun (u, j', o') => (u, (j', o')))).take K =
      hstv.base.usedRecvOPK.map (fun (u, j', o') => (u, (j', o'))) := by
    apply List.take_of_length_le; simpa using hB.usedRecvOPK_le
  have hTakeP : (hstv.base.principals.map (Prod.map id principalEntryToVal)).take K =
      hstv.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  have hTakeS : (hstv.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      hstv.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.spkBundles_le
  have hTakeO : (hstv.base.opkEntries.map
      (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal)).take K =
      hstv.base.opkEntries.map
      (Prod.map (fun (u, j', o') => (u, (j', o'))) opkEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.opkEntries_le
  have hTakeI : hstv.idealSessions.take (min K S.N_dh) = hstv.idealSessions.take S.N_dh :=
    take_min_eq_take K S.N_dh hstv.idealSessions hB.idealSessions_le
  unfold prepareAuthHybridRecvC prepareAuthHybridRecvOPKPrim
  rw [letV_eval]
  have hBase : (ahsBase (v hst)).eval env = authStateToVal hstv.base := by
    simp [ahsBase, v, Expr.eval, hhst, authHybridStateToVal]
  rw [hBase]
  have hWonE : (asHasWonAuth (.var .zero)).eval (.cons (authStateToVal hstv.base) env) =
      hstv.base.hasWonAuth := rfl
  simp only [Comp.eval, v, Ext.refl_wk, hWonE]
  cases hWon : hstv.base.hasWonAuth with
  | true => simp [Expr.eval]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    repeat' (rw [letV_eval]; simp only [pkmHdr, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, hx, preKeyMsgToVal, preKeyMsgV])
    simp only [Comp.eval, Expr.eval, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk, hdrEkAPk,
      pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval,
      Env.get_succ, Env.get_zero, hx, hdrV, preKeyMsgToVal, preKeyMsgV]
    cases hHdr : (msgv.hdr.spkId == UInt32.ofNat jv.val &&
        msgv.hdr.pqspkId == UInt32.ofNat jv.val &&
        msgv.hdr.opkId? == some (UInt32.ofNat ov.val) &&
        msgv.hdr.ikAPk.length == 32 &&
        msgv.hdr.ekAPk.length == 32 &&
        msgv.ephAPk.length == 32) with
    | false => simp []
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, eAny, asUsedRecvOPK, nat3Eq_eval,
        Env.get_succ, Env.get_zero,
        authStateToVal, hTakeUsedO, any_usedRecv_eq_contains]
      cases hUsed : hstv.base.usedRecvOPK.contains (kv.val, jv.val, ov.val) with
      | true => simp []
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, bindV, Comp.eval]
        rw [koskSenderOkC_eval S K _ _ _ hstv.base rfl hB.advKeys_le hB.principals_le]
        simp only [Expr.eval, Env.get_succ, Env.get_zero,
          map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr; intro koskOk
        cases koskOk with
        | false => simp []
        | true =>
          simp only [Comp.eval, Expr.eval, Env.get_zero,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            caseOptV, eFind, asPrincipals, asSpkBundles, natEq_eval, nat2Eq_eval,
            Env.get_succ, hx, hTakeP, hTakeS,
            List.find?_map, Function.comp_def, Prod.map, id_eq]
          cases hFindP :
              hstv.base.principals.find? (fun (idx, _) => idx == kv.val) with
          | none => simp []
          | some kP =>
            rcases kP with ⟨kIdx, kEntry⟩
            cases hFindS :
                hstv.base.spkBundles.find? (fun (idx, _) => idx == (kv.val, jv.val)) with
            | none => simp []
            | some bP =>
              rcases bP with ⟨bIdx, bEntry⟩
              simp only [Option.map_some]
              rw [letV_eval]; simp only [Expr.eval, Env.get_succ, Env.get_zero]
              rw [letV_eval]; simp only [Expr.eval, Env.get_succ, Env.get_zero]
              rw [letV_eval_eq _ _ _
                (checkAndMarkKyberBaseKeySeen hstv.base.seenKyberBaseKeys kv.val msgv.hdr.pqspkId
                  msgv.hdr.spkId msgv.hdr.ekAPk)
                (by
                  rw [kyberCheckE_eval K _ _ _
                    (by simp [asUsedKyberTriples, Expr.eval, hB.usedKyberTriples_le])]
                  simp [asUsedKyberTriples, Expr.eval, hx])]
              simp only [asOpkEntries, nat3Eq_eval,
                Comp.eval, Expr.eval, Env.get_succ, Env.get_zero,
                hTakeO, List.find?_map, Function.comp_def, Prod.map, id_eq]
              cases hFindO : hstv.base.opkEntries.find?
                  (fun (idx, _) => idx == (kv.val, jv.val, ov.val)) with
              | none => simp []
              | some oP =>
                rcases oP with ⟨oIdx, oEntry⟩
                simp only [Option.map_some, Prod.map]
                rw [letV_eval]; simp only [Expr.eval, Env.get_zero]
                cases hCons : oEntry.consumed with
                | true =>
                  simp [Comp.eval, Expr.eval, oeConsumed, opkEntryToVal, hCons]
                | false =>
                  simp only [Comp.eval, Expr.eval, oeConsumed, boolOr_eval,
                    sbPqspkSk, hdrKemCt, spkBundleEntryToVal,
                    queryPrim_eval, evalPrimQ,
                    Env.get_succ, Env.get_zero, opkEntryToVal, hCons,
                    Bool.false_eq_true, ↓reduceIte, bind_assoc]
                  apply bind_congr; intro (can : Bool)
                  apply bind_congr; intro (canE : Bool)
                  cases hCan : (!(checkAndMarkKyberBaseKeySeen hstv.base.seenKyberBaseKeys kv.val
                      msgv.hdr.pqspkId msgv.hdr.spkId msgv.hdr.ekAPk).1 || !can || !canE) with
                  | true => simp []
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
                    apply bind_congr; intro ss?
                    cases ss? with
                    | none => simp []
                    | some ss =>
                      simp only []
                      rw [letV_eval]
                      simp only [sbPqspkPk,
                        Expr.eval, Env.get_succ, Env.get_zero, hx]
                      rw [letV_eval]
                      simp only [ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
                        ahsIdealSessions, Expr.eval,
                        Env.get_succ, Env.get_zero, hhst, authHybridStateToVal]
                      simp only [Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
                        sbSpkSk, peSecIKA0, oeOpkSk,
                        Env.get_succ, Env.get_zero,
                        principalEntryToVal, bind_assoc]
                      apply bind_congr; intro dh1
                      apply bind_congr; intro dh2
                      apply bind_congr; intro dh3
                      apply bind_congr; intro dh4
                      rw [letV_eval]
                      simp only [buildSecretsE_eval, Expr.eval,
                        Env.get_succ, Env.get_zero]
                      simp only [Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
                        Env.get_succ, Env.get_zero]
                      apply bind_congr; intro dhR
                      rw [findHonestC_eval S _ _ _ hstv.base (by simp [authStateToVal]) hB.principals_le]
                      simp only [Expr.eval,
                        Env.get_succ, Env.get_zero,
                        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
                      apply bind_congr; intro snd?
                      rw [letV_eval]
                      simp only [eCaseOpt, peCorrupted, Expr.eval, Env.get_zero]
                      repeat' (rw [letV_eval]; simp only [peIkAPk, sbSpkPk, oeOpkPk,
                        Expr.eval, Env.get_succ, Env.get_zero])
                      simp only [findMV, findML_eq_findMPrim, Comp.eval, Expr.eval,
                        Env.get_succ, Env.get_zero, ← List.map_take, hTakeI]
                      rw [findMPrim_map_congr idealAuthSessionToVal _
                        (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
                          bEntry.pqspkPk msgv.hdr)]
                      · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
                        apply bind_congr; intro matched?
                        cases matched? with
                        | none =>
                          simp only [Option.map_none, pure_bind]
                          rw [letV_eval]
                          cases snd? with
                          | none =>
                            simp [Comp.eval, Expr.eval, hCons, preparedAuthRecvToVal,
                              recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                              principalEntryToVal, spkBundleEntryToVal, opkEntryToVal,
                              preKeyMsgToVal, preKeyMsgV, hdrV]
                          | some sP =>
                            rcases sP with ⟨_, _⟩
                            simp [Comp.eval, Expr.eval, hCons, preparedAuthRecvToVal,
                              recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                              principalEntryToVal, spkBundleEntryToVal, opkEntryToVal,
                              preKeyMsgToVal, preKeyMsgV, hdrV]
                        | some s =>
                          simp only [Option.map_some, Expr.eval,
                            queryPrim_eval, evalPrimQ, bytesBeq_eval,
                            iasEphAPk, idealAuthSessionToVal,
                            Env.get_succ, Env.get_zero, bind_assoc]
                          apply bind_congr; intro p1
                          apply bind_congr; intro p2
                          simp only [pure_bind]
                          rw [letV_eval]
                          cases snd? with
                          | none =>
                            simp [Comp.eval, Expr.eval, hCons, preparedAuthRecvToVal,
                              recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                              principalEntryToVal, spkBundleEntryToVal, opkEntryToVal,
                              preKeyMsgToVal, preKeyMsgV, hdrV]
                          | some sP =>
                            rcases sP with ⟨_, _⟩
                            simp [Comp.eval, Expr.eval, hCons, preparedAuthRecvToVal,
                              recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                              principalEntryToVal, spkBundleEntryToVal, opkEntryToVal,
                              preKeyMsgToVal, preKeyMsgV, hdrV]
                      · intro s
                        exact matchIdealAuthHandshakeC_eval S _ _ _ _ _ .zero _
                          kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk) bEntry.pqspkPk msgv.hdr s
                          rfl rfl rfl rfl rfl rfl

theorem prepareAuthHybridRecvNoOPKC_eval (hst : Var Γ₁ authHybridStateTy) (x : Var Γ₂ recvQTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (hstv : AuthHybridState S) (kv : Fin S.N_id) (jv : Fin S.N_recv) (lv : Fin S.N_no_opk)
    (msgv : PreKeyMsg)
    (hhst : Env.get env (h₁.wk hst) = authHybridStateToVal hstv)
    (hx : Env.get env (h₂.wk x) = (kv.val, (jv.val, (lv.val, preKeyMsgToVal msgv))))
    (hB : AuthHybridListsBounded K hstv) :
    (prepareAuthHybridRecvC S K false hst x).eval env =
      Option.map preparedAuthRecvToVal <$>
        prepareAuthHybridRecvNoOPKPrim S kv jv lv msgv hstv := by
  have hTakeUsedN : (hstv.base.usedRecvNoOPK.map (fun (u, j', l') => (u, (j', l')))).take K =
      hstv.base.usedRecvNoOPK.map (fun (u, j', l') => (u, (j', l'))) := by
    apply List.take_of_length_le; simpa using hB.usedRecvNoOPK_le
  have hTakeP : (hstv.base.principals.map (Prod.map id principalEntryToVal)).take K =
      hstv.base.principals.map (Prod.map id principalEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.principals_le
  have hTakeS : (hstv.base.spkBundles.map (Prod.map id spkBundleEntryToVal)).take K =
      hstv.base.spkBundles.map (Prod.map id spkBundleEntryToVal) := by
    apply List.take_of_length_le; simpa using hB.spkBundles_le
  have hTakeI : hstv.idealSessions.take (min K S.N_dh) = hstv.idealSessions.take S.N_dh :=
    take_min_eq_take K S.N_dh hstv.idealSessions hB.idealSessions_le
  unfold prepareAuthHybridRecvC prepareAuthHybridRecvNoOPKPrim
  rw [letV_eval]
  have hBase : (ahsBase (v hst)).eval env = authStateToVal hstv.base := by
    simp [ahsBase, v, Expr.eval, hhst, authHybridStateToVal]
  rw [hBase]
  have hWonE : (asHasWonAuth (.var .zero)).eval (.cons (authStateToVal hstv.base) env) =
      hstv.base.hasWonAuth := rfl
  simp only [Comp.eval, v, Ext.refl_wk, hWonE]
  cases hWon : hstv.base.hasWonAuth with
  | true => simp [Expr.eval]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    repeat' (rw [letV_eval]; simp only [pkmHdr, Expr.eval, Ext.step_wk, Ext.refl_wk,
      Env.get_succ, Env.get_zero, hx, preKeyMsgToVal, preKeyMsgV])
    simp only [Comp.eval, Expr.eval, hdrSpkId, hdrPqspkId, hdrOpkId?, hdrIkAPk, hdrEkAPk,
      pkmEphAPk, optU32Eq_eval, natEq_eval, u32Beq_eval, u32OfNat_eval, bytesLen_eval,
      Env.get_succ, Env.get_zero,
      hx, hdrV, preKeyMsgToVal, preKeyMsgV]
    cases hHdr : (msgv.hdr.spkId == UInt32.ofNat jv.val &&
        msgv.hdr.pqspkId == UInt32.ofNat jv.val &&
        msgv.hdr.opkId? == none &&
        msgv.hdr.ikAPk.length == 32 &&
        msgv.hdr.ekAPk.length == 32 &&
        msgv.ephAPk.length == 32) with
    | false => simp []
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Expr.eval, eAny, asUsedRecvNoOPK, nat3Eq_eval,
        Env.get_succ, Env.get_zero,
        authStateToVal, hTakeUsedN, any_usedRecv_eq_contains]
      cases hUsed : hstv.base.usedRecvNoOPK.contains (kv.val, jv.val, lv.val) with
      | true => simp []
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [bindV_eval, koskSenderOkC_eval S K _ _ _ hstv.base rfl hB.advKeys_le hB.principals_le]
        simp only [Expr.eval, Env.get_succ, Env.get_zero,
          map_eq_bind_pure_comp, bind_assoc]
        apply bind_congr; intro koskOk
        cases koskOk with
        | false => simp [Comp.eval, Expr.eval]
        | true =>
          simp only [Comp.eval, Expr.eval, Env.get_zero,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            caseOptV, eFind, asPrincipals, asSpkBundles, natEq_eval, nat2Eq_eval,
            Env.get_succ, hx, hTakeP, hTakeS,
            List.find?_map, Function.comp_def, Prod.map, id_eq]
          cases hFindP :
              hstv.base.principals.find? (fun (idx, _) => idx == kv.val) with
          | none => simp []
          | some kP =>
            rcases kP with ⟨kIdx, kEntry⟩
            cases hFindS :
                hstv.base.spkBundles.find? (fun (idx, _) => idx == (kv.val, jv.val)) with
            | none => simp []
            | some bP =>
              rcases bP with ⟨bIdx, bEntry⟩
              simp only [Option.map_some, Prod.map, id_eq]
              rw [letV_eval]; simp only [Expr.eval, Env.get_succ, Env.get_zero]
              rw [letV_eval]; simp only [Expr.eval, Env.get_succ, Env.get_zero]
              rw [letV_eval_eq _ _ _
                (checkAndMarkKyberBaseKeySeen hstv.base.seenKyberBaseKeys kv.val msgv.hdr.pqspkId
                  msgv.hdr.spkId msgv.hdr.ekAPk)
                (by
                  rw [kyberCheckE_eval K _ _ _
                    (by simp [asUsedKyberTriples, Expr.eval, hB.usedKyberTriples_le])]
                  simp [asUsedKyberTriples, Expr.eval, hx])]
              rw [bindV_eval]
              simp only [Expr.eval,
                queryPrim_eval, evalPrimQ,
                Env.get_succ, Env.get_zero, bind_assoc]
              apply bind_congr; intro (can : Bool)
              rw [bindV_eval]
              simp only [Comp.eval, Expr.eval, boolOr_eval,
                queryPrim_eval, evalPrimQ,
                Env.get_succ, Env.get_zero]
              apply bind_congr; intro (canE : Bool)
              by_cases hCan : (!(checkAndMarkKyberBaseKeySeen hstv.base.seenKyberBaseKeys kv.val
                  msgv.hdr.pqspkId msgv.hdr.spkId msgv.hdr.ekAPk).1 || !can || !canE) = true
              · simp [hCan]
              · simp only [Bool.not_eq_true] at hCan
                simp only [hCan, Bool.false_eq_true, ↓reduceIte,
                  bindV, Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
                  Env.get_succ, Env.get_zero,
                  sbPqspkSk, hdrKemCt, spkBundleEntryToVal, bind_assoc]
                apply bind_congr; intro ss?
                cases ss? with
                | none => simp []
                | some ss =>
                  simp only []
                  rw [letV_eval]
                  simp only [sbPqspkPk, Expr.eval, Env.get_succ, Env.get_zero, hx]
                  rw [letV_eval]
                  simp only [ahsBase, ahsInitKemRecs, ahsRecvKemRecs,
                    ahsIdealSessions, Expr.eval,
                    Env.get_succ, Env.get_zero, hhst, authHybridStateToVal]
                  simp only [Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
                    sbSpkSk, peSecIKA0,
                    Env.get_succ, Env.get_zero,
                    principalEntryToVal, bind_assoc]
                  apply bind_congr; intro dh1
                  apply bind_congr; intro dh2
                  apply bind_congr; intro dh3
                  rw [letV_eval]
                  simp only [buildSecretsE_eval, Expr.eval, Env.get_succ, Env.get_zero]
                  simp only [Comp.eval, Expr.eval, queryPrim_eval, evalPrimQ,
                    Env.get_succ, Env.get_zero]
                  apply bind_congr; intro dhR
                  rw [findHonestC_eval S _ _ _ hstv.base (by simp [authStateToVal]) hB.principals_le]
                  simp only [Expr.eval, Env.get_succ, Env.get_zero,
                    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
                  apply bind_congr; intro snd?
                  rw [letV_eval]
                  simp only [eCaseOpt, peCorrupted, Expr.eval, Env.get_zero]
                  repeat' (rw [letV_eval]; simp only [peIkAPk, sbSpkPk,
                    Expr.eval, Env.get_succ, Env.get_zero])
                  simp only [findMV, findML_eq_findMPrim, Comp.eval, Expr.eval,
                    Env.get_succ, Env.get_zero, ← List.map_take, hTakeI]
                  rw [findMPrim_map_congr idealAuthSessionToVal _
                    (matchIdealAuthHandshakePrim kEntry.ikAPk bEntry.spkPk none
                      bEntry.pqspkPk msgv.hdr)]
                  · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
                    apply bind_congr; intro matched?
                    cases matched? with
                    | none =>
                      simp only [Option.map_none, pure_bind]
                      rw [letV_eval]
                      cases snd? with
                      | none =>
                        simp [Comp.eval, Expr.eval, preparedAuthRecvToVal,
                          recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                          principalEntryToVal, spkBundleEntryToVal,
                          preKeyMsgToVal, preKeyMsgV, hdrV]
                      | some sP =>
                        rcases sP with ⟨_, _⟩
                        simp [Comp.eval, Expr.eval, preparedAuthRecvToVal,
                          recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                          principalEntryToVal, spkBundleEntryToVal,
                          preKeyMsgToVal, preKeyMsgV, hdrV]
                    | some s =>
                      simp only [Option.map_some, Expr.eval,
                        queryPrim_eval, evalPrimQ, bytesBeq_eval,
                        iasEphAPk, idealAuthSessionToVal,
                        Env.get_succ, Env.get_zero, bind_assoc]
                      apply bind_congr; intro p1
                      apply bind_congr; intro p2
                      simp only [pure_bind]
                      rw [letV_eval]
                      cases snd? with
                      | none =>
                        simp [Comp.eval, Expr.eval, preparedAuthRecvToVal,
                          recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                          principalEntryToVal, spkBundleEntryToVal,
                          preKeyMsgToVal, preKeyMsgV, hdrV]
                      | some sP =>
                        rcases sP with ⟨_, _⟩
                        simp [Comp.eval, Expr.eval, preparedAuthRecvToVal,
                          recvFinishTagToVal, authHybridStateToVal, authStateToVal,
                          principalEntryToVal, spkBundleEntryToVal,
                          preKeyMsgToVal, preKeyMsgV, hdrV]
                  · intro s
                    exact matchIdealAuthHandshakeC_eval S _ _ _ _ _ .zero _
                      kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msgv.hdr s
                      rfl rfl rfl rfl rfl rfl

end SharedHelperEval

/-! ## Leaf Invariants and List-Length Preservation -/

/-- Structural leaf predicate holding when `P a` holds at every `pure a` leaf of `m`. -/
def AllLeaves {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (P : α → Prop) (m : OracleComp spec α) : Prop :=
  OracleComp.construct (C := fun _ => Prop) P (fun _ _ r => ∀ u, r u) m

theorem AllLeaves.toHoldsOnLeaves {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {m : OracleComp spec α} (h : AllLeaves P m) :
    HoldsOnLeaves P m := by
  induction m using OracleComp.inductionOn with
  | pure a => exact HoldsOnLeaves.pure h
  | query_bind q k ih => exact HoldsOnLeaves.bind_const _ (fun u => ih u (h u))

theorem allLeaves_bind_congr {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {P : α → Prop} {m : OracleComp spec α} (hm : AllLeaves P m)
    {f g : α → OracleComp spec β} (hfg : ∀ a, P a → f a = g a) :
    m >>= f = m >>= g :=
  hm.toHoldsOnLeaves.bind_congr f g hfg

theorem AllLeaves.pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {a : α} (ha : P a) :
    AllLeaves P (Pure.pure a : OracleComp spec α) := ha

theorem AllLeaves.bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α γ : Type}
    {P : α → Prop} {Q : γ → Prop} {m : OracleComp spec α} {k : α → OracleComp spec γ}
    (hm : AllLeaves P m) (hk : ∀ a, P a → AllLeaves Q (k a)) :
    AllLeaves Q (m >>= k) := by
  induction m using OracleComp.inductionOn with
  | pure a => exact hk a hm
  | query_bind q k' ih =>
    intro u
    exact ih u (hm u)

theorem AllLeaves.const {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (m : OracleComp spec α) :
    AllLeaves (fun _ => True) m := by
  induction m using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind _ _ ih => intro u; exact ih u

theorem AllLeaves.bind_const {ι : Type} {spec : OracleSpec.{0, 0} ι} {α γ : Type}
    {Q : γ → Prop} (m : OracleComp spec α) {k : α → OracleComp spec γ}
    (hk : ∀ a, AllLeaves Q (k a)) :
    AllLeaves Q (m >>= k) :=
  AllLeaves.bind (AllLeaves.const m) (fun a _ => hk a)

theorem AllLeaves.mono {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P Q : α → Prop} {m : OracleComp spec α}
    (hm : AllLeaves P m) (hImp : ∀ a, P a → Q a) :
    AllLeaves Q m := by
  induction m using OracleComp.inductionOn with
  | pure a => exact hImp a hm
  | query_bind q k ih =>
    intro u
    exact ih u (hm u)

theorem AllLeaves.ite {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} (c : Bool) {t e : OracleComp spec α}
    (ht : c = true → AllLeaves P t) (he : c = false → AllLeaves P e) :
    AllLeaves P (if c then t else e) := by
  cases c with
  | true => exact ht rfl
  | false => exact he rfl

theorem AllLeaves.embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {P : α → Prop} {m : OracleComp PrimBaseSpec α} (hm : AllLeaves P m) :
    AllLeaves P (FgGapDh.embedPrim (spec := spec) m) := by
  induction m using OracleComp.inductionOn with
  | pure a => exact hm
  | query_bind q k ih =>
    intro u
    exact ih u (hm u)

theorem AllLeaves.embedUnif {α : Type} {P : α → Prop} {m : ProbComp α}
    (hm : AllLeaves P m) :
    AllLeaves P (FgGapDh.embedUnif m) := by
  induction m using OracleComp.inductionOn with
  | pure a => exact hm
  | query_bind q k ih =>
    intro u
    exact ih u (hm u)

theorem evalHkdfRoPure_length_le {n : Nat} (roCache : List (Bytes × DRKey)) (secrets : Bytes)
    (hRo : roCache.length ≤ n) :
    AllLeaves (fun p => p.2.length ≤ n + 1) (evalHkdfRoPure roCache secrets) := by
  unfold evalHkdfRoPure
  cases roCache.find? (fun (s, _) => s == secrets) with
  | some p => rcases p with ⟨_, _⟩; exact AllLeaves.pure (by simp; omega)
  | none => exact AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega))

theorem evalRootKdfRoPure_length_le {n : Nat}
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))) (rk dh : Bytes)
    (hRoot : rootRoCache.length ≤ n) :
    AllLeaves (fun p => p.2.length ≤ n + 1) (evalRootKdfRoPure rootRoCache rk dh) := by
  unfold evalRootKdfRoPure
  cases rootRoCache.find? (fun (k, _) => k == (rk, dh)) with
  | some p => rcases p with ⟨_, _⟩; exact AllLeaves.pure (by simp; omega)
  | none =>
    exact AllLeaves.bind_const _ (fun _ =>
      AllLeaves.bind_const _ (fun _ => AllLeaves.pure (by simp; omega)))

theorem checkAndMarkKyberUsed_length_le {n : Nat}
    (used : List (Nat × KeyId × KeyId × Bytes)) (k : Nat) (pqspkId spkId : KeyId) (ekAPk : Bytes)
    (hU : used.length ≤ n) :
    (checkAndMarkKyberBaseKeySeen used k pqspkId spkId ekAPk).2.length ≤ n + 1 := by
  unfold checkAndMarkKyberBaseKeySeen
  dsimp only
  split <;> simp <;> omega

theorem finishAuthHybridSendPrim_bounded {S : Setup} {n : Nat}
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S)
    (hB : AuthHybridListsBounded n hst)
    (hRo : roCache'.length ≤ n + 1)
    (hRoot : rootRoCache'.length ≤ n + 1) :
    AllLeaves (fun p => AuthHybridListsBounded (n + 1) p.2)
      (finishAuthHybridSendPrim S sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst) := by
  unfold finishAuthHybridSendPrim
  refine AllLeaves.bind_const _ (fun ⟨spkHon, opkHon, pqspkHon⟩ => ?_)
  refine AllLeaves.bind_const _ (fun spkHonIdeal => ?_)
  refine AllLeaves.pure ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRo, hRoot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_trans hB.principals_le (Nat.le_succ n)
  · exact Nat.le_trans hB.spkBundles_le (Nat.le_succ n)
  · exact Nat.le_trans hB.opkEntries_le (Nat.le_succ n)
  · simp; exact hB.sessions_le
  · simp; exact hB.usedSendSessions_le
  · exact Nat.le_trans hB.usedRecvOPK_le (Nat.le_succ n)
  · exact Nat.le_trans hB.usedRecvNoOPK_le (Nat.le_succ n)
  · exact Nat.le_trans hB.usedKyberTriples_le (Nat.le_succ n)
  · exact Nat.le_trans hB.advKeys_le (Nat.le_succ n)
  · simp; exact hB.initKemRecs_le
  · exact Nat.le_trans hB.recvKemRecs_le (Nat.le_succ n)
  · cases peerPrincipal? <;> cases bundle.opkB? <;> dsimp only <;>
      (try simp) <;> have := hB.sentOPKEvents_le <;> omega
  · cases peerPrincipal? <;> cases bundle.opkB? <;> dsimp only <;>
      (try simp) <;> have := hB.sentNoOPKEvents_le <;> omega
  · cases peerPrincipal? <;> cases bundle.opkB? <;> dsimp only <;> (try split_ifs) <;>
      (try simp) <;> have := hB.idealSessions_le <;> omega

theorem PreparedRecvBounded.roCache_le {S : Setup} {n : Nat} {prep : PreparedAuthRecvPrim S}
    (hP : PreparedRecvBounded n prep) :
    prep.hstDec.base.roCache.length ≤ n := by
  rw [← hP.hstDec_eq]; exact hP.tag_bounded.roCache_le

theorem PreparedRecvBounded.rootRoCache_le {S : Setup} {n : Nat} {prep : PreparedAuthRecvPrim S}
    (hP : PreparedRecvBounded n prep) :
    prep.hstDec.base.rootRoCache.length ≤ n := by
  rw [← hP.hstDec_eq]; exact hP.tag_bounded.rootRoCache_le

theorem RecvTagBounded.hstDec_bounded {S : Setup} {n : Nat} {tag : RecvFinishTag S}
    (hT : RecvTagBounded n tag) :
    AuthHybridListsBounded (n + 1) tag.hstDec where
  principals_le       := Nat.le_trans hT.principals_le (Nat.le_succ n)
  spkBundles_le       := Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
  opkEntries_le       := Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
  sessions_le         := Nat.le_trans hT.sessions_le (Nat.le_succ n)
  usedSendSessions_le := Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
  usedRecvOPK_le      := Nat.le_trans hT.usedRecvOPK_le (Nat.le_succ n)
  usedRecvNoOPK_le    := Nat.le_trans hT.usedRecvNoOPK_le (Nat.le_succ n)
  usedKyberTriples_le := Nat.le_trans hT.usedKyberTriples_le (Nat.le_succ n)
  roCache_le          := Nat.le_trans hT.roCache_le (Nat.le_succ n)
  rootRoCache_le      := Nat.le_trans hT.rootRoCache_le (Nat.le_succ n)
  advKeys_le          := Nat.le_trans hT.advKeys_le (Nat.le_succ n)
  initKemRecs_le      := Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
  recvKemRecs_le      := hT.recvKemRecs_le
  sentOPKEvents_le    := Nat.le_trans hT.sentOPKEvents_le (Nat.le_succ n)
  sentNoOPKEvents_le  := Nat.le_trans hT.sentNoOPKEvents_le (Nat.le_succ n)
  idealSessions_le    := Nat.le_trans hT.idealSessions_le (Nat.le_succ n)

private theorem consumeFirstMPrim_length_le {α : Type} {n : Nat}
    (p : α → OracleComp PrimBaseSpec Bool) (mark : α → α) (xs : List α)
    (hLen : xs.length ≤ n) :
    AllLeaves (fun res => res.2.length ≤ n) (AuthSubHops1to3.consumeFirstMPrim p mark xs) := by
  suffices ∀ l : List α,
      AllLeaves (fun res => res.2.length = l.length) (consumeFirstMPrim p mark l) by
    exact (this xs).mono (fun res h => by rw [h]; exact hLen)
  intro l
  induction l with
  | nil => exact AllLeaves.pure rfl
  | cons x tl ih =>
    simp only [consumeFirstMPrim]
    refine AllLeaves.bind_const (p x) (fun b => ?_)
    cases b with
    | true => exact AllLeaves.pure (by simp)
    | false =>
      refine AllLeaves.bind ih (fun ⟨ok, xs'⟩ hEq => ?_)
      exact AllLeaves.pure (by simp [hEq])

theorem recvFinishTagRunPrim_bounded {S : Setup} {n : Nat}
    (checkAuth : Bool) (tag : RecvFinishTag S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
      List ((Bytes × Bytes) × (Bytes × Bytes))))
    (hT : RecvTagBounded n tag)
    (hRes : ∀ drKey rk1 ck1_1 pt roCache' rootRoCache',
      res? = some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') →
      roCache'.length ≤ n + 1 ∧ rootRoCache'.length ≤ n + 1) :
    AllLeaves (fun p => AuthHybridListsBounded (n + 1) p.2)
      (tag.runPrim S checkAuth res?) := by
  have hSO : tag.hstDec.base.sentOPKEvents.length ≤ n + 1 :=
    Nat.le_trans hT.sentOPKEvents_le (Nat.le_succ n)
  have hSN : tag.hstDec.base.sentNoOPKEvents.length ≤ n + 1 :=
    Nat.le_trans hT.sentNoOPKEvents_le (Nat.le_succ n)
  have hIS : tag.hstDec.idealSessions.length ≤ n + 1 :=
    Nat.le_trans hT.idealSessions_le (Nat.le_succ n)
  cases tag with
  | opk k j o kEntry bEntry oEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim
    cases hR : res? with
    | none => exact AllLeaves.pure hT.hstDec_bounded
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      rcases hRes drKey rk1 ck1_1 pt roCache' rootRoCache' hR with ⟨hRo, hRoot⟩
      have hTriples : usedTriples'.length ≤ n + 1 := hT.usedTriples'_le
      refine AllLeaves.bind_const _ (fun sender? => ?_)
      cases sender? with
      | none =>
        refine AllLeaves.pure
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
            hSO, hSN, hIS⟩
        · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
        · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
        · simp; exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
        · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
        · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
        · simp; exact hT.usedRecvOPK_le
        · exact Nat.le_trans hT.usedRecvNoOPK_le (Nat.le_succ n)
        · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
        · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        refine AllLeaves.ite (!senderEntry.corrupted) (fun _ => ?_) (fun _ => ?_)
        · refine AllLeaves.bind
            (consumeFirstMPrim_length_le (n := n + 1) _ _ _
              (by simp [RecvFinishTag.hstDec] at hSO ⊢; omega))
            (fun ⟨matchedOk, sentOPK'⟩ hSO' => ?_)
          refine AllLeaves.pure
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
              hSO', hSN, hIS⟩
          · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
          · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
          · simp; exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
          · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
          · simp; exact hT.usedRecvOPK_le
          · exact Nat.le_trans hT.usedRecvNoOPK_le (Nat.le_succ n)
          · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
          · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
        · refine AllLeaves.pure
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
              hSO, hSN, hIS⟩
          · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
          · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
          · simp; exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
          · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
          · simp; exact hT.usedRecvOPK_le
          · exact Nat.le_trans hT.usedRecvNoOPK_le (Nat.le_succ n)
          · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
          · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
  | noOpk k j l kEntry bEntry usedTriples' msg hstDec =>
    unfold RecvFinishTag.runPrim
    cases hR : res? with
    | none => exact AllLeaves.pure hT.hstDec_bounded
    | some val =>
      rcases val with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      rcases hRes drKey rk1 ck1_1 pt roCache' rootRoCache' hR with ⟨hRo, hRoot⟩
      have hTriples : usedTriples'.length ≤ n + 1 := hT.usedTriples'_le
      refine AllLeaves.bind_const _ (fun sender? => ?_)
      cases sender? with
      | none =>
        refine AllLeaves.pure
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
            hSO, hSN, hIS⟩
        · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
        · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
        · exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
        · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
        · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
        · exact Nat.le_trans hT.usedRecvOPK_le (Nat.le_succ n)
        · simp; exact hT.usedRecvNoOPK_le
        · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
        · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
      | some sp =>
        rcases sp with ⟨_, senderEntry⟩
        refine AllLeaves.ite (!senderEntry.corrupted) (fun _ => ?_) (fun _ => ?_)
        · refine AllLeaves.bind
            (consumeFirstMPrim_length_le (n := n + 1) _ _ _
              (by simp [RecvFinishTag.hstDec] at hSN ⊢; omega))
            (fun ⟨matchedOk, sentNoOPK'⟩ hSN' => ?_)
          refine AllLeaves.pure
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
              hSO, hSN', hIS⟩
          · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
          · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
          · exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
          · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedRecvOPK_le (Nat.le_succ n)
          · simp; exact hT.usedRecvNoOPK_le
          · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
          · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)
        · refine AllLeaves.pure
            ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hTriples, hRo, hRoot, ?_, ?_, hT.recvKemRecs_le,
              hSO, hSN, hIS⟩
          · exact Nat.le_trans hT.principals_le (Nat.le_succ n)
          · exact Nat.le_trans hT.spkBundles_le (Nat.le_succ n)
          · exact Nat.le_trans hT.opkEntries_le (Nat.le_succ n)
          · exact Nat.le_trans hT.sessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedSendSessions_le (Nat.le_succ n)
          · exact Nat.le_trans hT.usedRecvOPK_le (Nat.le_succ n)
          · simp; exact hT.usedRecvNoOPK_le
          · exact Nat.le_trans hT.advKeys_le (Nat.le_succ n)
          · exact Nat.le_trans hT.initKemRecs_le (Nat.le_succ n)

theorem prepareAuthHybridRecvOPKPrim_bounded {S : Setup} {n : Nat}
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hB : AuthHybridListsBounded n hst) :
    AllLeaves
      (fun prep? => ∀ prep, prep? = some prep → PreparedRecvBounded n prep)
      (prepareAuthHybridRecvOPKPrim S k j o msg hst) := by
  unfold prepareAuthHybridRecvOPKPrim
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun koskOk => ?_)
  refine AllLeaves.ite (!koskOk) (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact AllLeaves.pure (by intro _ h; cases h)
  | some kP =>
    rcases kP with ⟨_, kEntry⟩
    cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact AllLeaves.pure (by intro _ h; cases h)
    | some bP =>
      rcases bP with ⟨_, bEntry⟩
      cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact AllLeaves.pure (by intro _ h; cases h)
      | some oP =>
        rcases oP with ⟨_, oEntry⟩
        refine AllLeaves.ite oEntry.consumed
          (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
        refine AllLeaves.bind_const _ (fun canon => ?_)
        refine AllLeaves.bind_const _ (fun canonEph => ?_)
        refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
        refine AllLeaves.bind_const _ (fun ss? => ?_)
        cases ss? with
        | none => exact AllLeaves.pure (by intro _ h; cases h)
        | some ss =>
          refine AllLeaves.bind_const _ (fun dh1 => ?_)
          refine AllLeaves.bind_const _ (fun dh2 => ?_)
          refine AllLeaves.bind_const _ (fun dh3 => ?_)
          refine AllLeaves.bind_const _ (fun dh4 => ?_)
          refine AllLeaves.bind_const _ (fun dhR => ?_)
          refine AllLeaves.bind_const _ (fun sender? => ?_)
          refine AllLeaves.bind_const _ (fun matched? => ?_)
          have hDone : ∀ sameEph : Bool,
              ∀ prep : PreparedAuthRecvPrim S,
                some { kEntry := kEntry, bEntry := bEntry, opkPk? := some oEntry.opkPk,
                       secrets := buildSecrets dh1 dh2 dh3 (some dh4) ss, dhRatchet := dhR,
                       isUncorruptedHonestSender :=
                         match sender? with | some (_, sE) => !sE.corrupted | none => false,
                       matchedSess? := matched?, sameEph := sameEph,
                       hstDec := { hst with
                         recvKemRecs :=
                           { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                             pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss } ::
                           hst.recvKemRecs },
                       finishTag := .opk k j o kEntry bEntry oEntry
                         (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                           msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                         msg
                         { hst with
                           recvKemRecs :=
                             { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                               pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss } ::
                             hst.recvKemRecs } } = some prep →
                PreparedRecvBounded n prep := by
            intro sameEph prep hPrep
            cases hPrep
            exact ⟨rfl, ⟨hB.principals_le, hB.spkBundles_le, hB.opkEntries_le,
              hB.sessions_le, hB.usedSendSessions_le, hB.usedRecvOPK_le, hB.usedRecvNoOPK_le,
              hB.usedKyberTriples_le, hB.roCache_le, hB.rootRoCache_le, hB.advKeys_le,
              hB.initKemRecs_le, by simp [RecvFinishTag.hstDec, hB.recvKemRecs_le],
              hB.sentOPKEvents_le, hB.sentNoOPKEvents_le, hB.idealSessions_le,
              checkAndMarkKyberUsed_length_le _ _ _ _ _ hB.usedKyberTriples_le⟩⟩
          cases matched? with
          | none => exact AllLeaves.pure (hDone false)
          | some s =>
            refine AllLeaves.bind_const _ (fun p1 => ?_)
            refine AllLeaves.bind_const _ (fun p2 => ?_)
            exact AllLeaves.pure (hDone (p1 == p2))

theorem prepareAuthHybridRecvNoOPKPrim_bounded {S : Setup} {n : Nat}
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hB : AuthHybridListsBounded n hst) :
    AllLeaves
      (fun prep? => ∀ prep, prep? = some prep → PreparedRecvBounded n prep)
      (prepareAuthHybridRecvNoOPKPrim S k j l msg hst) := by
  unfold prepareAuthHybridRecvNoOPKPrim
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  refine AllLeaves.bind_const _ (fun koskOk => ?_)
  refine AllLeaves.ite (!koskOk) (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
  cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact AllLeaves.pure (by intro _ h; cases h)
  | some kP =>
    rcases kP with ⟨_, kEntry⟩
    cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact AllLeaves.pure (by intro _ h; cases h)
    | some bP =>
      rcases bP with ⟨_, bEntry⟩
      refine AllLeaves.bind_const _ (fun canon => ?_)
      refine AllLeaves.bind_const _ (fun canonEph => ?_)
      refine AllLeaves.ite _ (fun _ => AllLeaves.pure (by intro _ h; cases h)) (fun _ => ?_)
      refine AllLeaves.bind_const _ (fun ss? => ?_)
      cases ss? with
      | none => exact AllLeaves.pure (by intro _ h; cases h)
      | some ss =>
        refine AllLeaves.bind_const _ (fun dh1 => ?_)
        refine AllLeaves.bind_const _ (fun dh2 => ?_)
        refine AllLeaves.bind_const _ (fun dh3 => ?_)
        refine AllLeaves.bind_const _ (fun dhR => ?_)
        refine AllLeaves.bind_const _ (fun sender? => ?_)
        refine AllLeaves.bind_const _ (fun matched? => ?_)
        have hDone : ∀ sameEph : Bool,
            ∀ prep : PreparedAuthRecvPrim S,
              some { kEntry := kEntry, bEntry := bEntry, opkPk? := none,
                     secrets := buildSecrets dh1 dh2 dh3 none ss, dhRatchet := dhR,
                     isUncorruptedHonestSender :=
                       match sender? with | some (_, sE) => !sE.corrupted | none => false,
                     matchedSess? := matched?, sameEph := sameEph,
                     hstDec := { hst with
                       recvKemRecs :=
                         { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                           pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss } ::
                         hst.recvKemRecs },
                     finishTag := .noOpk k j l kEntry bEntry
                       (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                         msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                       msg
                       { hst with
                         recvKemRecs :=
                           { k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
                             pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss } ::
                           hst.recvKemRecs } } = some prep →
              PreparedRecvBounded n prep := by
          intro sameEph prep hPrep
          cases hPrep
          exact ⟨rfl, ⟨hB.principals_le, hB.spkBundles_le, hB.opkEntries_le,
            hB.sessions_le, hB.usedSendSessions_le, hB.usedRecvOPK_le, hB.usedRecvNoOPK_le,
            hB.usedKyberTriples_le, hB.roCache_le, hB.rootRoCache_le, hB.advKeys_le,
            hB.initKemRecs_le, by simp [RecvFinishTag.hstDec, hB.recvKemRecs_le],
            hB.sentOPKEvents_le, hB.sentNoOPKEvents_le, hB.idealSessions_le,
            checkAndMarkKyberUsed_length_le _ _ _ _ _ hB.usedKyberTriples_le⟩⟩
        cases matched? with
        | none => exact AllLeaves.pure (hDone false)
        | some s =>
          refine AllLeaves.bind_const _ (fun p1 => ?_)
          refine AllLeaves.bind_const _ (fun p2 => ?_)
          exact AllLeaves.pure (hDone (p1 == p2))

theorem stepAuthOtherPrim_bounded {S : Setup} {n : Nat}
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hB : AuthListsBounded n hst) :
    AllLeaves (fun p => AuthListsBounded (n + 1) p.2)
      (AuthSubHops1to3.stepAuthOtherPrim S q hst) := by
  have hB' : AuthListsBounded (n + 1) hst := hB.mono (Nat.le_succ n)
  cases q with
  | initPrin u =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
      AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))))
    refine AllLeaves.pure ⟨⟨?_, hB'.spkBundles_le, hB'.opkEntries_le, hB'.sessions_le,
      hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
      hB'.usedKyberTriples_le, hB'.roCache_le, hB'.rootRoCache_le, hB'.advKeys_le,
      hB'.initKemRecs_le, hB'.recvKemRecs_le,
      hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
    simp; exact hB.principals_le
  | corruptIK u =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact AllLeaves.pure hB'
    | some p =>
      rcases p with ⟨_, entry⟩
      refine AllLeaves.pure ⟨⟨?_, hB'.spkBundles_le, hB'.opkEntries_le, hB'.sessions_le,
        hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
        hB'.usedKyberTriples_le, hB'.roCache_le, hB'.rootRoCache_le, hB'.advKeys_le,
        hB'.initKemRecs_le, hB'.recvKemRecs_le,
        hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
      simp; exact hB'.principals_le
  | genSPK u j =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => exact AllLeaves.pure hB'
    | some p =>
      rcases p with ⟨_, uEntry⟩
      refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
        AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ =>
          AllLeaves.bind_const _ (fun ⟨_, _⟩ => AllLeaves.bind_const _ (fun _ =>
            AllLeaves.bind_const _ (fun _ => ?_)))))))
      refine AllLeaves.pure ⟨⟨hB'.principals_le, ?_, hB'.opkEntries_le, hB'.sessions_le,
        hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
        hB'.usedKyberTriples_le, hB'.roCache_le, hB'.rootRoCache_le, hB'.advKeys_le,
        hB'.initKemRecs_le, hB'.recvKemRecs_le,
        hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
      simp; exact hB.spkBundles_le
  | genOPK u j o =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    refine AllLeaves.pure ⟨⟨hB'.principals_le, hB'.spkBundles_le, ?_, hB'.sessions_le,
      hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
      hB'.usedKyberTriples_le, hB'.roCache_le, hB'.rootRoCache_le, hB'.advKeys_le,
      hB'.initKemRecs_le, hB'.recvKemRecs_le,
      hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
    simp; exact hB.opkEntries_le
  | registerKey sk =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.ite _ (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind_const _ (fun _ => AllLeaves.bind_const _ (fun _ => ?_))
    refine AllLeaves.pure ⟨⟨hB'.principals_le, hB'.spkBundles_le, hB'.opkEntries_le,
      hB'.sessions_le, hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
      hB'.usedKyberTriples_le, hB'.roCache_le, hB'.rootRoCache_le, ?_,
      hB'.initKemRecs_le, hB'.recvKemRecs_le,
      hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
    simp; exact hB.advKeys_le
  | roQuery secrets =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind (AllLeaves.embedUnif (evalHkdfRoPure_length_le _ _ hB.roCache_le)) ?_
    intro ⟨dk, roCache'⟩ hRo
    exact AllLeaves.pure ⟨⟨hB'.principals_le, hB'.spkBundles_le, hB'.opkEntries_le,
      hB'.sessions_le, hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
      hB'.usedKyberTriples_le, hRo, hB'.rootRoCache_le, hB'.advKeys_le,
      hB'.initKemRecs_le, hB'.recvKemRecs_le,
      hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
  | roRootQuery rk dh =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => ?_)
    refine AllLeaves.bind
      (AllLeaves.embedUnif (evalRootKdfRoPure_length_le _ _ _ hB.rootRoCache_le)) ?_
    intro ⟨out, rootRoCache'⟩ hRoot
    exact AllLeaves.pure ⟨⟨hB'.principals_le, hB'.spkBundles_le, hB'.opkEntries_le,
      hB'.sessions_le, hB'.usedSendSessions_le, hB'.usedRecvOPK_le, hB'.usedRecvNoOPK_le,
      hB'.usedKyberTriples_le, hB'.roCache_le, hRoot, hB'.advKeys_le,
      hB'.initKemRecs_le, hB'.recvKemRecs_le,
      hB'.sentOPKEvents_le, hB'.sentNoOPKEvents_le, hB'.idealSessions_le⟩, hB'.mkSaltCache_le⟩
  | revealDhSecrets =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => AllLeaves.pure hB')
  | sendOPK _ _ _ _ _ =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => AllLeaves.pure hB')
  | sendNoOPK _ _ _ _ _ =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => AllLeaves.pure hB')
  | recvOPK _ _ _ _ =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => AllLeaves.pure hB')
  | recvNoOPK _ _ _ _ =>
    unfold AuthSubHops1to3.stepAuthOtherPrim; dsimp only
    refine AllLeaves.ite hst.toAuthHybridState.base.hasWonAuth
      (fun _ => AllLeaves.pure hB') (fun _ => AllLeaves.pure hB')

end SignalPqxdh.Security.ReductionDsl.AuthPrf

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

@[simp] theorem embedPrim_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    _root_.SignalPqxdh.Security.embedPrim (spec := spec) (Pure.pure a) = Pure.pure a := rfl

def PTag.evalPrim : (g : PTag) → g.dom.denote → OracleComp PrimBaseSpec g.cod.denote
  | .x25519 => fun x => primQ (.x25519 x.1 x.2)
  | .x25519Base => fun sk => primQ (.x25519Base sk)
  | .isCanonical => fun pk => primQ (.isCanonical pk)
  | .pow8 => fun pk => primQ (.pow8 pk)
  | .sigPkGen => fun sk => primQ (.sigPkGen sk)
  | .sigSign _ => fun x => primQ (.sigSign x.1 x.2.1 x.2.2)
  | .sigVerify _ => fun x => primQ (.sigVerify x.1 x.2.1 x.2.2)
  | .kemKeyGen => fun coins => primQ (.kemKeyGen coins)
  | .kemEncaps => fun x => primQ (.kemEncaps x.1 x.2)
  | .kemDecaps => fun x => primQ (.kemDecaps x.1 x.2)
  | .hkdfDerive96 _ => fun bytes => drKeyToVal <$> primQ (.hkdfDerive96 bytes)
  | .rootCreateChain => fun x => primQ (.rootCreateChain x.1 x.2)
  | .chainKdfSeed => fun ck => primQ (.chainKdfSeed ck)
  | .chainKdfNext => fun ck => primQ (.chainKdfNext ck)
  | .spqrInitSend _ _ => fun x => primQ (.spqrInitSend x.1 x.2)
  | .spqrInitRecv _ _ => fun x => primQ (.spqrInitRecv x.1 x.2)
  | .deriveMsgKeys _ => fun x => msgKeysToVal <$> primQ (.deriveMsgKeys x.1 x.2)
  | .aeadEnc _ _ _ => fun x => primQ (.aeadEnc (valToMsgKeys x.1) x.2.1 x.2.2)
  | .aeadDec _ _ _ => fun x => primQ (.aeadDec (valToMsgKeys x.1) x.2.1 x.2.2)

theorem queryPrim_eval {Γ : List PT} (g : PTag)
    (e : Expr pqxdhOps Γ g.dom) (env : Env Γ) :
    (queryPrim g e).eval env = PTag.evalPrim g (e.eval env) := by
  cases g <;> rfl

@[simp] theorem queryPrim_x25519_eval (x : (SignalPqxdh.LegacyCosted.PTag.x25519).dom.denote) :
    PTag.evalPrim .x25519 x = primQ (.x25519 x.1 x.2) := rfl
@[simp] theorem queryPrim_x25519Base_eval (x : Bytes) :
    PTag.evalPrim .x25519Base x = primQ (.x25519Base x) := rfl
@[simp] theorem queryPrim_isCanonical_eval (x : Bytes) :
    PTag.evalPrim .isCanonical x = primQ (.isCanonical x) := rfl
@[simp] theorem queryPrim_pow8_eval (x : Bytes) :
    PTag.evalPrim .pow8 x = primQ (.pow8 x) := rfl
@[simp] theorem queryPrim_sigPkGen_eval (x : Bytes) :
    PTag.evalPrim .sigPkGen x = primQ (.sigPkGen x) := rfl
@[simp] theorem queryPrim_sigSign_eval (m : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.sigSign m).dom.denote) :
    PTag.evalPrim (.sigSign m) x = primQ (.sigSign x.1 x.2.1 x.2.2) := rfl
@[simp] theorem queryPrim_sigVerify_eval (m : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.sigVerify m).dom.denote) :
    PTag.evalPrim (.sigVerify m) x = primQ (.sigVerify x.1 x.2.1 x.2.2) := rfl
@[simp] theorem queryPrim_kemKeyGen_eval (x : Bytes) :
    PTag.evalPrim .kemKeyGen x = primQ (.kemKeyGen x) := rfl
@[simp] theorem queryPrim_kemEncaps_eval (x : (SignalPqxdh.LegacyCosted.PTag.kemEncaps).dom.denote) :
    PTag.evalPrim .kemEncaps x = primQ (.kemEncaps x.1 x.2) := rfl
@[simp] theorem queryPrim_kemDecaps_eval (x : (SignalPqxdh.LegacyCosted.PTag.kemDecaps).dom.denote) :
    PTag.evalPrim .kemDecaps x = primQ (.kemDecaps x.1 x.2) := rfl
@[simp] theorem queryPrim_hkdfDerive96_eval (w : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.hkdfDerive96 w).dom.denote) :
    PTag.evalPrim (.hkdfDerive96 w) x = drKeyToVal <$> primQ (.hkdfDerive96 x) := rfl
@[simp] theorem queryPrim_rootCreateChain_eval (x : (SignalPqxdh.LegacyCosted.PTag.rootCreateChain).dom.denote) :
    PTag.evalPrim .rootCreateChain x = primQ (.rootCreateChain x.1 x.2) := rfl
@[simp] theorem queryPrim_chainKdfSeed_eval (x : Bytes) :
    PTag.evalPrim .chainKdfSeed x = primQ (.chainKdfSeed x) := rfl
@[simp] theorem queryPrim_chainKdfNext_eval (x : Bytes) :
    PTag.evalPrim .chainKdfNext x = primQ (.chainKdfNext x) := rfl
@[simp] theorem queryPrim_spqrInitSend_eval (p c : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.spqrInitSend p c).dom.denote) :
    PTag.evalPrim (.spqrInitSend p c) x = primQ (.spqrInitSend x.1 x.2) := rfl
@[simp] theorem queryPrim_spqrInitRecv_eval (p c : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.spqrInitRecv p c).dom.denote) :
    PTag.evalPrim (.spqrInitRecv p c) x = primQ (.spqrInitRecv x.1 x.2) := rfl
@[simp] theorem queryPrim_deriveMsgKeys_eval (s : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.deriveMsgKeys s).dom.denote) :
    PTag.evalPrim (.deriveMsgKeys s) x = msgKeysToVal <$> primQ (.deriveMsgKeys x.1 x.2) := rfl
@[simp] theorem queryPrim_aeadEnc_eval (a m c : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.aeadEnc a m c).dom.denote) :
    PTag.evalPrim (.aeadEnc a m c) x = primQ (.aeadEnc (valToMsgKeys x.1) x.2.1 x.2.2) := rfl
@[simp] theorem queryPrim_aeadDec_eval (a c m : ℕ+) (x : (SignalPqxdh.LegacyCosted.PTag.aeadDec a c m).dom.denote) :
    PTag.evalPrim (.aeadDec a c m) x = primQ (.aeadDec (valToMsgKeys x.1) x.2.1 x.2.2) := rfl

end SignalPqxdh.Security.ReductionDsl.AuthAead
