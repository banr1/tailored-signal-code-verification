/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.CostUB -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Soundness -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.SoundnessTwoClass -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import Computational.Proofs.ReductionDsl.Size


/-!
# Base Cost, Query, and `DdhStep` Infrastructure for `fgKeyIndGapDhProg`

Provides query weight functions, modular `costUB`/`queriesUB` lemmas, syntactic `totalCost` and
`totalQueries` bounds, and `DdhStep` potential infrastructure for `fgKeyIndGapDhProg`.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd


/-! ## Query Weight Functions and `liftBase` / `gPrim` Simp Lemmas -/

@[expose] def wPrimBase : pqPrimIface.Tag → ℕ := fun _ => 1

/-- Weight `1` on primitive tags `.inl _`, `0` on the DDH tag `.inr ()` in `pqGapDhIface`. -/
@[expose] def wPrimGdh : pqGapDhIface.Tag → ℕ
  | .inl _  => 1
  | .inr () => 0

/-- Weight `0` on primitive tags `.inl _`, `1` on the DDH tag `.inr ()` in `pqGapDhIface`. -/
@[expose] def wDdhGdh : pqGapDhIface.Tag → ℕ
  | .inl _  => 0
  | .inr () => 1

@[expose] def wsZeroBase : pqPrimIface.smp.Samp → ℕ := fun _ => 0

@[expose] def wsZero : pqGapDhIface.smp.Samp → ℕ := fun _ => 0

@[simp] theorem wPrimGdh_inl (g : PTag) : wPrimGdh (.inl g) = 1 := rfl
@[simp] theorem wPrimGdh_inr (u : Unit) : wPrimGdh (.inr u) = 0 := rfl
@[simp] theorem wDdhGdh_inl (g : PTag) : wDdhGdh (.inl g) = 0 := rfl
@[simp] theorem wDdhGdh_inr (u : Unit) : wDdhGdh (.inr u) = 1 := rfl
@[simp] theorem wPrimBase_apply (g : pqPrimIface.Tag) : wPrimBase g = 1 := rfl
@[simp] theorem wsZeroBase_apply (s : pqPrimIface.smp.Samp) : wsZeroBase s = 0 := rfl
@[simp] theorem wsZero_apply (s : pqGapDhIface.smp.Samp) : wsZero s = 0 := rfl

@[simp] theorem liftBase_costUB {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).costUB = c.costUB := by
  induction c <;> simp_all [liftBase, Comp.costUB, pqChalIface, pqPrimIface]

theorem liftBase_queries {C : ChallengerOracle} (w : (pqChalIface C).Tag → ℕ)
    (ws : (pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [liftBase, Comp.queries]

theorem liftBase_queriesUB {C : ChallengerOracle} (w : (pqChalIface C).Tag → ℕ)
    (ws : (pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).queriesUB w ws =
      Comp.queriesUB (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [liftBase, Comp.queriesUB]

@[simp] theorem Comp_queries_zero {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    c.queries (fun _ => 0) (fun _ => 0) = 0 := by
  induction c <;> simp_all [Comp.queries]

@[simp] theorem gPrim_costUB {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).costUB = c.costUB :=
  liftBase_costUB c

@[simp] theorem gPrim_queries_wPrimGdh {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries wPrimGdh wsZero = c.queries wPrimBase wsZeroBase :=
  liftBase_queries (C := gapDhDdhOracle) wPrimGdh wsZero c

@[simp] theorem gPrim_queriesUB_wPrimGdh {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimBase wsZeroBase :=
  liftBase_queriesUB (C := gapDhDdhOracle) wPrimGdh wsZero c

@[simp] theorem gPrim_queries_wDdhGdh {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries wDdhGdh wsZero = 0 := by
  rw [gPrim, liftBase_queries (C := gapDhDdhOracle)]
  exact Comp_queries_zero c

/-! ## Atomic `costUB`, `queriesUB`, and `queries` Simp Lemmas -/

@[simp] theorem F_X25519_length' : F_X25519.length = 32 := by decide
@[simp] theorem bits_0 : bits 0 = 1 := by decide
@[simp] theorem bits_1 : bits 1 = 1 := by decide
@[simp] theorem bits_2 : bits 2 = 2 := by decide
@[simp] theorem bits_3 : bits 3 = 2 := by decide
@[simp] theorem bits_32 : bits 32 = 6 := by decide
@[simp] theorem bits_64 : bits 64 = 7 := by decide
@[simp] theorem bits_96 : bits 96 = 7 := by decide
@[simp] theorem bits_128 : bits 128 = 8 := by decide
@[simp] theorem bits_160 : bits 160 = 8 := by decide
@[simp] theorem bits_192 : bits 192 = 8 := by decide

section AtomicSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[simp] theorem v_costUB [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).costUB = 1 := rfl

@[simp] theorem bindV_costUB (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).costUB = m.costUB + (k .zero).costUB + 1 := rfl

@[simp] theorem letV_costUB (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).costUB = e.costUB + 1 + (k .zero).costUB + 1 := rfl

@[simp] theorem caseOptV_costUB (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).costUB = o.costUB + (kn.costUB + (ks .zero).costUB) + 1 := rfl

@[simp] theorem caseSumV_costUB (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).costUB = s.costUB + ((kl .zero).costUB + (kr .zero).costUB) + 1 := rfl

@[simp] theorem findMV_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).costUB = xs.costUB + K * ((p .zero).costUB + 1) + 1 := rfl

@[simp] theorem anyMV_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).costUB = xs.costUB + K * ((p .zero).costUB + 1) + 1 := rfl

@[simp] theorem mapMV_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).costUB = xs.costUB + K * ((f .zero).costUB + 1) + 1 := rfl

@[simp] theorem foldMV_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).costUB =
      xs.costUB + init.costUB + K * ((f .zero (.succ .zero)).costUB + 1) + 1 := rfl

@[simp] theorem eLet_costUB (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).costUB = e.costUB + (k .zero).costUB + 1 := rfl

@[simp] theorem eCaseOpt_costUB (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).costUB = o.costUB + (kn.costUB + (ks .zero).costUB) + 1 := rfl

@[simp] theorem eCaseSum_costUB (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) :
    (eCaseSum s kl kr).costUB = s.costUB + ((kl .zero).costUB + (kr .zero).costUB) + 1 := rfl

@[simp] theorem eFind_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).costUB = xs.costUB + K * ((p .zero).costUB + 1) + 1 := rfl

@[simp] theorem eAny_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).costUB = xs.costUB + K * ((p .zero).costUB + 1) + 1 := rfl

@[simp] theorem eMap_costUB (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eMap K xs f).costUB = xs.costUB + K * ((f .zero).costUB + 1) + 1 := rfl

@[simp] theorem litB_costUB (w : ℕ+) (bs : Bytes) :
    (litB w bs (Γ := Γ)).costUB = 1 + (w.val + bs.length) := rfl

@[simp] theorem consB_costUB {w : ℕ+} (b : UInt8) (e : Expr pqxdhOps Γ (B w)) :
    (consB b e).costUB = e.costUB + (w.val + 1) := rfl

@[simp] theorem takeKB_costUB (w k : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (takeKB w k e).costUB = e.costUB + (w.val + k.val) := rfl

@[simp] theorem dropB_costUB {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (e : Expr pqxdhOps Γ (B w)) :
    (dropB n e).costUB = n.costUB + e.costUB + 1 + (w.val + 1) := rfl

@[simp] theorem lenB_costUB {w : ℕ+} (e : Expr pqxdhOps Γ (B w)) :
    (lenB e).costUB = e.costUB + bits w.val := rfl

@[simp] theorem eqB_costUB {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (eqB a b).costUB = a.costUB + b.costUB + 1 + (m.val + n.val) := rfl

@[simp] theorem u32OfNat_costUB (e : Expr pqxdhOps Γ .nat) :
    (u32OfNat e).costUB = e.costUB + 1 := rfl

@[simp] theorem eqU32_costUB (a b : Expr pqxdhOps Γ U32) :
    (eqU32 a b).costUB = a.costUB + b.costUB + 1 + 1 := rfl

@[simp] theorem sBool_costUB : (sBool (Γ := Γ)).costUB = 2 := rfl
@[simp] theorem sBytes32_costUB : (sBytes32 (Γ := Γ)).costUB = 34 := rfl
@[simp] theorem sRandom64_costUB : (sRandom64 (Γ := Γ)).costUB = 66 := rfl
@[simp] theorem sDrKey96_costUB : (sDrKey96 (Γ := Γ)).costUB = 98 := rfl
@[simp] theorem sIndex_costUB (N : ℕ) : (sIndex N (Γ := Γ)).costUB = 1 + (bits N + 1) := rfl

@[simp] theorem qX25519_costUB (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).costUB = e.costUB + 97 := rfl
@[simp] theorem qX25519Base_costUB (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).costUB = e.costUB + 65 := rfl
@[simp] theorem qIsCanonical_costUB (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).costUB = e.costUB + 33 := rfl
@[simp] theorem qPow8_costUB (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).costUB = e.costUB + 65 := rfl
@[simp] theorem qSigPkGen_costUB (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).costUB = e.costUB + 65 := rfl
@[simp] theorem qSigSign_costUB (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).costUB = e.costUB + (1 + (32 + (m.val + 64)) + 64) := rfl
@[simp] theorem qSigVerify_costUB (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).costUB = e.costUB + (1 + (32 + (m.val + 64)) + 0) := rfl
@[simp] theorem qKemKeyGen_costUB (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).costUB = e.costUB + 4801 := rfl
@[simp] theorem qKemEncaps_costUB (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).costUB = e.costUB + 3201 := rfl
@[simp] theorem qKemDecaps_costUB (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).costUB = e.costUB + 4769 := rfl
@[simp] theorem ddhQ_costUB (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).costUB = x.costUB + (y.costUB + z.costUB + 1) + 1 + 97 := rfl

/-! ### `queriesUB` and `queries` Simp Lemmas for Binders and Primitives -/

@[simp] theorem bindV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).queriesUB w ws = m.queriesUB w ws + (k .zero).queriesUB w ws := rfl

@[simp] theorem letV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).queriesUB w ws = (k .zero).queriesUB w ws := by
  simp [letV, Comp.queriesUB]

@[simp] theorem caseOptV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).queriesUB w ws = kn.queriesUB w ws + (ks .zero).queriesUB w ws := rfl

@[simp] theorem caseSumV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).queriesUB w ws =
      (kl .zero).queriesUB w ws + (kr .zero).queriesUB w ws := rfl

@[simp] theorem findMV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).queriesUB w ws = K * (p .zero).queriesUB w ws := rfl

@[simp] theorem anyMV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).queriesUB w ws = K * (p .zero).queriesUB w ws := rfl

@[simp] theorem mapMV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).queriesUB w ws = K * (f .zero).queriesUB w ws := rfl

@[simp] theorem foldMV_queriesUB (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).queriesUB w ws = K * (f .zero (.succ .zero)).queriesUB w ws := rfl

@[simp] theorem bindV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).queries w ws = m.queries w ws + (k .zero).queries w ws := rfl

@[simp] theorem letV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).queries w ws = (k .zero).queries w ws := by
  simp [letV, Comp.queries]

@[simp] theorem caseOptV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).queries w ws = max (kn.queries w ws) ((ks .zero).queries w ws) := rfl

@[simp] theorem caseSumV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).queries w ws =
      max ((kl .zero).queries w ws) ((kr .zero).queries w ws) := rfl

@[simp] theorem findMV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).queries w ws = K * (p .zero).queries w ws := rfl

@[simp] theorem anyMV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).queries w ws = K * (p .zero).queries w ws := rfl

@[simp] theorem mapMV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (mapMV K xs f).queries w ws = K * (f .zero).queries w ws := rfl

@[simp] theorem foldMV_queries (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    (foldMV K xs init f).queries w ws = K * (f .zero (.succ .zero)).queries w ws := rfl

@[simp] theorem sBool_queriesUB : (sBool (Γ := Γ)).queriesUB wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sBytes32_queriesUB : (sBytes32 (Γ := Γ)).queriesUB wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sRandom64_queriesUB : (sRandom64 (Γ := Γ)).queriesUB wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sDrKey96_queriesUB : (sDrKey96 (Γ := Γ)).queriesUB wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sIndex_queriesUB (N : ℕ) :
    (sIndex N (Γ := Γ)).queriesUB wPrimBase wsZeroBase = 0 := rfl

@[simp] theorem sBool_queries : (sBool (Γ := Γ)).queries wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sBytes32_queries : (sBytes32 (Γ := Γ)).queries wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sRandom64_queries : (sRandom64 (Γ := Γ)).queries wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sDrKey96_queries : (sDrKey96 (Γ := Γ)).queries wPrimBase wsZeroBase = 0 := rfl
@[simp] theorem sIndex_queries (N : ℕ) :
    (sIndex N (Γ := Γ)).queries wPrimBase wsZeroBase = 0 := rfl

@[simp] theorem qX25519_queriesUB (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    (qX25519 e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qX25519Base_queriesUB (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qIsCanonical_queriesUB (e : Expr pqxdhOps Γ (B 32)) :
    (qIsCanonical e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qPow8_queriesUB (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qSigPkGen_queriesUB (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qSigSign_queriesUB (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigSign m e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qSigVerify_queriesUB (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qKemKeyGen_queriesUB (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qKemEncaps_queriesUB (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    (qKemEncaps e).queriesUB wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qKemDecaps_queriesUB (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    (qKemDecaps e).queriesUB wPrimBase wsZeroBase = 1 := rfl

@[simp] theorem ddhQ_queriesUB_wPrimGdh (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).queriesUB wPrimGdh wsZero = 0 := rfl
@[simp] theorem ddhQ_queries_wDdhGdh (x y z : Expr pqxdhOps Γ (B 32)) :
    (ddhQ x y z).queries wDdhGdh wsZero = 1 := rfl

end AtomicSimp

/-! ## DDH Query Counts (`wDdhGdh`) -/

@[simp] theorem mkSecretPosC_chal {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) :
    (mkSecretPosC z).queries wDdhGdh wsZero = 0 := by
  simp [mkSecretPosC, Comp.queries]

@[simp] theorem mkPairPosC_chal {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (mkPairPosC pk1 pk2).queries wDdhGdh wsZero = 0 := by
  simp [mkPairPosC, Comp.queries]

@[simp] theorem computePosC_chal {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queries wDdhGdh wsZero = 0 := by
  simp [computePosC, Comp.queries]

@[simp] theorem computeOptPosInitC_chal {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries wDdhGdh wsZero = 0 := by
  simp [computeOptPosInitC, Comp.queries]

@[simp] theorem ddhEqC_chal {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries wDdhGdh wsZero = 1 := by
  simp [ddhEqC, Comp.queries]

@[simp] theorem ddhEqOptC_chal {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries wDdhGdh wsZero = 1 := by
  simp [ddhEqOptC, Comp.queries]

@[simp] theorem entryMatchesC_chal {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries wDdhGdh wsZero = 4 := by
  simp [entryMatchesC, Comp.queries]

@[simp] theorem fgPatchC_chal (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries wDdhGdh wsZero = 4 * K := by
  simp [fgPatchC, Comp.queries, Nat.mul_comm]

@[simp] theorem chooseRespRandC_chal (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries wDdhGdh wsZero = 0 := by
  simp [chooseRespRandC, Comp.queries]

@[simp] theorem chooseInitRandC_chal (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries wDdhGdh wsZero = 0 := by
  simp [chooseInitRandC, Comp.queries]

@[simp] theorem wrapBase_chal {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).queries wDdhGdh wsZero = 0 := by
  simp [wrapBase, Comp.queries]

@[simp] theorem wrapSim_chal {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).queries wDdhGdh wsZero = c.queries wDdhGdh wsZero := by
  simp [wrapSim, Comp.queries]

theorem gdhHandle_chalQueries (S : Setup) (K : Nat) :
    (gdhHandle S K).queries wDdhGdh wsZero = 4 * K := by
  simp [gdhHandle, initPrinGdhB, genSpkGdhB, genOpkGdhB, initiateGdhB,
    finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB, roParsedC, roRawFallbackC,
    registerGdhB, Comp.queries]

theorem gdhFinish_chalQueries (S : Setup) (K : Nat) :
    (gdhFinish S K).queries wDdhGdh wsZero = K + (min K S.N_dh) + (min K S.N_sess_tot) := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, letV_queries, bindV_queries, caseOptV_queries,
    findMV_queries, mapMV_queries, foldMV_queries, ddhQ_queries_wDdhGdh,
    gPrim_queries_wDdhGdh, Comp.queries, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero, Nat.zero_add, Nat.max_zero, max_self]
  omega

theorem initAdv4_chalQueries (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    (initAdv4 S U V).queries wDdhGdh wsZero = 0 := by
  simp [initAdv4, Comp.queries]

theorem fgKeyIndGapDhProg_init_chalQueries (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.queries wDdhGdh wsZero = 0 := by
  simp [fgKeyIndGapDhProg, initAdv4_chalQueries, Comp.queries]

/-! ## Primitive Query Upper Bounds (`wPrimGdh`) -/

@[simp] theorem findHonestC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) := by
  simp [findHonestC, Comp.queriesUB, Nat.mul_comm]

@[simp] theorem isGameSpkC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) := by
  simp [isGameSpkC, Comp.queriesUB, Nat.mul_comm]

@[simp] theorem isGameOpkC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) := by
  simp [isGameOpkC, Comp.queriesUB, Nat.mul_comm]

@[simp] theorem koskSenderOkPowsC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) + 1 := by
  simp [koskSenderOkPowsC, Comp.queriesUB]

@[simp] theorem koskBundleOkPowsC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queriesUB wPrimBase wsZeroBase = 6 * (min K S.N_dh) + 3 := by
  simp only [koskBundleOkPowsC, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB,
    findHonestC_primUB, isGameSpkC_primUB, isGameOpkC_primUB, qPow8_queriesUB,
    Comp.queriesUB]
  omega

@[simp] theorem lookupSpkSkC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (spkPk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows spkPk).queriesUB wPrimBase wsZeroBase = (min K S.N_dh) + 1 := by
  simp only [lookupSpkSkC, letV_queriesUB, bindV_queriesUB, findMV_queriesUB,
    qPow8_queriesUB, Comp.queriesUB]
  omega

@[simp] theorem resolveSigPkC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) := by
  simp [resolveSigPkC, Comp.queriesUB]

@[simp] theorem honestPeerC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queriesUB wPrimBase wsZeroBase = 2 * (min K S.N_dh) := by
  simp [honestPeerC, Comp.queriesUB]

@[simp] theorem checkProvC_primUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) :
    (checkProvC S K (Δ := Δ) st bu).queriesUB wPrimBase wsZeroBase = 6 * (min K S.N_dh) := by
  simp only [checkProvC, bindV_queriesUB, letV_queriesUB, caseOptV_queriesUB,
    anyMV_queriesUB, findHonestC_primUB, qPow8_queriesUB, Comp.queriesUB]
  omega

@[simp] theorem partnerC_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).queriesUB wPrimBase wsZeroBase = 8 := by
  simp [partnerC, Comp.queriesUB]

@[simp] theorem chooseRespRandC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queriesUB wPrimGdh wsZero = 8 * (min K S.N_dh) := by
  simp [chooseRespRandC, Comp.queriesUB, Nat.mul_comm]

@[simp] theorem chooseInitRandC_primUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queriesUB wPrimGdh wsZero = 8 * (min K S.N_sess_tot) := by
  simp [chooseInitRandC, Comp.queriesUB, Nat.mul_comm]

@[simp] theorem mkSecretPosC_primUB {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) :
    (mkSecretPosC z).queriesUB wPrimGdh wsZero = 1 := by
  simp [mkSecretPosC, Comp.queriesUB]

@[simp] theorem mkPairPosC_primUB {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (mkPairPosC pk1 pk2).queriesUB wPrimGdh wsZero = 2 := by
  simp [mkPairPosC, Comp.queriesUB]

@[simp] theorem computePosC_primUB {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queriesUB wPrimGdh wsZero = 6 := by
  simp [computePosC, Comp.queriesUB]

@[simp] theorem computeOptPosInitC_primUB {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queriesUB wPrimGdh wsZero = 6 := by
  simp [computeOptPosInitC, Comp.queriesUB]

@[simp] theorem ddhEqC_primUB {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queriesUB wPrimGdh wsZero = 0 := by
  simp [ddhEqC, Comp.queriesUB]

@[simp] theorem ddhEqOptC_primUB {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queriesUB wPrimGdh wsZero = 0 := by
  simp [ddhEqOptC, Comp.queriesUB]

@[simp] theorem entryMatchesC_primUB {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queriesUB wPrimGdh wsZero = 0 := by
  simp [entryMatchesC, Comp.queriesUB]

@[simp] theorem fgPatchC_primUB (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queriesUB wPrimGdh wsZero = 0 := by
  simp [fgPatchC, Comp.queriesUB]

@[simp] theorem wrapBase_primUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimBase wsZeroBase := by
  simp [wrapBase, Comp.queriesUB]

@[simp] theorem wrapSim_primUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).queriesUB wPrimGdh wsZero = c.queriesUB wPrimGdh wsZero := by
  simp [wrapSim, Comp.queriesUB]

theorem gdhHandle_primUB (S : Setup) (K : Nat) :
    (gdhHandle S K).queriesUB wPrimGdh wsZero =
      153 + 72 * (min K S.N_dh) + 16 * (min K S.N_sess_tot) := by
  simp only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB, genOpkGdhB,
    initiateGdhB, finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase_primUB, wrapSim_primUB,
    letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB, caseSumV_queriesUB,
    gPrim_queriesUB_wPrimGdh, koskBundleOkPowsC_primUB, koskSenderOkPowsC_primUB,
    resolveSigPkC_primUB, lookupSpkSkC_primUB, honestPeerC_primUB, checkProvC_primUB,
    findHonestC_primUB, chooseInitRandC_primUB, chooseRespRandC_primUB,
    computePosC_primUB, computeOptPosInitC_primUB, mkSecretPosC_primUB, fgPatchC_primUB,
    sBytes32_queriesUB, sRandom64_queriesUB, sDrKey96_queriesUB,
    qX25519_queriesUB, qX25519Base_queriesUB, qIsCanonical_queriesUB, qPow8_queriesUB,
    qSigPkGen_queriesUB, qSigSign_queriesUB, qSigVerify_queriesUB,
    qKemKeyGen_queriesUB, qKemEncaps_queriesUB, qKemDecaps_queriesUB,
    Comp.queriesUB]
  ring

theorem gdhFinish_primUB (S : Setup) (K : Nat) :
    (gdhFinish S K).queriesUB wPrimGdh wsZero = 3 * (min K S.N_dh) + (min K S.N_sess_tot) := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC, letV_queriesUB, bindV_queriesUB, caseOptV_queriesUB,
    findMV_queriesUB, mapMV_queriesUB, foldMV_queriesUB,
    ddhQ_queriesUB_wPrimGdh, gPrim_queriesUB_wPrimGdh,
    qPow8_queriesUB, qX25519_queriesUB, Comp.queriesUB]
  ring

theorem initAdv4_primQueries (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    (initAdv4 S U V).queries wPrimGdh wsZero = 0 := by
  simp [initAdv4, Comp.queries]

theorem fgKeyIndGapDhProg_init_primQueries (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.queries wPrimGdh wsZero = 0 := by
  simp [fgKeyIndGapDhProg, initAdv4_primQueries, Comp.queries]

/-! ## Modular `costUB` Lemmas for Helpers and Branches -/

@[simp] theorem fePos1_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (fePos1 e).costUB = e.costUB + 1 := rfl
@[simp] theorem fePos2_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (fePos2 e).costUB = e.costUB + 2 := rfl
@[simp] theorem fePos3_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (fePos3 e).costUB = e.costUB + 3 := rfl
@[simp] theorem fePos4_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (fePos4 e).costUB = e.costUB + 4 := rfl
@[simp] theorem feSs_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (feSs e).costUB = e.costUB + 5 := rfl
@[simp] theorem feDk_costUB {Γ : List PT} (e : Expr pqxdhOps Γ fgPatchEntryTy) :
    (feDk e).costUB = e.costUB + 5 := rfl

@[simp] theorem paU_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paU p).costUB = p.costUB + 1 := rfl
@[simp] theorem paV_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paV p).costUB = p.costUB + 2 := rfl
@[simp] theorem paUp_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paUp p).costUB = p.costUB + 3 := rfl
@[simp] theorem paPrinFlag_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paPrinFlag p).costUB = p.costUB + 4 := rfl
@[simp] theorem paPrinIdx_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paPrinIdx p).costUB = p.costUB + 5 := rfl
@[simp] theorem paDhFlag_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paDhFlag p).costUB = p.costUB + 6 := rfl
@[simp] theorem paEphIdx_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paEphIdx p).costUB = p.costUB + 7 := rfl
@[simp] theorem paSpkIdx_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paSpkIdx p).costUB = p.costUB + 8 := rfl
@[simp] theorem paOpkMode_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paOpkMode p).costUB = p.costUB + 9 := rfl
@[simp] theorem paOpkIdx_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paOpkIdx p).costUB = p.costUB + 10 := rfl
@[simp] theorem paMode_costUB {Γ : List PT} (p : Expr pqxdhOps Γ paramsTy) :
    (paMode p).costUB = p.costUB + 10 := rfl

@[simp] theorem smBase_costUB {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    (smBase s).costUB = s.costUB + 1 := rfl
@[simp] theorem smFgL_costUB {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    (smFgL s).costUB = s.costUB + 2 := rfl
@[simp] theorem smRaw_costUB {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    (smRaw s).costUB = s.costUB + 3 := rfl
@[simp] theorem smLog_costUB {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    (smLog s).costUB = s.costUB + 4 := rfl
@[simp] theorem smPows_costUB {Γ : List PT} (s : Expr pqxdhOps Γ simTy) :
    (smPows s).costUB = s.costUB + 4 := rfl

@[simp] theorem encEC_costUB {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (encEC e).costUB = e.costUB + 33 := rfl

@[simp] theorem encKEM_costUB {Γ : List PT} (e : Expr pqxdhOps Γ (B 1568)) :
    (encKEM e).costUB = e.costUB + 1569 := rfl

@[simp] theorem mkSecretPosC_costUB {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) :
    (mkSecretPosC z).costUB = z.costUB + 42 := by
  simp only [mkSecretPosC, letV_costUB, bindV_costUB, gPrim_costUB,
    qIsCanonical_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[simp] theorem mkPairPosC_costUB {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (mkPairPosC pk1 pk2).costUB = pk1.costUB + pk2.costUB + 150 := by
  simp only [mkPairPosC, letV_costUB, bindV_costUB, gPrim_costUB,
    qPow8_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[simp] theorem computePosC_costUB {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) :
    (computePosC sk1 sk2 pk1 pk2).costUB =
      2 * sk1.costUB + 2 * sk2.costUB + 2 * pk1.costUB + 2 * pk2.costUB + 454 := by
  simp only [computePosC, natEq, lenB_costUB, PNat.val_ofNat, bits_32, bits_0,
    bindV_costUB, gPrim_costUB, qX25519_costUB, mkSecretPosC_costUB,
    mkPairPosC_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem computeOptPosInitC_costUB {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32))
    (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).costUB =
      sk1.costUB + pk1.costUB + opkB?.costUB + 549 := by
  simp only [computeOptPosInitC, letV_costUB, caseOptV_costUB, bindV_costUB,
    computePosC_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
    List.length_nil, PNat.val_ofNat]
  ring

@[simp] theorem ddhEqC_costUB {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).costUB = p1.costUB + p2.costUB + 601 := by
  simp only [ddhEqC, orE, letV_costUB, caseSumV_costUB, eqB_costUB, ddhQ_costUB,
    v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat]

@[simp] theorem ddhEqOptC_costUB {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).costUB = p1?.costUB + p2?.costUB + 621 := by
  simp only [ddhEqOptC, letV_costUB, caseOptV_costUB, ddhEqC_costUB,
    v_costUB, Comp.costUB, Expr.costUB]

@[simp] theorem entryMatchesC_costUB {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).costUB = 2530 := by
  simp only [entryMatchesC, bindV_costUB, ddhEqC_costUB, ddhEqOptC_costUB,
    fePos1_costUB, fePos2_costUB, fePos3_costUB, fePos4_costUB, feSs_costUB,
    eqB_costUB, v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat]

@[simp] theorem fgPatchC_costUB (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).costUB = fgL.costUB + 2531 * K + 131 := by
  simp only [fgPatchC, feMk, letV_costUB, bindV_costUB, findMV_costUB, caseOptV_costUB,
    entryMatchesC_costUB, gPrim_costUB, sDrKey96_costUB, feDk_costUB,
    v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem findHonestC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).costUB = ik.costUB + 206 * (min K S.N_dh) + 6 := by
  simp only [findHonestC, stPrin, peIkAPk, letV_costUB, findMV_costUB,
    bindV_costUB, qPow8_costUB, eqB_costUB, v_costUB, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  ring

@[simp] theorem isGameSpkC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).costUB = pk.costUB + 206 * (min K S.N_dh) + 7 := by
  simp only [isGameSpkC, stSpks, sbSpkPk, letV_costUB, anyMV_costUB,
    bindV_costUB, qPow8_costUB, eqB_costUB, v_costUB, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  ring

@[simp] theorem isGameOpkC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).costUB = pk.costUB + 206 * (min K S.N_dh) + 8 := by
  simp only [isGameOpkC, stOpks, oeOpkPk, letV_costUB, anyMV_costUB,
    bindV_costUB, qPow8_costUB, eqB_costUB, v_costUB, Comp.costUB, Expr.costUB,
    PNat.val_ofNat]
  ring

@[simp] theorem isAdvPowsE_costUB (K : Nat) {Γ : List PT}
    (pows : Expr pqxdhOps Γ (.list (.prod (B 32) (B 32)))) (wPk : Expr pqxdhOps Γ (B 32)) :
    (isAdvPowsE K pows wPk).costUB = pows.costUB + wPk.costUB + 70 * K + 5 := by
  simp only [isAdvPowsE, eLet_costUB, eAny_costUB, eqB_costUB,
    v_costUB, Expr.costUB, PNat.val_ofNat]
  ring

@[simp] theorem koskSenderOkPowsC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).costUB =
      pows.costUB + ik.costUB + 206 * (min K S.N_dh) + 70 * K + 95 := by
  simp only [koskSenderOkPowsC, orE, isSomeE, letV_costUB, bindV_costUB,
    findHonestC_costUB, qPow8_costUB, isAdvPowsE_costUB,
    v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem koskBundleOkPowsC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).costUB =
      pows.costUB + 618 * (min K S.N_dh) + 210 * K + 288 := by
  simp only [koskBundleOkPowsC, buIkB, buSpkB, buOpkB, orE, isSomeE,
    letV_costUB, bindV_costUB, caseOptV_costUB,
    findHonestC_costUB, isGameSpkC_costUB, isGameOpkC_costUB,
    qPow8_costUB, isAdvPowsE_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem lookupSpkSkC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (spkPk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows spkPk).costUB =
      pows.costUB + spkPk.costUB + 139 * (min K S.N_dh) + 69 * K + 122 := by
  simp only [lookupSpkSkC, stSpks, sbSpkPk, sbSpkSk, letV_costUB, bindV_costUB,
    findMV_costUB, eCaseOpt_costUB, eFind_costUB, qPow8_costUB, eqB_costUB, litB_costUB,
    v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  ring

@[simp] theorem resolveSigPkC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).costUB = ik.costUB + 206 * (min K S.N_dh) + 20 := by
  simp only [resolveSigPkC, peIkSignPk, letV_costUB, bindV_costUB,
    findHonestC_costUB, eCaseOpt_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem honestPeerC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).costUB = ik.costUB + 206 * (min K S.N_dh) + 23 := by
  simp only [honestPeerC, peCorrupted, bindV_costUB, findHonestC_costUB,
    eCaseOpt_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[simp] theorem checkProvC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) :
    (checkProvC S K (Δ := Δ) st bu).costUB = 636 * (min K S.N_dh) + 3160 * K + 52 := by
  simp only [checkProvC, buIkB, buSpkB, buPqspkB, buOpkB, stSpks, stOpks,
    sbSpkPk, sbPqspkPk, oeOpkPk, natEq,
    bindV_costUB, letV_costUB, caseOptV_costUB, anyMV_costUB, eAny_costUB,
    findHonestC_costUB, qPow8_costUB, eqB_costUB,
    v_costUB, Comp.costUB, Expr.costUB, PNat.val_ofNat]
  ring

@[simp] theorem partnerC_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).costUB = 7370 := by
  simp only [partnerC, seHdr, reHdr, sePeerIk, reRespIk, sePeerSpk, reSpk,
    sePeerOpk, reOpk, sePeerPqspk, rePqspk, hdIkAPk, hdEkAPk, hdKemCt,
    getDBytes, optBytesEq, eLet2, bindV_costUB, eCaseOpt_costUB, eLet_costUB,
    qPow8_costUB, eqB_costUB, litB_costUB, v_costUB, Comp.costUB, Expr.costUB,
    List.length_nil, PNat.val_ofNat]

@[simp] theorem chooseRespRandC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).costUB = 7371 * (min K S.N_dh) + 123 := by
  simp only [chooseRespRandC, stSess, seDrRand, bindV_costUB, caseOptV_costUB,
    gPrim_costUB, findMV_costUB, partnerC_costUB, sDrKey96_costUB,
    v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem chooseInitRandC_costUB (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).costUB = 7371 * (min K S.N_sess_tot) + 120 := by
  simp only [chooseInitRandC, stResps, reDrRand, bindV_costUB, caseOptV_costUB,
    gPrim_costUB, findMV_costUB, partnerC_costUB, sDrKey96_costUB,
    v_costUB, Comp.costUB, Expr.costUB]
  ring

section CostUBAccessors

variable {Γ : List PT}

@[simp] theorem rNone_costUB : (rNone (Γ := Γ)).costUB = 2 := rfl
@[simp] theorem rInitPrin_costUB (ik s : Expr pqxdhOps Γ (B 32)) : (rInitPrin ik s).costUB = ik.costUB + s.costUB + 3 := rfl
@[simp] theorem rPk_costUB (pk : Expr pqxdhOps Γ (B 32)) : (rPk pk).costUB = pk.costUB + 3 := rfl
@[simp] theorem rCorr_costUB (ik s : Expr pqxdhOps Γ (B 32)) : (rCorr ik s).costUB = ik.costUB + s.costUB + 5 := rfl
@[simp] theorem rBundle_costUB (b : Expr pqxdhOps Γ bundleT) : (rBundle b).costUB = b.costUB + 5 := rfl
@[simp] theorem rHdr_costUB (h : Expr pqxdhOps Γ hdrT) : (rHdr h).costUB = h.costUB + 6 := rfl
@[simp] theorem rInitUnfresh_costUB (dk : Expr pqxdhOps Γ drKeyT) (h : Expr pqxdhOps Γ hdrT) :
    (rInitUnfresh dk h).costUB = dk.costUB + h.costUB + 8 := rfl
@[simp] theorem rAccFresh_costUB : (rAccFresh (Γ := Γ)).costUB = 9 := rfl
@[simp] theorem rDrKey_costUB (dk : Expr pqxdhOps Γ drKeyT) : (rDrKey dk).costUB = dk.costUB + 9 := rfl
@[simp] theorem rSpkSk_costUB (sk : Expr pqxdhOps Γ (B 32)) : (rSpkSk sk).costUB = sk.costUB + 10 := rfl

@[simp] theorem qK_costUB (e : Expr pqxdhOps Γ accQTy) : (qK e).costUB = e.costUB + 1 := rfl
@[simp] theorem qJ_costUB (e : Expr pqxdhOps Γ accQTy) : (qJ e).costUB = e.costUB + 2 := rfl
@[simp] theorem qO_costUB (e : Expr pqxdhOps Γ accQTy) : (qO e).costUB = e.costUB + 3 := rfl
@[simp] theorem qHdr_costUB (e : Expr pqxdhOps Γ accQTy) : (qHdr e).costUB = e.costUB + 3 := rfl
@[simp] theorem slice32_costUB (off : Nat) (bs : Expr pqxdhOps Γ (B 192)) :
    (slice32 off bs).costUB = bs.costUB + bits off + 418 := by
  simp only [slice32, takeKB_costUB, dropB_costUB, Expr.costUB, PNat.val_ofNat]; ring

end CostUBAccessors

@[simp] theorem wrapSim_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).costUB = c.costUB + 9 := rfl

@[simp] theorem wrapBase_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

@[simp] theorem finishAcceptGdhC_costUB (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).costUB =
      opkPkOpt.costUB + opks'.costUB + usedO'.costUB + usedN'.costUB + kyb'.costUB +
        7577 * (min K S.N_dh) + 401 := by
  cases hasOpk <;> (
    simp only [finishAcceptGdhC, stUpd, stMk, reUpd, reMk, smUpd, smMk, qKJO, isSomeE,
      letV_costUB, bindV_costUB, eCaseOpt_costUB, gPrim_costUB,
      findHonestC_costUB, chooseRespRandC_costUB,
      smRaw_costUB, smLog_costUB, smPows_costUB,
      qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
      rDrKey_costUB, rAccFresh_costUB, v_costUB, Comp.costUB, Expr.costUB,
      ↓reduceIte, Bool.false_eq_true]
    ring)

@[simp] theorem logFindC_costUB (K off : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) :
    (logFindC (Δ := Δ) K off pa sm).costUB = K * (bits off + 526) + 77 := by
  simp only [logFindC, slice32_costUB, smLog_costUB, paU_costUB, paV_costUB,
    bindV_costUB, findMV_costUB, eMap_costUB, eCaseOpt_costUB, ddhQ_costUB, litB_costUB,
    v_costUB, Comp.costUB, List.length_replicate, PNat.val_ofNat]
  ring

@[simp] theorem spkPowsC_costUB (S : Setup) (K : Nat) {Γ : List PT}
    (spks : Expr pqxdhOps Γ (.list (.prod (.prod .nat .nat) spkBundleEntryTy))) :
    (spkPowsC S K spks).costUB = spks.costUB + 77 * (min K S.N_dh) + 1 := by
  simp only [spkPowsC, mapMV_costUB, bindV_costUB, gPrim_costUB, qPow8_costUB,
    v_costUB, Comp.costUB, Expr.costUB]
  ring

@[simp] theorem lookupFromPowsE_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spkPows : Var Γ₁ (.list (.prod (B 32) (B 32))))
    (advPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (wSpk : Var Δ (B 32)) :
    (lookupFromPowsE S K spkPows advPows wSpk).costUB = 69 * (min K S.N_dh) + 69 * K + 43 := by
  simp only [lookupFromPowsE, eCaseOpt_costUB, eFind_costUB, eqB_costUB, litB_costUB,
    v_costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  ring

@[simp] theorem initDh1CandC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spkPows : Var Γ₁ (.list (.prod (B 32) (B 32))))
    (advPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Δ keyIndSessionEntryTy) :
    (initDh1CandC S K spkPows advPows s).costUB = 69 * (min K S.N_dh) + 69 * K + 228 := by
  simp only [initDh1CandC, bindV_costUB, gPrim_costUB, qPow8_costUB, qX25519_costUB,
    lookupFromPowsE_costUB, v_costUB, Expr.costUB]
  ring

@[simp] theorem respDh1CandC_costUB (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (spks : Var Γ₁ (.list (.prod (.prod .nat .nat) spkBundleEntryTy)))
    (r : Var Γ₂ keyIndRespEntryTy) :
    (respDh1CandC (Δ := Δ) S K spks r).costUB = 66 * (min K S.N_dh) + 145 := by
  simp only [respDh1CandC, respBundleKeyE, nat2Eq, natEq, gPrim_costUB, qX25519_costUB,
    eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, litB_costUB,
    v_costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0]
  ring

@[simp] theorem findMapStepC_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (acc : Var Γ₂ (.opt (B 32)))
    (cand : Comp pqxdhOps pqGapDhIface Δ (B 32)) :
    (findMapStepC pa acc cand).costUB = cand.costUB + 117 := by
  simp only [findMapStepC, caseOptV_costUB, bindV_costUB, ddhQ_costUB,
    paU_costUB, paV_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

set_option maxRecDepth 100000 in
theorem gdhHandle_costUB (S : Setup) (K : Nat) :
    (gdhHandle S K).costUB =
      28015 * K + 27165 * (min K S.N_dh) + 14742 * (min K S.N_sess_tot) +
        2 * bits (S.N_recv.min S.N_spk_tot) + bits (S.N_opk.min S.N_opk_tot) +
        2 * bits (S.N_send_opk.min S.N_send_opk_tot) + 2 * bits S.N_send_opk_tot +
        2 * bits (S.N_send_no_opk.min S.N_send_no_opk_tot) + 2 * bits S.N_send_tot +
        60850 := by
  simp only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB, genOpkGdhB,
    initiateGdhB, finishAcceptGdhC_costUB, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase_costUB, wrapSim_costUB,
    stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
    smMk, smUpd, qKJO, rs, slice32_costUB,
    qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
    rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
    rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    paU_costUB, paV_costUB, paUp_costUB, paPrinFlag_costUB, paPrinIdx_costUB,
    paDhFlag_costUB, paEphIdx_costUB, paSpkIdx_costUB, paOpkMode_costUB, paOpkIdx_costUB,
    spkFlatIdxE, opkFlatIdxE, initSlotIdxE, initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
    mulRight, eLet2, reMk,
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
  ring

theorem gdhFinish_costUB (S : Setup) (K : Nat) :
    (gdhFinish S K).costUB =
      69 * (min K S.N_dh) ^ 2 + 69 * K * (min K S.N_dh) + 66 * (min K S.N_dh) * (min K S.N_sess_tot) +
        423 * (min K S.N_dh) + 263 * (min K S.N_sess_tot) + 2132 * K + 409 := by
  simp only [gdhFinish, extractMode0C, logFindC_costUB, spkPowsC_costUB, findMapStepC_costUB,
    initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
    smBase_costUB, smLog_costUB, smPows_costUB, paU_costUB, paV_costUB, paMode_costUB,
    natEq,
    letV_costUB, bindV_costUB, caseOptV_costUB,
    findMV_costUB, foldMV_costUB,
    eCaseOpt_costUB, eMap_costUB,
    ddhQ_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB,
    List.length_replicate, PNat.val_ofNat,
    bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
  ring

theorem initAdv4_costUB (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    (initAdv4 S U V).costUB =
      U.costUB + V.costUB + bits (fgTotalIndexCount S) +
        4 * bits (S.N_id * S.N_spk_tot) + 8 * bits S.N_spk_tot +
        5 * bits S.N_opk_tot +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) +
        3 * bits S.N_id + 154 := by
  simp only [initAdv4, initParamsFlat, initParamsDh, initParamsIk, initParamsOpk,
    paMk, emptySimE, smMk, emptyStE, stMk,
    letV_costUB, bindV_costUB, gPrim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
    Comp.costUB, Expr.costUB, bits_0, bits_1, bits_2, bits_3]
  ring

/-! ## `totalCost`, `totalQueries`, and Query-Bound Soundness for `fgKeyIndGapDhProg` -/

theorem gdhHandle_cost_le_min (S : Setup) (K : Nat) :
    (gdhHandle S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 11 * bits S.N_dh +
        60850 := by
  have h := (gdhHandle S K).cost_le_costUB
  rw [gdhHandle_costUB] at h
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have c1 := bits_mono (show S.N_recv.min S.N_spk_tot ≤ S.N_dh from le_trans (Nat.min_le_right _ _) (by omega))
  have c2 := bits_mono (show S.N_opk.min S.N_opk_tot ≤ S.N_dh from le_trans (Nat.min_le_right _ _) (by omega))
  have c3 := bits_mono (show S.N_send_opk.min S.N_send_opk_tot ≤ S.N_dh from le_trans (Nat.min_le_right _ _) (by omega))
  have c4 := bits_mono (show S.N_send_opk_tot ≤ S.N_dh by omega)
  have c5 := bits_mono (show S.N_send_no_opk.min S.N_send_no_opk_tot ≤ S.N_dh from le_trans (Nat.min_le_right _ _) (by omega))
  have c6 := bits_mono (show S.N_send_tot ≤ S.N_dh by omega)
  omega

theorem gdhHandle_cost_le (S : Setup) (K : Nat) :
    (gdhHandle S K).cost ≤ 28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60861 := by
  have h := (gdhHandle S K).cost_le_costUB
  rw [gdhHandle_costUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have b1 := bits_le_succ (S.N_recv.min S.N_spk_tot)
  have b2 := bits_le_succ (S.N_opk.min S.N_opk_tot)
  have b3 := bits_le_succ (S.N_send_opk.min S.N_send_opk_tot)
  have b4 := bits_le_succ S.N_send_opk_tot
  have b5 := bits_le_succ (S.N_send_no_opk.min S.N_send_no_opk_tot)
  have b6 := bits_le_succ S.N_send_tot
  have m1 : S.N_recv.min S.N_spk_tot ≤ S.N_spk_tot := Nat.min_le_right _ _
  have m2 : S.N_opk.min S.N_opk_tot ≤ S.N_opk_tot := Nat.min_le_right _ _
  have m3 : S.N_send_opk.min S.N_send_opk_tot ≤ S.N_send_opk_tot := Nat.min_le_right _ _
  have m4 : S.N_send_no_opk.min S.N_send_no_opk_tot ≤ S.N_send_no_opk_tot := Nat.min_le_right _ _
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  omega

theorem gdhFinish_cost_le_min (S : Setup) (K : Nat) :
    (gdhFinish S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * (min K S.N_dh) +
        66 * (min K S.N_dh) * (min K S.N_sess_tot) +
        423 * (min K S.N_dh) + 263 * (min K S.N_sess_tot) + 2132 * K + 409 := by
  have h := (gdhFinish S K).cost_le_costUB
  rw [gdhFinish_costUB] at h
  exact h

theorem gdhFinish_cost_le (S : Setup) (K : Nat) :
    (gdhFinish S K).cost ≤
      69 * S.N_dh ^ 2 + 69 * K * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        423 * S.N_dh + 263 * S.N_sess_tot + 2132 * K + 409 := by
  refine (gdhFinish_cost_le_min S K).trans ?_
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  gcongr

theorem fgKeyIndGapDhProg_init_costUB (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.costUB =
      bits (fgTotalIndexCount S) +
        4 * bits (S.N_id * S.N_spk_tot) + 8 * bits S.N_spk_tot +
        5 * bits S.N_opk_tot +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) +
        3 * bits S.N_id + 163 := by
  simp only [fgKeyIndGapDhProg, bindV_costUB, initAdv4_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

theorem fgKeyIndGapDhProg_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.cost ≤ 26 * S.N_dh ^ 2 + 16 * S.N_dh + 190 := by
  have h := (fgKeyIndGapDhProg S K).init.cost_le_costUB
  rw [fgKeyIndGapDhProg_init_costUB] at h
  have b1 := bits_le_succ (fgTotalIndexCount S)
  have b2 := bits_le_succ (S.N_id * S.N_spk_tot)
  have b3 := bits_le_succ S.N_spk_tot
  have b4 := bits_le_succ S.N_opk_tot
  have b5 := bits_le_succ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)
  have b6 := bits_le_succ
    (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id)
  have b7 := bits_le_succ S.N_id
  have hfg : fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]

theorem fgKeyIndGapDhProg_init_cost_le_log (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).init.cost ≤ 38 * bits S.N_dh + 200 := by
  have h := (fgKeyIndGapDhProg S K).init.cost_le_costUB
  rw [fgKeyIndGapDhProg_init_costUB] at h
  have hfg : fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh → bits x ≤ 2 * bits S.N_dh + 1 := by
    intro x hx
    exact le_trans (bits_mono hx) (by
      have hm := bits_mul S.N_dh S.N_dh
      omega)
  have b1 : bits (fgTotalIndexCount S) ≤ 2 * bits S.N_dh + 1 :=
    hsq _ (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
  have b2 : bits (S.N_id * S.N_spk_tot) ≤ 2 * bits S.N_dh + 1 := hsq _ (by nlinarith)
  have b3 : bits S.N_spk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have b4 : bits S.N_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have b5 : bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) ≤ 2 * bits S.N_dh + 1 :=
    hsq _ (by nlinarith)
  have b6 : bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) ≤
      2 * bits S.N_dh + 1 :=
    hsq _ (by nlinarith)
  have b7 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
  omega

theorem fgKeyIndGapDhProg_totalCost_poly_le_min (S : Setup) (K q : Nat) :
    (fgKeyIndGapDhProg S K).totalCost q ≤
      q * (28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot +
        11 * bits S.N_dh + 60882) +
        69 * (min K S.N_dh) ^ 2 + 69 * K * min K S.N_dh +
        66 * min K S.N_dh * min K S.N_sess_tot +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot +
        38 * bits S.N_dh + 2132 * K + 609 := by
  have hI := fgKeyIndGapDhProg_init_cost_le_log S K
  have hH := gdhHandle_cost_le_min S K
  have hF := gdhFinish_cost_le_min S K
  have hmax : max 1 ((gdhHandle S K).cost + 32) ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot +
        11 * bits S.N_dh + 60882 := by omega
  have hq := Nat.mul_le_mul_left q hmax
  change (fgKeyIndGapDhProg S K).init.cost + q * max 1 ((gdhHandle S K).cost + 32) +
    (gdhFinish S K).cost ≤ _
  linarith

theorem fgKeyIndGapDhProg_totalCost_poly_le (S : Setup) (K q : Nat) :
    (fgKeyIndGapDhProg S K).totalCost q ≤
      q * (28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60893) +
        95 * S.N_dh ^ 2 + 69 * K * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        439 * S.N_dh + 263 * S.N_sess_tot + 2132 * K + 599 := by
  have hI := fgKeyIndGapDhProg_init_cost_le S K
  have hH := gdhHandle_cost_le S K
  have hF := gdhFinish_cost_le S K
  have hmax : max 1 ((gdhHandle S K).cost + 32) ≤
      28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60893 := by omega
  have hq : q * max 1 ((gdhHandle S K).cost + 32) ≤
      q * (28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60893) :=
    Nat.mul_le_mul_left q hmax
  change (fgKeyIndGapDhProg S K).init.cost + q * max 1 ((gdhHandle S K).cost + 32) +
    (gdhFinish S K).cost ≤ _
  linarith

/-- Syntactic step-cost bound `stepCostBudget S b` for `(fgKeyIndGapDhProg S b.q_total).totalCost b.q_total`. -/
theorem fgKeyIndGapDhProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDhProg S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  refine (fgKeyIndGapDhProg_totalCost_poly_le_min S b.q_total b.q_total).trans ?_
  have hbits : bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits]
  dsimp only [stepCostBudget, _root_.SignalPqxdh.Security.stepCostBudget]
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hdiff :
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (md + ms) +
        2 ^ 10 * (q + 1) * (ld + ls) + 2 ^ 11 * md ^ 2 + 2 ^ 8 * md * ms =
      (q * (28015 * q + 27165 * md + 14742 * ms + 11 * (ld + 1) + 60882) +
        69 * md ^ 2 + 69 * q * md + 66 * md * ms + 423 * md + 263 * ms +
        38 * (ld + 1) + 2132 * q + 609) +
      (37521 * q ^ 2 + 68047 * q + 64889 + 5534 * q * md + 32345 * md +
        18026 * q * ms + 32505 * ms + 1013 * q * ld + 986 * ld +
        1024 * q * ls + 1024 * ls + 1979 * md ^ 2 + 190 * md * ms) := by ring
  omega

theorem gdhHandle_primQueries_le (S : Setup) (K : Nat) :
    (gdhHandle S K).queries wPrimGdh wsZero ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhHandle S K)
  rw [gdhHandle_primUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

theorem gdhFinish_primQueries_le (S : Setup) (K : Nat) :
    (gdhFinish S K).queries wPrimGdh wsZero ≤ 3 * S.N_dh + S.N_sess_tot := by
  have h := Comp.queries_le_queriesUB wPrimGdh wsZero (gdhFinish S K)
  rw [gdhFinish_primUB] at h
  have md : min K S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min K S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  omega

theorem fgKeyIndGapDhProg_totalPrimQueries_poly_le (S : Setup) (K q : Nat) :
    (fgKeyIndGapDhProg S K).totalQueries wPrimGdh wsZero q ≤
      q * (153 + 72 * S.N_dh + 16 * S.N_sess_tot) + 3 * S.N_dh + S.N_sess_tot := by
  simp only [CostedReduction.totalQueries, fgKeyIndGapDhProg_init_primQueries]
  have hH := Nat.mul_le_mul_left q (gdhHandle_primQueries_le S K)
  have hF := gdhFinish_primQueries_le S K
  change 0 + q * (gdhHandle S K).queries wPrimGdh wsZero +
    (gdhFinish S K).queries wPrimGdh wsZero ≤ _
  omega

theorem fgKeyIndGapDhProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDhProg S b.q_total).totalQueries wPrimGdh wsZero b.q_total ≤
      primQueryBudget S b := by
  have hp := fgKeyIndGapDhProg_totalPrimQueries_poly_le S b.q_total b.q_total
  unfold primQueryBudget
  nlinarith

theorem fgKeyIndGapDhProg_totalChalQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyIndGapDhProg S K).totalQueries wDdhGdh wsZero q =
      4 * q * K + K + min K S.N_dh + min K S.N_sess_tot := by
  simp only [CostedReduction.totalQueries, fgKeyIndGapDhProg_init_chalQueries]
  change 0 + q * (gdhHandle S K).queries wDdhGdh wsZero +
    (gdhFinish S K).queries wDdhGdh wsZero = _
  rw [gdhHandle_chalQueries, gdhFinish_chalQueries]
  ring

theorem fgKeyIndGapDhProg_totalChalQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDhProg S b.q_total).totalQueries wDdhGdh wsZero b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [fgKeyIndGapDhProg_totalChalQueries_eq]
  have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  nlinarith

theorem fgKeyIndGapDhProg_chalBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyIndGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => q.isRight = true) (4 * q * K + K + min K S.N_dh + min K S.N_sess_tot) := by
  rw [← fgKeyIndGapDhProg_totalChalQueries_eq S K q]
  refine CostedReduction.queryBound_eval (fgKeyIndGapDhProg S K) (fun q => q.isRight = true)
    wDdhGdh wsZero ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqGapDhIface, pqChalIface] at hx
    | inr t => rcases t with ⟨⟩; simp [wDdhGdh]
  · intro n
    simp [pqGapDhIface, pqChalIface]

theorem fgKeyIndGapDhProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyIndGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((fgKeyIndGapDhProg S K).totalQueries wPrimGdh wsZero q) := by
  refine CostedReduction.queryBound_eval (fgKeyIndGapDhProg S K) (fun q => isPrimQuery q = true)
    wPrimGdh wsZero ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [wPrimGdh]
    | inr t => simp [pqGapDhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + gapDhDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

/-! ## Semantic Bilinear `gdhQueryBudget` Bound for `fgKeyIndGapDhProg` -/

@[expose] def isRoQ {S : Setup} : KeyIndQuery S → Bool
  | .roQuery _ => true
  | _          => false

@[expose] def isSessQ {S : Setup} : KeyIndQuery S → Bool
  | .initiateOPK _ _ _   => true
  | .initiateNoOPK _ _ _ => true
  | .acceptOPK _ _ _ _   => true
  | .acceptNoOPK _ _ _ _ => true
  | _                    => false

@[expose] def isSecPos (p : fgPosTy.denote) : Bool := p.isLeft

@[expose] def isSecOptPos : Option fgPosTy.denote → Bool
  | none   => true
  | some p => isSecPos p

/-- True iff all positions of an `fgPatchEntryTy` entry are `.secret` (`.inl _`). -/
@[expose] def isSecEntry (e : fgPatchEntryTy.denote) : Bool :=
  isSecPos e.1 && isSecPos e.2.1 && isSecPos e.2.2.1 && isSecOptPos e.2.2.2.1

@[expose] def fgRDone (fgL : List fgPatchEntryTy.denote) : ℕ := fgL.countP isSecEntry

@[expose] def fgSDone (fgL : List fgPatchEntryTy.denote) : ℕ := fgL.countP (fun e => !isSecEntry e)

/-- Potential function bounding remaining handler `ddhQ` queries given `(r, s)` existing
    all-secret / pair-containing entries in `fgL` and `(r_rem, s_rem)` remaining RO / session
    queries. -/
@[expose] def fgDdhPhi (r s r_rem s_rem : ℕ) : ℕ :=
  4 * r * s_rem + 4 * s * r_rem + 4 * r_rem * s_rem + 4 * s * s_rem + 2 * s_rem * (s_rem - 1)

theorem fgRDone_add_fgSDone (fgL : List fgPatchEntryTy.denote) :
    fgRDone fgL + fgSDone fgL = fgL.length := by
  induction fgL with
  | nil => rfl
  | cons e es ih =>
    simp only [fgRDone, fgSDone, List.countP_cons, List.length_cons] at ih ⊢
    cases isSecEntry e <;> simp <;> omega

theorem countP_take_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (K : ℕ), (xs.take K).countP p ≤ xs.countP p
  | [], _ => by simp
  | _, 0 => by simp
  | x :: xs, K + 1 => by
    simp only [List.take_succ_cons, List.countP_cons]
    have ih := countP_take_le p xs K
    cases p x <;> simp <;> omega

theorem fgDdhPhi_zero_done (r_rem s_rem : ℕ) :
    fgDdhPhi 0 0 r_rem s_rem = 4 * r_rem * s_rem + 2 * s_rem * (s_rem - 1) := by
  simp [fgDdhPhi]

theorem fgDdhPhi_mono {r₁ r₂ s r_rem₁ r_rem₂ s_rem₁ s_rem₂ : ℕ}
    (hr : r₁ ≤ r₂) (hrr : r_rem₁ ≤ r_rem₂) (hsr : s_rem₁ ≤ s_rem₂) :
    fgDdhPhi r₁ s r_rem₁ s_rem₁ ≤ fgDdhPhi r₂ s r_rem₂ s_rem₂ := by
  unfold fgDdhPhi
  have hsub : s_rem₁ - 1 ≤ s_rem₂ - 1 := by omega
  gcongr

theorem fgDdhPhi_ro_step (r s r' s_rem : ℕ) :
    4 * s + fgDdhPhi (r + 1) s r' s_rem = fgDdhPhi r s (r' + 1) s_rem := by
  unfold fgDdhPhi
  generalize s_rem - 1 = t
  ring

theorem fgDdhPhi_sess_step (r s r_rem s' : ℕ) :
    4 * (r + s) + fgDdhPhi r (s + 1) r_rem s' = fgDdhPhi r s r_rem (s' + 1) := by
  rcases s' with _ | m
  · simp [fgDdhPhi]; ring
  · simp only [fgDdhPhi, Nat.add_sub_cancel]; ring

theorem fgDdhPhi_le_sess_inc {r s r' s' : ℕ}
    (h : (r' = r ∧ s' = s) ∨ (r' = r + 1 ∧ s' = s) ∨ (r' = r ∧ s' = s + 1))
    (r_rem s_rem : ℕ) :
    fgDdhPhi r' s' r_rem s_rem ≤ fgDdhPhi r (s + 1) r_rem s_rem := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    unfold fgDdhPhi
    nlinarith
  }

/-- Joint `ddhQ` query-count bound and support postcondition on `GdhSimSpec`. -/
@[expose] def DdhStep {α : Type} (m : ℕ) (Q : α → Prop)
    (oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α) : Prop :=
  oa.IsQueryBoundP (fun q => q.isRight = true) m ∧ ∀ x ∈ support oa, Q x

theorem hwDdh : ∀ g x,
    (fun q : (PrimBaseSpec + gapDhDdhOracle.spec).Domain => q.isRight = true)
      (pqGapDhIface.enc g x) → 1 ≤ wDdhGdh g := by
  intro g x hx
  cases g with
  | inl t => simp [pqGapDhIface, pqChalIface] at hx
  | inr t => rcases t with ⟨⟩; simp [wDdhGdh]

theorem hUDdh : ∀ n,
    (pqGapDhIface.fwdU n).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  intro n
  simp [pqGapDhIface, pqChalIface]

theorem ddhStep_mono {α : Type} {m₁ m₂ : ℕ} {Q₁ Q₂ : α → Prop}
    {oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α}
    (hm : m₁ ≤ m₂) (hQ : ∀ x, Q₁ x → Q₂ x) (h : DdhStep m₁ Q₁ oa) :
    DdhStep m₂ Q₂ oa :=
  ⟨h.1.mono hm, fun x hx => hQ x (h.2 x hx)⟩

theorem ddhStep_pure {α : Type} {Q : α → Prop} (x : α) (h : Q x) :
    DdhStep 0 Q (pure x) :=
  ⟨isQueryBoundP_pure _ _ 0, fun y hy => by
    simp only [support_pure, Set.mem_singleton_iff] at hy
    rwa [hy]⟩

theorem ddhStep_ret {Γ : List PT} {τ : PT} {Q : τ.denote → Prop}
    (e : Expr pqxdhOps Γ τ) (env : Env Γ) (h : Q (e.eval env)) :
    DdhStep 0 Q ((Comp.ret (I := pqGapDhIface) e).eval env) :=
  ddhStep_pure (e.eval env) h

theorem ddhStep_bind {α β : Type} {m₁ m₂ : ℕ} {Q₁ : α → Prop} {Q₂ : β → Prop}
    {oa : OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) α}
    {k : α → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) β}
    (hoa : DdhStep m₁ Q₁ oa) (hk : ∀ x, Q₁ x → DdhStep m₂ Q₂ (k x)) :
    DdhStep (m₁ + m₂) Q₂ (oa >>= k) :=
  ⟨isQueryBoundP_bind (n := m₁) (m := m₂) hoa.1 (fun x hx => (hk x (hoa.2 x hx)).1),
   fun y hy => by
     rw [mem_support_bind_iff] at hy
     obtain ⟨x, hx, hy⟩ := hy
     exact (hk x (hoa.2 x hx)).2 y hy⟩

theorem ddhStep_bindV {Γ : List PT} {τ₁ τ₂ : PT} {m₁ m₂ : ℕ}
    {Q₁ : τ₁.denote → Prop} {Q₂ : τ₂.denote → Prop}
    (c : Comp pqxdhOps pqGapDhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ)
    (hc : DdhStep m₁ Q₁ (c.eval env))
    (hk : ∀ x, Q₁ x → DdhStep m₂ Q₂ ((k .zero).eval (.cons x env))) :
    DdhStep (m₁ + m₂) Q₂ ((bindV c k).eval env) := by
  change DdhStep (m₁ + m₂) Q₂ (c.eval env >>= fun x => (k .zero).eval (.cons x env))
  exact ddhStep_bind hc hk

theorem ddhStep_bindV_zero {Γ : List PT} {τ₁ τ₂ : PT} {m : ℕ} {Q : τ₂.denote → Prop}
    (c : Comp pqxdhOps pqGapDhIface Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ)
    (hc : c.queries wDdhGdh wsZero = 0)
    (hk : ∀ x, DdhStep m Q ((k .zero).eval (.cons x env))) :
    DdhStep m Q ((bindV c k).eval env) := by
  have hc0 : DdhStep 0 (fun _ => True) (c.eval env) :=
    ⟨by rw [← hc]; exact Comp.queryBound_eval _ wDdhGdh wsZero hwDdh hUDdh c env,
     fun _ _ => trivial⟩
  have hb := ddhStep_bindV c k env hc0 (fun x _ => hk x)
  rwa [Nat.zero_add] at hb

theorem ddhStep_letV {Γ : List PT} {τ₁ τ₂ : PT} {m : ℕ} {Q : τ₂.denote → Prop}
    (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ)
    (hk : DdhStep m Q ((k .zero).eval (.cons (e.eval env) env))) :
    DdhStep m Q ((letV e k).eval env) := by
  rwa [letV_eval]

theorem ddhStep_ite {Γ : List PT} {τ : PT} {m : ℕ} {Q : τ.denote → Prop}
    (b : Expr pqxdhOps Γ .bool) (t f : Comp pqxdhOps pqGapDhIface Γ τ) (env : Env Γ)
    (ht : b.eval env = true → DdhStep m Q (t.eval env))
    (hf : b.eval env = false → DdhStep m Q (f.eval env)) :
    DdhStep m Q ((Comp.ite b t f).eval env) := by
  simp only [Comp.eval]
  cases hb : b.eval env
  · exact hf hb
  · exact ht hb

theorem ddhStep_caseOptV {Γ : List PT} {τ₁ τ₂ : PT} {m : ℕ} {Q : τ₂.denote → Prop}
    (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps pqGapDhIface Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    (env : Env Γ)
    (hn : o.eval env = none → DdhStep m Q (kn.eval env))
    (hs : ∀ x, o.eval env = some x → DdhStep m Q ((ks .zero).eval (.cons x env))) :
    DdhStep m Q ((caseOptV o kn ks).eval env) := by
  change DdhStep m Q ((Comp.caseOpt o kn (ks .zero)).eval env)
  simp only [Comp.eval]
  cases ho : o.eval env with
  | none => exact hn ho
  | some x => exact hs x ho

theorem ddhStep_caseSumV {Γ : List PT} {τ₁ τ₂ τ : PT} {m : ℕ} {Q : τ.denote → Prop}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqGapDhIface (τ₂ :: Γ) τ)
    (env : Env Γ)
    (hl : ∀ a, s.eval env = .inl a → DdhStep m Q ((kl .zero).eval (.cons a env)))
    (hr : ∀ b, s.eval env = .inr b → DdhStep m Q ((kr .zero).eval (.cons b env))) :
    DdhStep m Q ((caseSumV s kl kr).eval env) := by
  change DdhStep m Q ((Comp.caseSum s (kl .zero) (kr .zero)).eval env)
  simp only [Comp.eval]
  cases hs : s.eval env with
  | inl a => exact hl a hs
  | inr b => exact hr b hs

theorem findML_queryBound_countP {α : Type} (q : α → Bool)
    (p : α → OracleComp (PrimBaseSpec + gapDhDdhOracle.spec) Bool) (k : ℕ)
    (h0 : ∀ x, q x = true → (p x).IsQueryBoundP (fun t => t.isRight = true) 0)
    (hk : ∀ x, (p x).IsQueryBoundP (fun t => t.isRight = true) k) :
    ∀ xs : List α, (findML p xs).IsQueryBoundP (fun t => t.isRight = true)
      (k * xs.countP (fun x => !q x))
  | [] => by simp [findML]
  | x :: xs => by
    simp only [findML, List.countP_cons]
    by_cases hq : q x = true
    · simp only [hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      refine (isQueryBoundP_bind (n := 0) (m := k * xs.countP (fun x => !q x))
        (h0 x hq) (fun b _ => ?_)).mono (by omega)
      cases b
      · exact findML_queryBound_countP q p k h0 hk xs
      · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
    · have hqf : (!q x) = true := by cases hqx : q x <;> simp_all
      simp only [hqf, ↓reduceIte, Nat.mul_add, Nat.mul_one, Nat.add_comm _ k]
      refine isQueryBoundP_bind (n := k) (m := k * xs.countP (fun x => !q x))
        (hk x) (fun b _ => ?_)
      cases b
      · exact findML_queryBound_countP q p k h0 hk xs
      · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)

theorem mkSecretPosC_step {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) (env : Env Γ) :
    DdhStep 0 (fun p => isSecPos p = true) ((mkSecretPosC z).eval env) := by
  unfold mkSecretPosC
  refine ddhStep_letV _ _ _ ?_
  refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun c => ?_
  exact ddhStep_ret _ _ rfl

theorem ddhEqC_sec {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) (env : Env Γ)
    (h1 : isSecPos (p1.eval env) = true) (h2 : isSecPos (p2.eval env) = true) :
    ((ddhEqC p1 p2).eval env).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  rcases hp1 : p1.eval env with s1 | q1
  · rcases hp2 : p2.eval env with s2 | q2
    · simp only [ddhEqC, letV_eval, caseSumV, Comp.eval, Expr.eval, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', hp1, hp2]
      exact isQueryBoundP_pure _ _ 0
    · simp [isSecPos, hp2] at h2
  · simp [isSecPos, hp1] at h1

theorem ddhEqOptC_sec {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) (env : Env Γ)
    (h1 : isSecOptPos (p1?.eval env) = true) (h2 : isSecOptPos (p2?.eval env) = true) :
    ((ddhEqOptC p1? p2?).eval env).IsQueryBoundP (fun q => q.isRight = true) 0 := by
  rcases hp1 : p1?.eval env with _ | x1 <;> rcases hp2 : p2?.eval env with _ | x2
  · simp only [ddhEqOptC, letV_eval, caseOptV, Comp.eval, Expr.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', hp1, hp2]
    exact isQueryBoundP_pure _ _ 0
  · simp only [ddhEqOptC, letV_eval, caseOptV, Comp.eval, Expr.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', hp1, hp2]
    exact isQueryBoundP_pure _ _ 0
  · simp only [ddhEqOptC, letV_eval, caseOptV, Comp.eval, Expr.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', hp1, hp2]
    exact isQueryBoundP_pure _ _ 0
  · simp only [isSecOptPos, hp1] at h1
    simp only [isSecOptPos, hp2] at h2
    simp only [ddhEqOptC, letV_eval, caseOptV, Comp.eval, Expr.eval, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', hp1, hp2]
    exact ddhEqC_sec _ _ _ h1 h2

theorem entryMatchesC_sec {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy)
    (env : Env Δ)
    (h1 : isSecPos ((v pos1).eval env) = true)
    (h2 : isSecPos ((v pos2).eval env) = true)
    (h3 : isSecPos ((v pos3).eval env) = true)
    (h4 : isSecOptPos ((v pos4?).eval env) = true)
    (he : isSecEntry ((v e).eval env) = true) :
    ((entryMatchesC pos1 pos2 pos3 pos4? ss e).eval env).IsQueryBoundP
      (fun q => q.isRight = true) 0 := by
  simp only [isSecEntry, Bool.and_eq_true] at he
  obtain ⟨⟨⟨he1, he2⟩, he3⟩, he4⟩ := he
  unfold entryMatchesC
  simp only [Comp.eval]
  split
  · exact isQueryBoundP_pure _ _ 0
  · simp only [bindV, Comp.eval]
    have q1 := ddhEqC_sec (v pos1) (fePos1 (v e)) env h1 (by simpa [fePos1, Expr.eval] using he1)
    refine (isQueryBoundP_bind (n := 0) (m := 0) q1 fun b1 _ => ?_).mono (by omega)
    have q2 := ddhEqC_sec (v pos2) (fePos2 (v e)) (.cons b1 env)
      (by simpa [v, Expr.eval, Env.get_succ'] using h2)
      (by simpa [fePos2, v, Expr.eval, Env.get_succ'] using he2)
    refine (isQueryBoundP_bind (n := 0) (m := 0) q2 fun b2 _ => ?_).mono (by omega)
    have q3 := ddhEqC_sec (v pos3) (fePos3 (v e)) (.cons b2 (.cons b1 env))
      (by simpa [v, Expr.eval, Env.get_succ'] using h3)
      (by simpa [fePos3, v, Expr.eval, Env.get_succ'] using he3)
    refine (isQueryBoundP_bind (n := 0) (m := 0) q3 fun b3 _ => ?_).mono (by omega)
    have q4 := ddhEqOptC_sec (v pos4?) (fePos4 (v e)) (.cons b3 (.cons b2 (.cons b1 env)))
      (by simpa [v, Expr.eval, Env.get_succ'] using h4)
      (by simpa [fePos4, v, Expr.eval, Env.get_succ'] using he4)
    refine (isQueryBoundP_bind (n := 0) (m := 0) q4 fun b4 _ => ?_).mono (by omega)
    exact isQueryBoundP_pure _ _ 0

theorem fgPatchC_sec_step (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) (env : Env Δ)
    (h1 : isSecPos ((v pos1).eval env) = true)
    (h2 : isSecPos ((v pos2).eval env) = true)
    (h3 : isSecPos ((v pos3).eval env) = true)
    (h4 : isSecOptPos ((v pos4?).eval env) = true) :
    DdhStep (4 * fgSDone (fgL.eval env))
      (fun res => fgRDone res.2 ≤ fgRDone (fgL.eval env) + 1 ∧ fgSDone res.2 = fgSDone (fgL.eval env))
      ((fgPatchC K pos1 pos2 pos3 pos4? ss fgL).eval env) := by
  unfold fgPatchC
  refine ddhStep_letV _ _ _ ?_
  set L := fgL.eval env
  have hFind : DdhStep (4 * fgSDone L) (fun _ => True)
      ((findMV K (v (.zero : Var (Ty.list fgPatchEntryTy :: Δ) (.list fgPatchEntryTy)))
        fun e => entryMatchesC pos1 pos2 pos3 pos4? ss e).eval (.cons L env)) := by
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [findMV, Comp.eval, v, Ext.refl_wk', Expr.eval, Env.get_zero']
    refine (findML_queryBound_countP isSecEntry _ 4 ?_ ?_ (L.take K)).mono ?_
    · intro x hx
      exact entryMatchesC_sec pos1 pos2 pos3 pos4? ss .zero (.cons x (.cons L env))
        (by simpa [v, Expr.eval, Env.get_succ'] using h1)
        (by simpa [v, Expr.eval, Env.get_succ'] using h2)
        (by simpa [v, Expr.eval, Env.get_succ'] using h3)
        (by simpa [v, Expr.eval, Env.get_succ'] using h4)
        (by simpa [v, Expr.eval, Env.get_zero'] using hx)
    · intro x
      have hc := Comp.queryBound_eval (fun q => q.isRight = true) wDdhGdh wsZero hwDdh hUDdh
        (entryMatchesC pos1 pos2 pos3 pos4? ss .zero) (.cons x (.cons L env))
      rwa [entryMatchesC_chal] at hc
    · exact Nat.mul_le_mul_left 4 (countP_take_le (fun e => !isSecEntry e) L K)
  refine ddhStep_mono (m₁ := 4 * fgSDone L + 0) (by omega) (fun x hx => hx)
    (ddhStep_bindV _ _ _ hFind fun found _ => ?_)
  refine ddhStep_caseOptV _ _ _ _ (fun _ => ?_) (fun e _ => ?_)
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun dk => ?_
    refine ddhStep_ret _ _ ?_
    have hNew : isSecEntry
        ((feMk (v pos1) (v pos2) (v pos3) (v pos4?) (v ss)
          (v (.zero : Var (drKeyTy :: .opt fgPatchEntryTy :: .list fgPatchEntryTy :: Δ) drKeyTy))).eval
          (.cons dk (.cons found (.cons L env)))) = true := by
      simp only [feMk, isSecEntry, Expr.eval, v, Ext.step_wk', Ext.refl_wk',
        Env.get_zero', Env.get_succ', Bool.and_eq_true]
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    dsimp only [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ'] at hNew ⊢
    simp only [fgRDone, fgSDone, List.countP_cons, hNew, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    exact ⟨le_rfl, rfl⟩
  · refine ddhStep_ret _ _ ?_
    dsimp only [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact ⟨Nat.le_succ _, rfl⟩

theorem fgPatchC_any_step (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) (env : Env Δ) :
    DdhStep (4 * (fgRDone (fgL.eval env) + fgSDone (fgL.eval env)))
      (fun res =>
        let r := fgRDone (fgL.eval env)
        let s := fgSDone (fgL.eval env)
        (fgRDone res.2 = r ∧ fgSDone res.2 = s) ∨
        (fgRDone res.2 = r + 1 ∧ fgSDone res.2 = s) ∨
        (fgRDone res.2 = r ∧ fgSDone res.2 = s + 1))
      ((fgPatchC K pos1 pos2 pos3 pos4? ss fgL).eval env) := by
  unfold fgPatchC
  refine ddhStep_letV _ _ _ ?_
  set L := fgL.eval env
  have hFind : DdhStep (4 * (fgRDone L + fgSDone L)) (fun _ => True)
      ((findMV K (v (.zero : Var (Ty.list fgPatchEntryTy :: Δ) (.list fgPatchEntryTy)))
        fun e => entryMatchesC pos1 pos2 pos3 pos4? ss e).eval (.cons L env)) := by
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [findMV, Comp.eval, v, Ext.refl_wk', Expr.eval, Env.get_zero']
    refine (findML_queryBound _ (k := 4) (fun x => ?_) (L.take K)).mono ?_
    · have hc := Comp.queryBound_eval (fun q => q.isRight = true) wDdhGdh wsZero hwDdh hUDdh
        (entryMatchesC pos1 pos2 pos3 pos4? ss .zero) (.cons x (.cons L env))
      rwa [entryMatchesC_chal] at hc
    · have hlen : (L.take K).length ≤ L.length := by simp [List.length_take]
      have hrs := fgRDone_add_fgSDone L
      omega
  refine ddhStep_mono (m₁ := 4 * (fgRDone L + fgSDone L) + 0) (by omega) (fun x hx => hx)
    (ddhStep_bindV _ _ _ hFind fun found _ => ?_)
  refine ddhStep_caseOptV _ _ _ _ (fun _ => ?_) (fun e _ => ?_)
  · refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) fun dk => ?_
    refine ddhStep_ret _ _ ?_
    dsimp only [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
    simp only [fgRDone, fgSDone, List.countP_cons]
    cases isSecEntry ((feMk (v pos1) (v pos2) (v pos3) (v pos4?) (v ss)
      (v (.zero : Var (drKeyTy :: .opt fgPatchEntryTy :: .list fgPatchEntryTy :: Δ) drKeyTy))).eval
      (.cons dk (.cons found (.cons L env)))) <;> simp
  · refine ddhStep_ret _ _ ?_
    dsimp only [Expr.eval, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']
    exact Or.inl ⟨rfl, rfl⟩

scoped macro "ddh_step_auto" : tactic =>
  `(tactic| repeat' (first
    | refine ddhStep_ret _ _ ?_
    | refine ddhStep_letV _ _ _ ?_
    | refine ddhStep_ite _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    | refine ddhStep_caseOptV _ _ _ _ (fun _ => ?_) (fun _ _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (gPrim_queries_wDdhGdh _) (fun _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (computePosC_chal _ _ _ _) (fun _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (computeOptPosInitC_chal _ _ _) (fun _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (mkSecretPosC_chal _) (fun _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (chooseInitRandC_chal _ _ _ _) (fun _ => ?_)
    | refine ddhStep_bindV_zero _ _ _ (chooseRespRandC_chal _ _ _ _) (fun _ => ?_)))

theorem wrapBase_ddhStep {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.2.1 = ((v sm).eval env).2.1) ((wrapBase pa sm c).eval env) := by
  unfold wrapBase; ddh_step_auto
  rfl

theorem wrapSim_ddhStep {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {m : ℕ}
    {Q : List fgPatchEntryTy.denote → Prop}
    (pa : Var Γ₁ paramsTy)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) (env : Env Δ)
    (hc : DdhStep m (fun p => Q p.2.2.1) (c.eval env)) :
    DdhStep m (fun p => Q p.2.2.2.1) ((wrapSim pa c).eval env) := by
  unfold wrapSim
  refine ddhStep_mono (m₁ := m + 0) (by omega) (fun x hx => hx)
    (ddhStep_bindV _ _ _ hc fun r hr => ?_)
  exact ddhStep_ret _ _ hr

theorem initPrinGdhB_ddhStep (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((initPrinGdhB K pa sm bSt u).eval env) := by
  unfold initPrinGdhB; ddh_step_auto <;> rfl


theorem genOpkGdhB_ddhStep (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((genOpkGdhB S K pa sm bSt x).eval env) := by
  unfold genOpkGdhB; ddh_step_auto <;> simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

theorem registerGdhB_ddhStep {Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (sk : Var Γ₄ (B 32)) (env : Env Δ) :
    DdhStep 0 (fun p => p.2.2.1 = ((v sm).eval env).2.1)
      ((registerGdhB sm bSt sk).eval env) := by
  unfold registerGdhB; ddh_step_auto <;> simp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ']

theorem roRawFallbackC_ddhStep (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (B 192)) (env : Env Δ) :
    DdhStep (4 * fgSDone ((v sm).eval env).2.1)
      (fun p => fgRDone p.2.2.1 ≤ fgRDone ((v sm).eval env).2.1 + 1 ∧
        fgSDone p.2.2.1 = fgSDone ((v sm).eval env).2.1)
      ((roRawFallbackC K sm sec).eval env) := by
  refine ddhStep_mono (m₁ := 0) (Nat.zero_le _) (fun x hx => hx) ?_
  unfold roRawFallbackC; ddh_step_auto <;> {
    dsimp only [smUpd, smMk, smFgL, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ']
    exact ⟨Nat.le_succ _, rfl⟩
  }

theorem ddhStep_bindV_0 {Γ : List PT} {a b : PT} {m : ℕ}
    {P : a.denote → Prop} {Q : b.denote → Prop}
    (c : Comp pqxdhOps pqGapDhIface Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps pqGapDhIface (a :: Γ) b)
    (env : Env Γ) (hc : DdhStep 0 P (c.eval env))
    (hk : ∀ x, P x → DdhStep m Q ((k .zero).eval (.cons x env))) :
    DdhStep m Q ((bindV c k).eval env) :=
  ddhStep_mono (m₁ := 0 + m) (Nat.zero_add m).le (fun _ h => h) (ddhStep_bindV c k env hc hk)


@[expose] def SessPost (L : List fgPatchEntryTy.denote) (L' : List fgPatchEntryTy.denote) : Prop :=
  let r := fgRDone L
  let s := fgSDone L
  (fgRDone L' = r ∧ fgSDone L' = s) ∨
  (fgRDone L' = r + 1 ∧ fgSDone L' = s) ∨
  (fgRDone L' = r ∧ fgSDone L' = s + 1)

theorem sessPost_refl (L : List fgPatchEntryTy.denote) : SessPost L L :=
  Or.inl ⟨rfl, rfl⟩


theorem finishAcceptGdhC_ddhStep (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    {Q : List fgPatchEntryTy.denote → Prop}
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) (env : Env Δ)
    (hQ : Q (((v patchR).eval env).2)) :
    DdhStep 0 (fun p => Q p.2.2.1)
      ((finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).eval env) := by
  unfold finishAcceptGdhC
  ddh_step_auto
  simp only [eCaseOpt, Expr.eval]
  split <;> {
    simp only [smUpd, smMk, v, Expr.eval, Ext.step_wk', Ext.refl_wk',
      Env.get_zero', Env.get_succ']
    exact hQ
  }


end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
