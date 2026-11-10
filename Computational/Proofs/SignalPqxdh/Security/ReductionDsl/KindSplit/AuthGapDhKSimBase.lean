/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeySig -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# Shared Invariants and Per-Arm Contracts for One-Key `Auth` Gap-DH and EUF-CMA Simulation

**Checked by Lean.** Defines the simulator shadow invariant `FgSimShadowInv`, RO-entry purity
lemmas, online table-patching simulations, and the unified per-arm simulation contract `FgArmSim`
shared by `a1g2KindProg` and `a1s2KindProg`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase

open OracleSpec OracleComp
open _root_.ReductionDsl
  (Ty Var Expr Comp Env CostedReduction pqAtomicSig pqAtomicOps PB bundleT bundleV drKeyT)
open _root_.Computational.Proofs.ReductionDsl.StepSim (ForgetSim isGamePred bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (aiAuthSigDdh embedTy embedVal projVal embedVal_projVal embedEnv embedCtx embedVar
   mapExpr mapComp mapComp_eval comp_queries_zero_of_zero tlAuthSigDdh liftAuth1Stage)
open _root_.SignalPqxdh
  (Setup QueryBudget AuthQuery PreKeyBundleInput PreKeyMsg Bytes authSpec F_X25519)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface B)
open _root_.SignalPqxdh.Costed (pqAuthSigAndDdhIface authCodec preKeyMsgV)
open _root_.SignalPqxdh.Security (fgRootEntryMatches liftGdhToSign)
open _root_.SignalPqxdh.Security.FgGapDh (FgPoS FgPatchEntry ddhEqGdh ddhEqOptGdh fgEntryMatches)
open _root_.SignalPqxdh.Security.ReductionDsl
  (authStateTy fgPosTy fgPatchEntryTy authQueryTy authRespTy
   valToFgPos valToFgPatchEntry eval_sampleDrKey96C eval_sampleBytes32C)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext v letV bindV caseOptV caseSumV findMV
   patchKeyTy sendQTy fgSimTy rootEntryTy respRecTy a1gParams2Ty a1g2StTy a1sStTy
   pkP1 pkP2 pkP3 pkP4 pkSs feDk reRk rePos reRk1 reCk
   a1gPre2C fgStep2C a1sSendCheckC fgAuth1KeyGapDhProg sigAuth1KeyDslProg
   ddhEqC ddhEqOptC entryMatchesC patchC rootPatchC ddhEqC_eval ddhEqOptC_eval entryMatchesC_eval
   valToRootEntry)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
  (liftGdhComp liftGdhComp_eval)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (avlTy avlSearchB192C avlInsertAtPathC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
  (AvlB192Valid AvlPair32Valid avlSearchInsertB192_spec avlInsertAtPathC_eval_congr)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (SourceTag TaggedEntry roEntriesOf roEntriesOf_cons_sess
   ShadowRelB192 ShadowRelPair32 RoCacheRelB192)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels authSendQAtomicTy)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv AuthBaseAtomOnlineBounded)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (seqFgEntryTy seqRootEntryTy fgRoAvlTy fgRootRoAvlTy fgAuthShadowAuxTy
   a1g2ShadowStTy a1s2ShadowStTy fgCoreOutTy
   auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess auxFgRootCtr auxFgRootRoAvl auxRawAvl
   liftCs1 patchWithShadowC rootPatchWithShadowC a1sSendCheckLegC
   fgCoreArm_roQuery fgCoreArm_roRootQuery fgCoreArm_initPrin fgCoreArm_corrupt
   fgCoreArm_genSPK fgCoreArm_genOPK fgCoreArm_send fgCoreArm_recv
   fgCoreArm_revealDh fgCoreArm_registerKey
   a1g2KindProg a1s2KindProg)

@[expose] def forgetGdh (s' : a1g2ShadowStTy.denote) : (embedTy a1g2StTy).denote := s'.1

@[expose] def forgetSig (s' : a1s2ShadowStTy.denote) : (embedTy a1sStTy).denote := s'.1

/-- Atomic-lifted reference Gap-DH reduction for one-key `Auth`. -/
@[expose] def gdhOldAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftAuth1Stage tlAuthSigDdh S (fgAuth1KeyGapDhProg S b.q_total)

/-- Atomic-lifted reference EUF-CMA reduction for one-key `Auth`. -/
@[expose] def sigOldAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthSigAndDdhIface (authSpec S) (authCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftAuth1Stage tlAuthSigDdh S (sigAuth1KeyDslProg S b)

/-- Well-formedness of an RO-inserted `fgPatchEntry` whose secret slots are slices of a 160- or
    192-byte `F_X25519`-prefixed secret `sec`. -/
structure ValidParsedRoFgEntry
    (sec : Bytes) (e : (embedTy fgPatchEntryTy).denote) : Prop where
  prefix_eq : List.take 32 sec = F_X25519
  len_160_or_192 : sec.length = 160 ∨ sec.length = 192
  p1_inl : ∃ c1 : Bool, e.1 = Sum.inl (List.take 32 (List.drop 32 sec), c1)
  p2_inl : ∃ c2 : Bool, e.2.1 = Sum.inl (List.take 32 (List.drop 64 sec), c2)
  p3_inl : ∃ c3 : Bool, e.2.2.1 = Sum.inl (List.take 32 (List.drop 96 sec), c3)
  p4_ss_shape :
    (sec.length = 192 ∧
      (∃ c4 : Bool, e.2.2.2.1 = some (Sum.inl (List.take 32 (List.drop 128 sec), c4))) ∧
      e.2.2.2.2.1 = List.take 32 (List.drop 160 sec)) ∨
    (sec.length = 160 ∧
      e.2.2.2.1 = none ∧
      e.2.2.2.2.1 = List.take 32 (List.drop 128 sec))

/-- Well-formedness of an RO-inserted `rootEntry` with root key `k.1` and secret DH slot `k.2`. -/
structure ValidRoRootEntry
    (k : Bytes × Bytes) (e : (embedTy rootEntryTy).denote) : Prop where
  rk_eq : e.1 = k.1
  pos_inl : ∃ c : Bool, e.2.1 = Sum.inl (k.2, c)

private theorem list_eq_of_slices_160 {α : Type} {xs ys : List α}
    (hx : xs.length = 160) (hy : ys.length = 160)
    (h0 : List.take 32 xs = List.take 32 ys)
    (h1 : List.take 32 (List.drop 32 xs) = List.take 32 (List.drop 32 ys))
    (h2 : List.take 32 (List.drop 64 xs) = List.take 32 (List.drop 64 ys))
    (h3 : List.take 32 (List.drop 96 xs) = List.take 32 (List.drop 96 ys))
    (h4 : List.take 32 (List.drop 128 xs) = List.take 32 (List.drop 128 ys)) :
    xs = ys := by
  have decomp : ∀ (zs : List α), zs.length = 160 →
      zs = List.take 32 zs ++
        (List.take 32 (List.drop 32 zs) ++
          (List.take 32 (List.drop 64 zs) ++
            (List.take 32 (List.drop 96 zs) ++ List.take 32 (List.drop 128 zs)))) := by
    intro zs hlen
    have hd128 : List.take 32 (List.drop 128 zs) = List.drop 128 zs := by
      apply List.take_of_length_le
      simp [hlen]
    rw [hd128]
    have step4 : List.take 32 (List.drop 96 zs) ++ List.drop 128 zs = List.drop 96 zs := by
      have : List.drop 128 zs = List.drop 32 (List.drop 96 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    have step3 : List.take 32 (List.drop 64 zs) ++ List.drop 96 zs = List.drop 64 zs := by
      have : List.drop 96 zs = List.drop 32 (List.drop 64 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    have step2 : List.take 32 (List.drop 32 zs) ++ List.drop 64 zs = List.drop 32 zs := by
      have : List.drop 64 zs = List.drop 32 (List.drop 32 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    rw [step4, step3, step2, List.take_append_drop]
  rw [decomp xs hx, decomp ys hy, h0, h1, h2, h3, h4]

private theorem list_eq_of_slices_192 {α : Type} {xs ys : List α}
    (hx : xs.length = 192) (hy : ys.length = 192)
    (h0 : List.take 32 xs = List.take 32 ys)
    (h1 : List.take 32 (List.drop 32 xs) = List.take 32 (List.drop 32 ys))
    (h2 : List.take 32 (List.drop 64 xs) = List.take 32 (List.drop 64 ys))
    (h3 : List.take 32 (List.drop 96 xs) = List.take 32 (List.drop 96 ys))
    (h4 : List.take 32 (List.drop 128 xs) = List.take 32 (List.drop 128 ys))
    (h5 : List.take 32 (List.drop 160 xs) = List.take 32 (List.drop 160 ys)) :
    xs = ys := by
  have decomp : ∀ (zs : List α), zs.length = 192 →
      zs = List.take 32 zs ++
        (List.take 32 (List.drop 32 zs) ++
          (List.take 32 (List.drop 64 zs) ++
            (List.take 32 (List.drop 96 zs) ++
              (List.take 32 (List.drop 128 zs) ++ List.take 32 (List.drop 160 zs))))) := by
    intro zs hlen
    have hd160 : List.take 32 (List.drop 160 zs) = List.drop 160 zs := by
      apply List.take_of_length_le
      simp [hlen]
    rw [hd160]
    have step5 : List.take 32 (List.drop 128 zs) ++ List.drop 160 zs = List.drop 128 zs := by
      have : List.drop 160 zs = List.drop 32 (List.drop 128 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    have step4 : List.take 32 (List.drop 96 zs) ++ List.drop 128 zs = List.drop 96 zs := by
      have : List.drop 128 zs = List.drop 32 (List.drop 96 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    have step3 : List.take 32 (List.drop 64 zs) ++ List.drop 96 zs = List.drop 64 zs := by
      have : List.drop 96 zs = List.drop 32 (List.drop 64 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    have step2 : List.take 32 (List.drop 32 zs) ++ List.drop 64 zs = List.drop 32 zs := by
      have : List.drop 64 zs = List.drop 32 (List.drop 32 zs) := by simp [List.drop_drop]
      rw [this, List.take_append_drop]
    rw [step5, step4, step3, step2, List.take_append_drop]
  rw [decomp xs hx, decomp ys hy, h0, h1, h2, h3, h4, h5]

private theorem fgEntryMatches_on_parsedRo {sec sec' : Bytes}
    {e : (embedTy fgPatchEntryTy).denote}
    {c1 c2 c3 : Bool} {p4 : Option FgPoS} {ss : Bytes}
    (hPfx : List.take 32 sec = F_X25519)
    (hShape :
      (sec.length = 192 ∧
        (∃ c4 : Bool, p4 = some (.secret (List.take 32 (List.drop 128 sec)) c4)) ∧
        ss = List.take 32 (List.drop 160 sec)) ∨
      (sec.length = 160 ∧
        p4 = none ∧
        ss = List.take 32 (List.drop 128 sec)))
    (hEntry : ValidParsedRoFgEntry sec' e) :
    fgEntryMatches
      (.secret (List.take 32 (List.drop 32 sec)) c1)
      (.secret (List.take 32 (List.drop 64 sec)) c2)
      (.secret (List.take 32 (List.drop 96 sec)) c3)
      p4 ss (valToFgPatchEntry (projVal fgPatchEntryTy e)) =
    pure (sec' == sec) := by
  rcases e with ⟨e1, e2, e3, e4, e5, e6⟩
  obtain ⟨c1', he1⟩ := hEntry.p1_inl
  obtain ⟨c2', he2⟩ := hEntry.p2_inl
  obtain ⟨c3', he3⟩ := hEntry.p3_inl
  dsimp only at he1 he2 he3
  have hp1 : valToFgPos (projVal fgPosTy e1) =
      .secret (List.take 32 (List.drop 32 sec')) c1' := by
    rw [he1]; rfl
  have hp2 : valToFgPos (projVal fgPosTy e2) =
      .secret (List.take 32 (List.drop 64 sec')) c2' := by
    rw [he2]; rfl
  have hp3 : valToFgPos (projVal fgPosTy e3) =
      .secret (List.take 32 (List.drop 96 sec')) c3' := by
    rw [he3]; rfl
  have hvp : valToFgPatchEntry (projVal fgPatchEntryTy (e1, e2, e3, e4, e5, e6)) =
      ⟨valToFgPos (projVal fgPosTy e1), valToFgPos (projVal fgPosTy e2),
        valToFgPos (projVal fgPosTy e3), (projVal (.opt fgPosTy) e4).map valToFgPos,
        e5, (valToFgPatchEntry (projVal fgPatchEntryTy (e1, e2, e3, e4, e5, e6))).dk⟩ := rfl
  rw [hvp]
  rcases hShape with ⟨hlen, ⟨c4, hp4⟩, hss⟩ | ⟨hlen, hp4, hss⟩ <;>
    rcases hEntry.p4_ss_shape with ⟨hlen', ⟨c4', he4⟩, hess'⟩ | ⟨hlen', he4, hess'⟩
  ·
    dsimp only at he4 hess'
    have hp4' : (projVal (.opt fgPosTy) e4).map valToFgPos =
        some (.secret (List.take 32 (List.drop 128 sec')) c4') := by
      rw [he4]; rfl
    simp only [fgEntryMatches, hp1, hp2, hp3, hp4, hp4', hss, hess',
      ddhEqGdh, ddhEqOptGdh, pure_bind]
    by_cases hEq : sec' = sec
    · subst hEq; simp
    · rw [beq_eq_false_iff_ne.mpr hEq]
      split_ifs with hne
      · rfl
      · congr 1
        rw [Bool.not_eq_true, bne_eq_false_iff_eq] at hne
        rw [Bool.eq_false_iff]
        intro hand
        simp only [Bool.and_eq_true, beq_iff_eq] at hand
        exact hEq (list_eq_of_slices_192 hlen' hlen
          (hEntry.prefix_eq.trans hPfx.symm)
          hand.1.1.1.symm hand.1.1.2.symm hand.1.2.symm hand.2.symm hne.symm)
  ·
    dsimp only at he4
    have hp4' : (projVal (.opt fgPosTy) e4).map valToFgPos = none := by
      rw [he4]; rfl
    simp only [fgEntryMatches, hp1, hp2, hp3, hp4, hp4',
      ddhEqGdh, ddhEqOptGdh, pure_bind, Bool.and_false, ite_self]
    have hne : sec' ≠ sec := fun h => by subst h; omega
    simp [beq_eq_false_iff_ne.mpr hne]
  ·
    dsimp only at he4
    have hp4' : (projVal (.opt fgPosTy) e4).map valToFgPos =
        some (.secret (List.take 32 (List.drop 128 sec')) c4') := by
      rw [he4]; rfl
    simp only [fgEntryMatches, hp1, hp2, hp3, hp4, hp4',
      ddhEqGdh, ddhEqOptGdh, pure_bind, Bool.and_false, ite_self]
    have hne : sec' ≠ sec := fun h => by subst h; omega
    simp [beq_eq_false_iff_ne.mpr hne]
  ·
    dsimp only at he4 hess'
    have hp4' : (projVal (.opt fgPosTy) e4).map valToFgPos = none := by
      rw [he4]; rfl
    simp only [fgEntryMatches, hp1, hp2, hp3, hp4, hp4', hss, hess',
      ddhEqGdh, ddhEqOptGdh, pure_bind, Bool.and_true]
    by_cases hEq : sec' = sec
    · subst hEq; simp
    · rw [beq_eq_false_iff_ne.mpr hEq]
      split_ifs with hne
      · rfl
      · congr 1
        rw [Bool.not_eq_true, bne_eq_false_iff_eq] at hne
        rw [Bool.eq_false_iff]
        intro hand
        simp only [Bool.and_eq_true, beq_iff_eq] at hand
        exact hEq (list_eq_of_slices_160 hlen' hlen
          (hEntry.prefix_eq.trans hPfx.symm)
          hand.1.1.symm hand.1.2.symm hand.2.symm hne.symm)

private theorem fgRootEntryMatches_on_ro {rk dh : Bytes} {c : Bool}
    {k' : Bytes × Bytes} {e : (embedTy rootEntryTy).denote}
    (hEntry : ValidRoRootEntry k' e) :
    fgRootEntryMatches rk (.secret dh c) (valToRootEntry (projVal rootEntryTy e)) =
      pure (k' == (rk, dh)) := by
  obtain ⟨c', hpos⟩ := hEntry.pos_inl
  rcases k' with ⟨rk', dh'⟩
  have hrk : (valToRootEntry (projVal rootEntryTy e)).rk = rk' := hEntry.rk_eq
  have hp : (valToRootEntry (projVal rootEntryTy e)).dhPos = .secret dh' c' := by
    simp only [valToRootEntry, projVal]
    rw [hpos]
    rfl
  simp only [fgRootEntryMatches, hrk, hp, ddhEqGdh]
  by_cases h1 : rk = rk'
  · subst h1
    by_cases h2 : dh = dh'
    · subst h2; simp
    · have hne : dh' ≠ dh := Ne.symm h2
      simp [h2, hne]
  · have hne : rk' ≠ rk := Ne.symm h1
    simp [bne_iff_ne, h1, hne]

/-- On RO-inserted `fgPatchEntry` values, `entryMatchesC` evaluates purely to `sec' == sec`. -/
theorem entryMatchesC_atomic_on_parsedRo
    {Γ₁ Δ : List (Ty pqSig)} (k : Var Γ₁ patchKeyTy) [h₁ : Ext Γ₁ (fgPatchEntryTy :: Δ)]
    (ρ : Env Δ) {sec sec' : Bytes} {e : (embedTy fgPatchEntryTy).denote}
    {c1 c2 c3 : Bool}
    (hPfx : List.take 32 sec = F_X25519)
    (hp1 : (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).1 =
      Sum.inl (List.take 32 (List.drop 32 sec), c1))
    (hp2 : (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.1 =
      Sum.inl (List.take 32 (List.drop 64 sec), c2))
    (hp3 : (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.1 =
      Sum.inl (List.take 32 (List.drop 96 sec), c3))
    (hShape :
      (sec.length = 192 ∧
        (∃ c4 : Bool, (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.1 =
          some (Sum.inl (List.take 32 (List.drop 128 sec), c4))) ∧
        (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.2 =
          List.take 32 (List.drop 160 sec)) ∨
      (sec.length = 160 ∧
        (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.1 = none ∧
        (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.2 =
          List.take 32 (List.drop 128 sec)))
    (hEntry : ValidParsedRoFgEntry sec' e) :
    (mapComp tlAuthSigDdh
      (liftGdhComp (entryMatchesC (Δ := fgPatchEntryTy :: Δ) k
        (.zero : Var (fgPatchEntryTy :: Δ) fgPatchEntryTy)))).eval
      (.cons e (embedEnv ρ)) = pure (sec' == sec) := by
  have he : e = embedVal fgPatchEntryTy (projVal fgPatchEntryTy e) :=
    (embedVal_projVal fgPatchEntryTy e).symm
  conv_lhs => rw [he]
  change (mapComp tlAuthSigDdh
    (liftGdhComp (entryMatchesC (Δ := fgPatchEntryTy :: Δ) k
      (.zero : Var (fgPatchEntryTy :: Δ) fgPatchEntryTy)))).eval
    (embedEnv (.cons (projVal fgPatchEntryTy e) ρ)) = pure (sec' == sec)
  rw [mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
  have hid : (embedVal .bool : Bool → Bool) = id := rfl
  simp only [hid, id_map, liftGdhComp_eval, entryMatchesC_eval, hp1, hp2, hp3]
  have hMatch :
      fgEntryMatches
        (.secret (List.take 32 (List.drop 32 sec)) c1)
        (.secret (List.take 32 (List.drop 64 sec)) c2)
        (.secret (List.take 32 (List.drop 96 sec)) c3)
        ((Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.1.map valToFgPos)
        (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.2
        (valToFgPatchEntry (projVal fgPatchEntryTy e)) = pure (sec' == sec) := by
    apply fgEntryMatches_on_parsedRo hPfx _ hEntry
    rcases hShape with ⟨hlen, ⟨c4, hp4⟩, hss⟩ | ⟨hlen, hp4, hss⟩
    · exact Or.inl ⟨hlen, ⟨c4, by simp [hp4]⟩, hss⟩
    · exact Or.inr ⟨hlen, by simp [hp4], hss⟩
  change liftGdhToSign (fgEntryMatches
    (.secret (List.take 32 (List.drop 32 sec)) c1)
    (.secret (List.take 32 (List.drop 64 sec)) c2)
    (.secret (List.take 32 (List.drop 96 sec)) c3)
    ((Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.1.map valToFgPos)
    (Env.get (.cons (projVal fgPatchEntryTy e) ρ) (h₁.wk k)).2.2.2.2
    (valToFgPatchEntry (projVal fgPatchEntryTy e))) = pure (sec' == sec)
  rw [hMatch]
  simp [liftGdhToSign]

/-- On RO-inserted `rootEntry` values, the `rootPatchC` match predicate evaluates purely to
    `k' == (rk, dh)`. -/
theorem rootMatchC_atomic_on_ro
    {Δ : List (Ty pqSig)}
    (rkE : Expr pqxdhOps (rootEntryTy :: Δ) (B 32))
    (posE : Expr pqxdhOps (rootEntryTy :: Δ) fgPosTy)
    (ρ : Env Δ) {rk dh : Bytes} {c : Bool}
    {k' : Bytes × Bytes} {e : (embedTy rootEntryTy).denote}
    (hrk : rkE.eval (.cons (projVal rootEntryTy e) ρ) = rk)
    (hpos : posE.eval (.cons (projVal rootEntryTy e) ρ) = Sum.inl (dh, c))
    (hEntry : ValidRoRootEntry k' e) :
    (mapComp tlAuthSigDdh
      (liftGdhComp
        (.iteC (.boolNot (.bytesBeq rkE (reRk (.var .zero)))) (.ret (.litBool false))
          (ddhEqC posE (rePos (.var .zero)))))).eval
      (.cons e (embedEnv ρ)) = pure (k' == (rk, dh)) := by
  have he : e = embedVal rootEntryTy (projVal rootEntryTy e) :=
    (embedVal_projVal rootEntryTy e).symm
  conv_lhs => rw [he]
  change (mapComp tlAuthSigDdh
    (liftGdhComp
      (.iteC (.boolNot (.bytesBeq rkE (reRk (.var .zero)))) (.ret (.litBool false))
        (ddhEqC posE (rePos (.var .zero)))))).eval
    (embedEnv (.cons (projVal rootEntryTy e) ρ)) = pure (k' == (rk, dh))
  rw [mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
  have hid : (embedVal .bool : Bool → Bool) = id := rfl
  simp only [hid, id_map, liftGdhComp_eval, Comp.iteC,
    reRk, rePos, Comp.eval, Expr.eval_bytesBeq, Expr.eval, Env.get, ddhEqC_eval,
    hrk, hpos]
  have hBody :
      (if (!(rk == (projVal rootEntryTy e).1)) = true then (pure false : OracleComp _ Bool)
       else ddhEqGdh (.secret dh c) (valToFgPos (projVal rootEntryTy e).2.1)) =
      fgRootEntryMatches rk (.secret dh c) (valToRootEntry (projVal rootEntryTy e)) := rfl
  change liftGdhToSign
    (if (!(rk == (projVal rootEntryTy e).1)) = true then (pure false : OracleComp _ Bool)
     else ddhEqGdh (.secret dh c) (valToFgPos (projVal rootEntryTy e).2.1)) =
    pure (k' == (rk, dh))
  rw [hBody, fgRootEntryMatches_on_ro hEntry]
  simp [liftGdhToSign]

/-- Post-halt-guard body of `a1gStep2C S b.q_total`. -/
@[expose] def legacyCoreArmComp (S : Setup) (b : QueryBudget) :
    Comp pqxdhOps pqSigAndDdhIface [a1gParams2Ty, fgSimTy, .nat, authQueryTy]
      (.prod authRespTy (.prod fgSimTy .nat)) :=
  let pa   : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] a1gParams2Ty := .zero
  let sim  : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] fgSimTy := .succ .zero
  let sigB : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] .nat := .succ (.succ .zero)
  let q    : Var [a1gParams2Ty, fgSimTy, .nat, authQueryTy] authQueryTy := .succ (.succ (.succ .zero))
  bindV (a1gPre2C b.q_total pa sim sigB q) fun pre =>
  caseSumV (v pre)
    (fun r => .ret (v r)) fun _ =>
  bindV (liftGdhComp (fgStep2C S b.q_total pa sim q)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.snd (v r)) (v sigB)))

/-- Mixed session and RO shadow invariant for the `fgPatchEntry` table. -/
@[expose] def FgTableShadow (S : Setup) (b : QueryBudget) (nOn nRo : ℕ)
    (fgL : (embedTy (.list fgPatchEntryTy)).denote)
    (fgRoAvl : fgRoAvlTy.denote)
    (fgSess : (embedTy (.list seqFgEntryTy)).denote)
    (fgCtr : ℕ) : Prop :=
  ∃ fgTagged : List (TaggedEntry Bytes (embedTy fgPatchEntryTy).denote),
    ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) (nOn + nRo)
      (AuthKindFuels.ofBudget S b).K_cap
      (fun e => e.2.2.2.2.2) fgL fgTagged fgRoAvl fgSess fgCtr ∧
    fgSess.length ≤ nOn ∧
    (roEntriesOf (fun e => e.2.2.2.2.2) fgTagged).length ≤ nRo ∧
    fgTagged.length ≤ nOn + nRo ∧
    ∀ te ∈ fgTagged, ∀ sec, te.tag = .ro sec → ValidParsedRoFgEntry sec te.entry

/-- Mixed session and RO shadow invariant for the `rootEntry` table. -/
@[expose] def RootTableShadow (S : Setup) (b : QueryBudget) (nOn nRoot : ℕ)
    (rootL : (embedTy (.list rootEntryTy)).denote)
    (rootRoAvl : fgRootRoAvlTy.denote)
    (rootSess : (embedTy (.list seqRootEntryTy)).denote)
    (rootCtr : ℕ) : Prop :=
  ∃ rootTagged : List (TaggedEntry (Bytes × Bytes) (embedTy rootEntryTy).denote),
    ShadowRelPair32 (.prod (PB 32) (PB 32)) (nOn + nRoot)
      (AuthKindFuels.ofBudget S b).K_cap
      (fun e => e.2.2) rootL rootTagged rootRoAvl rootSess rootCtr ∧
    rootSess.length ≤ nOn ∧
    (roEntriesOf (fun e => e.2.2) rootTagged).length ≤ nRoot ∧
    rootTagged.length ≤ nOn + nRoot ∧
    ∀ te ∈ rootTagged, ∀ k, te.tag = .ro k → ValidRoRootEntry k te.entry

/-- Simulator shadow invariant relating `sim` and `aux` at query-count vector `c`
    (`0` = online, `1` = `roQuery`, `2` = `roRootQuery`, `3` = total). -/
structure FgSimShadowInv (S : Setup) (b : QueryBudget) (c : Fin 4 → ℕ)
    (sim : (embedTy fgSimTy).denote) (aux : fgAuthShadowAuxTy.denote) : Prop where
  counter_inv : AuthCounterInv b c
  base_online : AuthBaseAtomOnlineBounded (c 0) sim.1
  pows_len    : sim.2.2.2.2.2.2.length ≤ c 0
  resp_len    : sim.2.2.2.2.2.1.length ≤ c 0
  log_len     : sim.2.2.2.2.1.length ≤ c 1
  fg_shadow   : FgTableShadow S b (c 0) (c 1)
    sim.2.1 (auxFgRoAvl aux) (auxFgSess aux) (auxFgCtr aux)
  root_shadow : RootTableShadow S b (c 0) (c 2)
    sim.2.2.1 (auxFgRootRoAvl aux) (auxFgRootSess aux) (auxFgRootCtr aux)
  raw_rel     : RoCacheRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total
    (AuthKindFuels.ofBudget S b).K_cap sim.2.2.2.1 (auxRawAvl aux)
  raw_len     : sim.2.2.2.1.length ≤ c 1

/-- State invariant for `a1g2KindProg`. -/
@[expose] def GdhAuthInv (S : Setup) (b : QueryBudget) (c : Fin 4 → ℕ)
    (s' : a1g2ShadowStTy.denote) : Prop :=
  FgSimShadowInv S b c s'.1.1.2 s'.2

/-- State invariant for `a1s2KindProg`. -/
@[expose] def SigAuthInv (S : Setup) (b : QueryBudget) (c : Fin 4 → ℕ)
    (s' : a1s2ShadowStTy.denote) : Prop :=
  FgSimShadowInv S b c s'.1.1.1.2 s'.2

private theorem le_bumpPred {S : Setup} (c : Fin 4 → ℕ) (t : AuthQuery S) (j : Fin 4) :
    c j ≤ bumpPred (authSimPred S) c t j := by
  simp only [bumpPred]; split_ifs <;> omega

private theorem embedVal_list_length {a : Ty pqSig} (xs : (Ty.list a).denote) :
    (embedVal (.list a) xs).length = xs.length := by
  simp [embedVal]

/-- Preserves `FgSimShadowInv` across a query step that leaves `sim` and `aux` unchanged. -/
theorem FgSimShadowInv.bump_unchanged {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote} (t : AuthQuery S)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    FgSimShadowInv S b (bumpPred (authSimPred S) c t) sim aux := by
  have h0 := le_bumpPred c t 0
  have h1 := le_bumpPred c t 1
  have h2 := le_bumpPred c t 2
  refine
    { counter_inv := hInv.counter_inv.bump t hroom
      base_online := hInv.base_online.mono h0
      pows_len    := Nat.le_trans hInv.pows_len h0
      resp_len    := Nat.le_trans hInv.resp_len h0
      log_len     := Nat.le_trans hInv.log_len h1
      fg_shadow   := ?_
      root_shadow := ?_
      raw_rel     := hInv.raw_rel
      raw_len     := Nat.le_trans hInv.raw_len h1 }
  · obtain ⟨fgTagged, hRel, hSess, hRo, hTag, hV⟩ := hInv.fg_shadow
    exact ⟨fgTagged, hRel.mono_cap (by omega), by omega, by omega, by omega, hV⟩
  · obtain ⟨rootTagged, hRel, hSess, hRo, hTag, hV⟩ := hInv.root_shadow
    exact ⟨rootTagged, hRel.mono_cap (by omega), by omega, by omega, by omega, hV⟩

/-- Preserves `FgSimShadowInv` when an aborted `recv` query prepends a responder record to `fsResp`. -/
theorem FgSimShadowInv.bump_resp_cons {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote}
    (r : (embedTy respRecTy).denote) (t : AuthQuery S)
    (hon : authSimPred S 0 t)
    (hroom : ∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    FgSimShadowInv S b (bumpPred (authSimPred S) c t)
      (sim.1, (sim.2.1, (sim.2.2.1, (sim.2.2.2.1, (sim.2.2.2.2.1,
        (r :: sim.2.2.2.2.2.1, sim.2.2.2.2.2.2)))))) aux := by
  have hU := hInv.bump_unchanged t hroom
  refine
    { counter_inv := hU.counter_inv
      base_online := hU.base_online
      pows_len    := hU.pows_len
      resp_len    := ?_
      log_len     := hU.log_len
      fg_shadow   := hU.fg_shadow
      root_shadow := hU.root_shadow
      raw_rel     := hU.raw_rel
      raw_len     := hU.raw_len }
  simp only [List.length_cons, bumpPred, hon, ↓reduceIte]
  exact Nat.succ_le_succ hInv.resp_len

/-- Simulation of `patchC` by `patchWithShadowC` with `FgTableShadow` preservation. -/
theorem patchWithShadowC_sim {S : Setup} {b : QueryBudget} {nOn nRo : ℕ}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List (Ty pqSig)}
    (k₁ : Var Γ₁ patchKeyTy) [hExt₁ : Ext Γ₁ Δ₁]
    (k₂ : Var Γ₂ patchKeyTy) [hExt₂ : Ext Γ₂ Δ₂]
    (fgLE₁ : Expr pqxdhOps Δ₁ (.list fgPatchEntryTy))
    (fgSessE₁ : Expr pqxdhOps Δ₁ (.list seqFgEntryTy))
    (fgCtrE₁ : Expr pqxdhOps Δ₁ .nat)
    (fgLE₂ : Expr pqxdhOps Δ₂ (.list fgPatchEntryTy))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (fgRoAvl : fgRoAvlTy.denote)
    (hk : Env.get env₁ (hExt₁.wk k₁) = Env.get env₂ (hExt₂.wk k₂))
    (hL : fgLE₁.eval env₁ = fgLE₂.eval env₂)
    (hCap : (nOn + 1) + nRo ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hShadow : FgTableShadow S b nOn nRo
      (embedVal (.list fgPatchEntryTy) (fgLE₁.eval env₁)) fgRoAvl
      (embedVal (.list seqFgEntryTy) (fgSessE₁.eval env₁)) (fgCtrE₁.eval env₁)) :
    (fun r => (r.1, r.2.1)) <$>
      (patchWithShadowC (AuthKindFuels.ofBudget S b).K_ro k₁ fgLE₁ fgSessE₁ fgCtrE₁).eval env₁ =
      (patchC b.q_total k₂ fgLE₂).eval env₂ ∧
    ∀ r ∈ support
      ((patchWithShadowC (AuthKindFuels.ofBudget S b).K_ro k₁ fgLE₁ fgSessE₁ fgCtrE₁).eval env₁),
      FgTableShadow S b (nOn + 1) nRo
        (embedVal (.list fgPatchEntryTy) r.2.1) fgRoAvl
        (embedVal (.list seqFgEntryTy) r.2.2.1) r.2.2.2 := by
  obtain ⟨fgTagged, hRel, hSessLen, hRoLen, hTagLen, hValidRo⟩ := hShadow
  have hLenEq : (fgLE₁.eval env₁).length = fgTagged.length := by
    rw [← embedVal_list_length (fgLE₁.eval env₁), ← hRel.1.forget_eq, List.length_map]
  have hKroLe : (AuthKindFuels.ofBudget S b).K_ro ≤ b.q_total :=
    AuthKindFuels.K_ro_le_q_total S b
  have hTake1 : List.take (AuthKindFuels.ofBudget S b).K_ro (fgLE₁.eval env₁) = fgLE₁.eval env₁ :=
    List.take_of_length_le (by omega)
  have hTake2 : List.take b.q_total (fgLE₁.eval env₁) = fgLE₁.eval env₁ :=
    List.take_of_length_le (by omega)
  simp only [patchWithShadowC, patchC, letV, bindV, caseOptV, findMV, Comp.findBoundedM,
    v, Var.vz, Var.vs,
    pkP1, pkP2, pkP3, pkP4, pkSs, feDk, Comp.eval_letC, eval_sampleDrKey96C, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get, entryMatchesC_eval,
    ← hL, hTake1, hTake2, hk, map_bind]
  constructor
  · refine congrArg (fun h => _ >>= h) (funext fun o => ?_)
    rcases o with _ | e
    · simp only [map_bind, map_pure]
    · simp only [map_pure]
  · intro r hr
    simp only [mem_support_bind_iff] at hr
    rcases hr with ⟨o, _, hr⟩
    rcases o with _ | e
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      rcases hr with ⟨dk, _, rfl⟩
      have hCtrEq : fgCtrE₁.eval env₁ = fgTagged.length := by
        rw [hRel.1.ctr_eq, ← hRel.1.forget_eq, List.length_map]
      let newE : fgPatchEntryTy.denote :=
        ((Env.get env₂ (hExt₂.wk k₂)).1,
          ((Env.get env₂ (hExt₂.wk k₂)).2.1,
            ((Env.get env₂ (hExt₂.wk k₂)).2.2.1,
              ((Env.get env₂ (hExt₂.wk k₂)).2.2.2.1,
                ((Env.get env₂ (hExt₂.wk k₂)).2.2.2.2, dk)))))
      have hRel' : ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) ((nOn + 1) + nRo)
          (AuthKindFuels.ofBudget S b).K_cap (fun e => e.2.2.2.2.2)
          (embedVal (.list fgPatchEntryTy) (newE :: fgLE₁.eval env₁))
          (⟨fgCtrE₁.eval env₁, .sess, embedVal fgPatchEntryTy newE⟩ :: fgTagged)
          fgRoAvl
          (embedVal (.list seqFgEntryTy) ((fgCtrE₁.eval env₁, newE) :: fgSessE₁.eval env₁))
          (fgCtrE₁.eval env₁ + 1) :=
        (hRel.mono_cap (by omega)).cons_sess (embedVal fgPatchEntryTy newE)
          (by rw [hCtrEq]; omega)
      refine ⟨⟨fgCtrE₁.eval env₁, .sess, embedVal fgPatchEntryTy newE⟩ :: fgTagged,
        hRel', ?_, ?_, ?_, ?_⟩
      · change (embedVal seqFgEntryTy _ :: embedVal (.list seqFgEntryTy) _).length ≤ nOn + 1
        simp only [List.length_cons]; omega
      · rw [roEntriesOf_cons_sess]; exact hRoLen
      · simp only [List.length_cons]; omega
      · intro te hMem sec hTag
        rcases List.mem_cons.mp hMem with rfl | hMem'
        · cases hTag
        · exact hValidRo te hMem' sec hTag
    · simp only [mem_support_pure_iff] at hr
      subst hr
      dsimp only
      exact ⟨fgTagged, hRel.mono_cap (by omega), by omega, hRoLen, by omega, hValidRo⟩

/-- Simulation of `rootPatchC` by `rootPatchWithShadowC` with `RootTableShadow` preservation. -/
theorem rootPatchWithShadowC_sim {S : Setup} {b : QueryBudget} {nOn nRoot : ℕ}
    {Δ₁ Δ₂ : List (Ty pqSig)}
    (rkE₁ : Expr pqxdhOps Δ₁ (B 32)) (posE₁ : Expr pqxdhOps Δ₁ fgPosTy)
    (rootLE₁ : Expr pqxdhOps Δ₁ (.list rootEntryTy))
    (rootSessE₁ : Expr pqxdhOps Δ₁ (.list seqRootEntryTy))
    (rootCtrE₁ : Expr pqxdhOps Δ₁ .nat)
    (rkE₂ : Expr pqxdhOps Δ₂ (B 32)) (posE₂ : Expr pqxdhOps Δ₂ fgPosTy)
    (rootLE₂ : Expr pqxdhOps Δ₂ (.list rootEntryTy))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (rootRoAvl : fgRootRoAvlTy.denote)
    (hrk : rkE₁.eval env₁ = rkE₂.eval env₂)
    (hpos : posE₁.eval env₁ = posE₂.eval env₂)
    (hL : rootLE₁.eval env₁ = rootLE₂.eval env₂)
    (hCap : (nOn + 1) + nRoot ≤ (AuthKindFuels.ofBudget S b).K_ro)
    (hShadow : RootTableShadow S b nOn nRoot
      (embedVal (.list rootEntryTy) (rootLE₁.eval env₁)) rootRoAvl
      (embedVal (.list seqRootEntryTy) (rootSessE₁.eval env₁)) (rootCtrE₁.eval env₁)) :
    (fun r => (r.1, r.2.1)) <$>
      (rootPatchWithShadowC (AuthKindFuels.ofBudget S b).K_ro
        rkE₁ posE₁ rootLE₁ rootSessE₁ rootCtrE₁).eval env₁ =
      (rootPatchC b.q_total rkE₂ posE₂ rootLE₂).eval env₂ ∧
    ∀ r ∈ support
      ((rootPatchWithShadowC (AuthKindFuels.ofBudget S b).K_ro
        rkE₁ posE₁ rootLE₁ rootSessE₁ rootCtrE₁).eval env₁),
      RootTableShadow S b (nOn + 1) nRoot
        (embedVal (.list rootEntryTy) r.2.1) rootRoAvl
        (embedVal (.list seqRootEntryTy) r.2.2.1) r.2.2.2 := by
  obtain ⟨rootTagged, hRel, hSessLen, hRoLen, hTagLen, hValidRo⟩ := hShadow
  have hLenEq : (rootLE₁.eval env₁).length = rootTagged.length := by
    rw [← embedVal_list_length (rootLE₁.eval env₁), ← hRel.1.forget_eq, List.length_map]
  have hKroLe : (AuthKindFuels.ofBudget S b).K_ro ≤ b.q_total :=
    AuthKindFuels.K_ro_le_q_total S b
  have hTake1 : List.take (AuthKindFuels.ofBudget S b).K_ro (rootLE₁.eval env₁) = rootLE₁.eval env₁ :=
    List.take_of_length_le (by omega)
  have hTake2 : List.take b.q_total (rootLE₁.eval env₁) = rootLE₁.eval env₁ :=
    List.take_of_length_le (by omega)
  simp only [rootPatchWithShadowC, rootPatchC, letV, bindV, caseOptV, findMV, Comp.findBoundedM,
    v, Var.vz, Var.vs, reRk, rePos, reRk1, reCk, Comp.iteC, Comp.eval_letC, eval_sampleBytes32C,
    Comp.eval, Expr.eval_bytesBeq, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get, ddhEqC_eval,
    ← hL, hTake1, hTake2, hrk, hpos, map_bind]
  constructor
  · refine congrArg (fun h => _ >>= h) (funext fun o => ?_)
    rcases o with _ | e
    · simp only [map_bind, map_pure]
    · simp only [map_pure]
  · intro r hr
    simp only [mem_support_bind_iff] at hr
    rcases hr with ⟨o, _, hr⟩
    rcases o with _ | e
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      rcases hr with ⟨rk1, _, ck1, _, rfl⟩
      have hCtrEq : rootCtrE₁.eval env₁ = rootTagged.length := by
        rw [hRel.1.ctr_eq, ← hRel.1.forget_eq, List.length_map]
      let newRE : rootEntryTy.denote :=
        (rkE₂.eval env₂, (posE₂.eval env₂, (rk1, ck1)))
      have hRel' : ShadowRelPair32 (.prod (PB 32) (PB 32)) ((nOn + 1) + nRoot)
          (AuthKindFuels.ofBudget S b).K_cap (fun e => e.2.2)
          (embedVal (.list rootEntryTy) (newRE :: rootLE₁.eval env₁))
          (⟨rootCtrE₁.eval env₁, .sess, embedVal rootEntryTy newRE⟩ :: rootTagged)
          rootRoAvl
          (embedVal (.list seqRootEntryTy) ((rootCtrE₁.eval env₁, newRE) :: rootSessE₁.eval env₁))
          (rootCtrE₁.eval env₁ + 1) :=
        (hRel.mono_cap (by omega)).cons_sess (embedVal rootEntryTy newRE)
          (by rw [hCtrEq]; omega)
      refine ⟨⟨rootCtrE₁.eval env₁, .sess, embedVal rootEntryTy newRE⟩ :: rootTagged,
        hRel', ?_, ?_, ?_, ?_⟩
      · change (embedVal seqRootEntryTy _ :: embedVal (.list seqRootEntryTy) _).length ≤ nOn + 1
        simp only [List.length_cons]; omega
      · rw [roEntriesOf_cons_sess]; exact hRoLen
      · simp only [List.length_cons]; omega
      · intro te hMem k hTag
        rcases List.mem_cons.mp hMem with rfl | hMem'
        · cases hTag
        · exact hValidRo te hMem' k hTag
    · simp only [mem_support_pure_iff] at hr
      subst hr
      dsimp only
      exact ⟨rootTagged, hRel.mono_cap (by omega), by omega, hRoLen, by omega, hValidRo⟩

@[reducible, expose] def AuthSigDdhSpec :=
  _root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.Costed.sigAndDdhOracle.spec

/-- Atomic-lifted evaluation of `legacyCoreArmComp S b` on `(pa, sim, sigB, t)`. -/
@[expose] def legacyCoreArmEval (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (t : AuthQuery S) :
    OracleComp AuthSigDdhSpec
      ((embedTy authRespTy).denote × ((embedTy fgSimTy).denote × ℕ)) :=
  (mapComp tlAuthSigDdh (legacyCoreArmComp S b)).eval
    (.cons pa (.cons sim (.cons sigB (.cons ((authCodec S).qenc t) .nil))))

@[expose] def armEval_initPrin (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (u : Fin S.N_id) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_initPrin (AuthKindFuels.ofBudget S b)
    (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero)))))
    (.var .zero)).eval
    (.cons u.val (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_corruptIK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (u : Fin S.N_id) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_corrupt (AuthKindFuels.ofBudget S b)
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons u.val (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_genSPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (p : Fin S.N_id × Fin S.N_recv) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_genSPK (AuthKindFuels.ofBudget S b)
    (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero)))))
    (.var .zero)).eval
    (.cons (p.1.val, p.2.val) (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_genOPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (p : Fin S.N_id × Fin S.N_recv × Fin S.N_opk) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_genOPK (AuthKindFuels.ofBudget S b)
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons (p.1.val, (p.2.1.val, p.2.2.val)) (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_sendOPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote)
    (p : Fin S.N_id × Fin S.N_send_opk × PreKeyBundleInput × Bytes × Bytes) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_send S (AuthKindFuels.ofBudget S b) true
    (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero)))))
    (.var .zero)).eval
    (.cons (p.1.val, (p.2.1.val, (bundleV (ℓ := 0) (Pt := Empty) p.2.2.1, (p.2.2.2.1, p.2.2.2.2))))
      (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_sendNoOPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote)
    (p : Fin S.N_id × Fin S.N_send_no_opk × PreKeyBundleInput × Bytes × Bytes) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_send S (AuthKindFuels.ofBudget S b) false
    (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    (.var (.succ (.succ (.succ .zero)))) (.var (.succ (.succ (.succ (.succ .zero)))))
    (.var .zero)).eval
    (.cons (p.1.val, (p.2.1.val, (bundleV (ℓ := 0) (Pt := Empty) p.2.2.1, (p.2.2.2.1, p.2.2.2.2))))
      (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_recvOPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote)
    (p : Fin S.N_id × Fin S.N_recv × Fin S.N_opk × PreKeyMsg) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) true
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons (p.1.val, (p.2.1.val, (p.2.2.1.val, preKeyMsgV p.2.2.2)))
      (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_recvNoOPK (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote)
    (p : Fin S.N_id × Fin S.N_recv × Fin S.N_no_opk × PreKeyMsg) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_recv S (AuthKindFuels.ofBudget S b) false
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons (p.1.val, (p.2.1.val, (p.2.2.1.val, preKeyMsgV p.2.2.2)))
      (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_roQuery (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (sec : Bytes) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_roQuery (AuthKindFuels.ofBudget S b)
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons sec (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_roRootQuery (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (p : Bytes × Bytes) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_roRootQuery (AuthKindFuels.ofBudget S b)
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons p (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_revealDhSecrets (_S : Setup) (_b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (_u : Unit) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_revealDh (Γ := [.unit, embedTy a1gParams2Ty, embedTy fgSimTy, .nat, fgAuthShadowAuxTy])
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero)))))).eval
    (.cons () (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

@[expose] def armEval_registerKey (_S : Setup) (_b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote) (sigB : ℕ)
    (aux : fgAuthShadowAuxTy.denote) (sk : Bytes) :
    OracleComp AuthSigDdhSpec fgCoreOutTy.denote :=
  (fgCoreArm_registerKey
    (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))
    (.var (.succ (.succ (.succ (.succ .zero))))) (.var .zero)).eval
    (.cons sk (.cons pa (.cons sim (.cons sigB (.cons aux .nil)))))

/-- Forgetful simulation contract for a single `AuthQuery` constructor arm, shared by
    `a1g2KindProg` and `a1s2KindProg`. -/
@[expose] def FgArmSim (S : Setup) (b : QueryBudget) {Payload : Type}
    (mkQ : Payload → AuthQuery S)
    (armEvalNew : (embedTy a1gParams2Ty).denote → (embedTy fgSimTy).denote → ℕ →
      fgAuthShadowAuxTy.denote → Payload →
      OracleComp AuthSigDdhSpec fgCoreOutTy.denote) : Prop :=
  ∀ (c : Fin 4 → ℕ) (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote)
    (sigB : ℕ) (aux : fgAuthShadowAuxTy.denote) (x : Payload),
    let t := mkQ x
    (∀ j, c j ≤ authSimBounds b j) →
    (∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) →
    FgSimShadowInv S b c sim aux →
    Prod.map id Prod.fst <$> armEvalNew pa sim sigB aux x =
      legacyCoreArmEval S b pa sim sigB t ∧
    ∀ p ∈ support (armEvalNew pa sim sigB aux x),
      FgSimShadowInv S b (bumpPred (authSimPred S) c t) p.2.1.1 p.2.2

/-- Bundled `FgArmSim` obligations for all twelve `AuthQuery` constructors. -/
structure AllFgArmsSim (S : Setup) (b : QueryBudget) : Prop where
  initPrin        : FgArmSim S b AuthQuery.initPrin (armEval_initPrin S b)
  corruptIK       : FgArmSim S b AuthQuery.corruptIK (armEval_corruptIK S b)
  genSPK          : FgArmSim S b (fun p => AuthQuery.genSPK p.1 p.2) (armEval_genSPK S b)
  genOPK          : FgArmSim S b (fun p => AuthQuery.genOPK p.1 p.2.1 p.2.2) (armEval_genOPK S b)
  sendOPK         : FgArmSim S b
    (fun p => AuthQuery.sendOPK p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (armEval_sendOPK S b)
  sendNoOPK       : FgArmSim S b
    (fun p => AuthQuery.sendNoOPK p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (armEval_sendNoOPK S b)
  recvOPK         : FgArmSim S b
    (fun p => AuthQuery.recvOPK p.1 p.2.1 p.2.2.1 p.2.2.2) (armEval_recvOPK S b)
  recvNoOPK       : FgArmSim S b
    (fun p => AuthQuery.recvNoOPK p.1 p.2.1 p.2.2.1 p.2.2.2) (armEval_recvNoOPK S b)
  roQuery         : FgArmSim S b AuthQuery.roQuery (armEval_roQuery S b)
  roRootQuery     : FgArmSim S b (fun p => AuthQuery.roRootQuery p.1 p.2) (armEval_roRootQuery S b)
  revealDhSecrets : FgArmSim S b (fun _ => AuthQuery.revealDhSecrets) (armEval_revealDhSecrets S b)
  registerKey     : FgArmSim S b AuthQuery.registerKey (armEval_registerKey S b)

/-- Simulation contract between `a1sSendCheckLegC` and `a1sSendCheckC` for `a1s2KindProg`. -/
@[expose] def SigSendCheckSim (S : Setup) (b : QueryBudget) : Prop :=
  ∀ (opk : Bool) (c : Fin 4 → ℕ) (s' : a1s2ShadowStTy.denote)
    (u : Fin S.N_id) (i : if opk then Fin S.N_send_opk else Fin S.N_send_no_opk)
    (bu : PreKeyBundleInput) (m0 m1 : Bytes),
    let t : AuthQuery S :=
      match opk, i with
      | true, i  => .sendOPK u i bu m0 m1
      | false, i => .sendNoOPK u i bu m0 m1
    let xVal : authSendQAtomicTy.denote :=
      (u.val, ((match opk, i with | true, i => i.val | false, i => i.val),
        (bundleV (ℓ := 0) (Pt := Empty) bu, (m0, m1))))
    (∀ j, c j ≤ authSimBounds b j) →
    (∀ j, authSimPred S j t → c j + 1 ≤ authSimBounds b j) →
    SigAuthInv S b c s' →
    s'.1.2.2.2 = none →
    (liftCs1 (a1sSendCheckLegC S (AuthKindFuels.ofBudget S b))
      (.pair (.fst (.var (.succ .zero))) (.var .zero))).eval
      (.cons xVal (.cons s' (.cons ((authCodec S).qenc t) .nil))) =
      (mapComp tlAuthSigDdh
        (a1sSendCheckC (Δ := [a1sStTy, sendQTy]) S b.q_total
          (.zero : Var [a1sStTy, sendQTy] a1sStTy)
          (.succ .zero : Var [a1sStTy, sendQTy] sendQTy))).eval
        (.cons s'.1 (.cons xVal .nil)) ∧
    ∀ r, Sum.inl r ∈ support
      ((liftCs1 (a1sSendCheckLegC S (AuthKindFuels.ofBudget S b))
        (.pair (.fst (.var (.succ .zero))) (.var .zero))).eval
        (.cons xVal (.cons s' (.cons ((authCodec S).qenc t) .nil)))) →
      SigAuthInv S b (bumpPred (authSimPred S) c t) (r.2, s'.2)

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
