/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCLazy
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import LibsignalBinary.Specifications.CryptoGames.Primitives

/-!
# Hop 1 of `cbc_indcpa`: Real IND-CPA Branch Equals Real PRF Branch

**Checked by Lean.**

Proves `CryptoGames.CBC.Hop1.cbc_branch_false_eq`:
`𝒟[(cbcScheme E encode).branch false A] = 𝒟[(blockPRF E).branch false (cbcRed encode A)]`,
relating eager and lazy uniform IV sampling via `CryptoGames.Lazy.Comm.simulateQ`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy CryptoGames.AEADScheme.EtMProof
namespace CryptoGames
namespace CBC
namespace Hop1

private def prfImpl (E : AesKey → Block → Block) :
    QueryImpl (unifSpec + MACScheme.prfSpec Block Block)
      (StateT (MACScheme.PRFState AesKey Block Block) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (MACScheme.PRFState AesKey Block Block) ProbComp) + MACScheme.prfEval (blockPRF E)

private def fillIv : Bool → Option Block → ProbComp (Option Block)
  | _, some iv => pure (some iv)
  | _, none => some <$> ($ᵗ Block)

private theorem fillIv_idem : Idem fillIv := by
  intro _ sl
  cases sl with
  | some iv => exact DEq.of_eq (by simp [fillIv])
  | none =>
    exact DEq.of_eq (by
      simp only [fillIv, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      rfl)

private def implSlot {M : Type} {n : ℕ} (f : Block → Block)
    (encode : M → List.Vector Block n) :
    QueryImpl (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n))
      (StateT (Bool × Option Block) ProbComp)
  | .inl m => AEADScheme.EtMProof.coin m
  | .inr msg => StateT.mk fun s =>
      if s.1 then pure (none, (true, s.2))
      else match s.2 with
      | some iv => pure (some (cbcEncrypt f iv (encode msg)), (true, some iv))
      | none => (fun iv => (some (cbcEncrypt f iv (encode msg)), (true, some iv))) <$> ($ᵗ Block)

private theorem implSlot_comm {M : Type} {n : ℕ} (f : Block → Block)
    (encode : M → List.Vector Block n) :
    ∀ t, Comm fillIv (implSlot f encode t) := by
  intro t ⟨qd, sl⟩
  rcases t with m | msg
  · have hcoin (x : Bool × Option Block) :
        (AEADScheme.EtMProof.coin m).run x =
          (liftM (OracleSpec.query (spec := unifSpec) m) : ProbComp (Fin (m + 1))) >>=
            fun u => pure (u, x) := by
      simp [AEADScheme.EtMProof.coin]
    simp only [implSlot, hcoin, bind_assoc]
    refine (DEq.swap (fillSt fillIv (qd, sl)) _ _).trans ?_
    refine DEq.bind_right _ fun u => ?_
    simp only [pure_bind, fillOut]
    have h := DEq.map (fillSt_idem fillIv_idem (qd, sl)) (u, ·)
    simpa only [map_bind] using h
  · cases qd
    · cases sl with
      | some iv =>
        exact DEq.of_eq (by simp [fillSt, fillIv, implSlot, fillOut])
      | none =>
        exact DEq.of_eq (by
          simp [fillSt, fillIv, implSlot, fillOut, map_eq_bind_pure_comp, bind_assoc])
    · have h := DEq.map (fillSt_idem fillIv_idem (true, sl))
        ((none : Option (List.Vector Block n)), ·)
      simpa only [implSlot, StateT.run_mk, fillOut, fillSt, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind, ↓reduceIte] using h

private theorem eager_eq_implSlot {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n) (k : AesKey) (iv : Block)
    {α : Type} (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n)) α)
    (s : CipherScheme.INDCPAState (AesKey × Block))
    (hs : s.key = (k, iv) ∧ s.b = false) :
    (simulateQ (implSlot (E k) encode) oa).run (s.queried, some iv) =
      Prod.map id (fun z => (z.queried, some iv)) <$>
        (simulateQ (cImpl (cbcScheme E encode)) oa).run s := by
  refine run_map (implSlot (E k) encode) (cImpl (cbcScheme E encode))
    (fun z => (z.queried, some iv)) (fun z => z.key = (k, iv) ∧ z.b = false)
    (fun t z ⟨hzk, hzb⟩ => ?_) oa s hs
  rcases t with m | msg
  · refine ⟨by simp [implSlot, cImpl, AEADScheme.EtMProof.coin], fun w hw => ?_⟩
    have hw' : w ∈ support ((AEADScheme.EtMProof.coin m : StateT _ ProbComp _).run z) := by
      simpa [cImpl] using hw
    rw [mem_support_coin hw']; exact ⟨hzk, hzb⟩
  · by_cases hq : z.queried = true
    · refine ⟨by simp [implSlot, cImpl, CipherScheme.indcpaEncrypt, hq], fun w hw => ?_⟩
      simp [cImpl, CipherScheme.indcpaEncrypt, hq] at hw
      subst hw; exact ⟨hzk, hzb⟩
    · have hqf : z.queried = false := Bool.eq_false_iff.mpr hq
      refine ⟨?_, fun w hw => ?_⟩
      · simp [implSlot, cImpl, CipherScheme.indcpaEncrypt, cbcScheme, hqf, hzk, hzb]
      · simp [cImpl, CipherScheme.indcpaEncrypt, hqf, hzb] at hw
        subst hw; exact ⟨hzk, rfl⟩

private theorem simulateQ_prfImpl_cbcM {n : ℕ} (E : AesKey → Block → Block)
    (iv : Block) (P : List.Vector Block n)
    (pst : MACScheme.PRFState AesKey Block Block) (hb : pst.b = false) :
    (simulateQ (prfImpl E) (cbcM MACScheme.evalQuery iv P)).run pst =
      pure (cbcEncrypt (E pst.key) iv P, pst) := by
  induction n generalizing iv with
  | zero => simp [cbcM, cbcEncrypt]
  | succ n ih =>
    simp only [cbcM, cbcEncrypt, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    have hev : (simulateQ (prfImpl E) (MACScheme.evalQuery (P.head ^^^ iv))).run pst =
        pure (E pst.key (P.head ^^^ iv), pst) := by
      simp [prfImpl, MACScheme.evalQuery, MACScheme.prfEval, blockPRF, hb]
    rw [hev, pure_bind, ih (E pst.key (P.head ^^^ iv)) P.tail, pure_bind]

private theorem lazy_eq_implSlot {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n) (k : AesKey)
    {α : Type} (oa : OracleComp (unifSpec + CipherScheme.indcpaSpec M (List.Vector Block n)) α) :
    ∀ (qd : Bool) (sl : Option Block) (pst : MACScheme.PRFState AesKey Block Block),
      (qd = false → sl = none) → pst.key = k → pst.b = false →
      (fun w => w.1.1) <$>
        (simulateQ (prfImpl E) ((simulateQ (cbcRedImpl encode) oa).run qd)).run pst =
      Prod.fst <$> (simulateQ (implSlot (E k) encode) oa).run (qd, sl) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro qd sl pst _ _ _
    simp
  | query_bind t cont ih =>
    intro qd sl pst hqd hpk hpb
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rcases t with m | msg
    · have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inl m)).run qd)).run pst =
          (liftM (OracleSpec.query (spec := unifSpec) m) : ProbComp (Fin (m + 1))) >>=
            fun u => pure ((u, qd), pst) := by
        simp [cbcRedImpl, prfImpl]
      have hR : (implSlot (E k) encode (.inl m)).run (qd, sl) =
          (liftM (OracleSpec.query (spec := unifSpec) m) : ProbComp (Fin (m + 1))) >>=
            fun u => pure (u, (qd, sl)) := by
        simp [implSlot, AEADScheme.EtMProof.coin]
      rw [hL, hR]
      simp only [bind_assoc, pure_bind]
      exact bind_congr fun u => ih u qd sl pst hqd hpk hpb
    · cases qd
      · have hsil : sl = none := hqd rfl
        subst hsil
        have hrun : (cbcRedImpl encode (.inr msg)).run false =
            (do
              let iv ← liftM ($ᵗ Block : ProbComp Block)
              let c ← cbcM MACScheme.evalQuery iv (encode msg)
              pure (some c, true)) := by
          simp [cbcRedImpl]
        have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inr msg)).run false)).run pst =
            ($ᵗ Block) >>= fun iv =>
              pure ((some (cbcEncrypt (E k) iv (encode msg)), true), pst) := by
          rw [hrun]
          have hlift : (simulateQ (prfImpl E)
              (liftM ($ᵗ Block : ProbComp Block) :
                OracleComp (unifSpec + MACScheme.prfSpec Block Block) Block)).run pst =
              ($ᵗ Block) >>= fun iv => pure (iv, pst) := by
            simp [prfImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]
          simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hlift,
            bind_assoc, pure_bind]
          refine bind_congr fun iv => ?_
          rw [simulateQ_prfImpl_cbcM E iv (encode msg) pst hpb, hpk, pure_bind]
        have hR : (implSlot (E k) encode (.inr msg)).run (false, none) =
            ($ᵗ Block) >>= fun iv =>
              pure (some (cbcEncrypt (E k) iv (encode msg)), (true, some iv)) := by
          simp [implSlot, map_eq_bind_pure_comp]
        rw [hL, hR]
        simp only [bind_assoc, pure_bind]
        exact bind_congr fun iv => ih _ true (some iv) pst (by intro h; cases h) hpk hpb
      · have hL : (simulateQ (prfImpl E) ((cbcRedImpl encode (.inr msg)).run true)).run pst =
            pure ((none, true), pst) := by
          simp [cbcRedImpl]
        have hR : (implSlot (E k) encode (.inr msg)).run (true, sl) =
            pure (none, (true, sl)) := by
          simp [implSlot]
        rw [hL, hR, pure_bind, pure_bind]
        exact ih none true sl pst (by intro h; cases h) hpk hpb

theorem cbc_branch_false_eq {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    𝒟[(cbcScheme E encode).branch false A] = 𝒟[(blockPRF E).branch false (cbcRed encode A)] := by
  rw [cipher_branch_eq, uniform_prod AesKey Block]
  unfold MACScheme.branch
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr ($ᵗ AesKey) _ _ fun k => ?_
  have hcomm := Comm.simulateQ fillIv_idem (implSlot_comm (E k) encode) A (false, none)
  have hmap := DEq.map hcomm (fun z : Bool × (Bool × Option Block) => z.1)
  have hdeq : DEq
      (Prod.fst <$> (fillSt fillIv (false, none) >>= (simulateQ (implSlot (E k) encode) A).run))
      (Prod.fst <$> (simulateQ (implSlot (E k) encode) A).run (false, none)) :=
    (map_fillOut (fun a _ => a) _).symm.trans (hmap.trans (map_fillOut (fun a _ => a) _))
  have heager :
      (do let iv ← $ᵗ Block
          (simulateQ (cImpl (cbcScheme E encode)) A).run' { key := (k, iv), b := false }) =
      Prod.fst <$> (fillSt fillIv (false, none) >>= (simulateQ (implSlot (E k) encode) A).run) := by
    simp only [fillSt, fillIv, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind,
      StateT.run'_eq]
    refine bind_congr fun iv => ?_
    have he := congrArg (Prod.fst <$> ·)
      (eager_eq_implSlot E encode k iv A { key := (k, iv), b := false } ⟨rfl, rfl⟩)
    simpa [Functor.map_map, map_eq_bind_pure_comp] using he.symm
  have hlazy :
      (simulateQ (prfImpl E) (cbcRed encode A)).run' { key := k, b := false } =
      Prod.fst <$> (simulateQ (implSlot (E k) encode) A).run (false, none) := by
    unfold cbcRed prfImpl
    have hl := lazy_eq_implSlot E encode k A false none { key := k, b := false }
      (fun _ => rfl) rfl rfl
    simpa [prfImpl, StateT.run'_eq, simulateQ_map, Functor.map_map] using hl
  change 𝒟[_] = 𝒟[(simulateQ (prfImpl E) (cbcRed encode A)).run' { key := k, b := false }]
  rw [heager, hlazy]
  exact DEq.evalDist_eq hdeq

end Hop1
end CBC
end CryptoGames
