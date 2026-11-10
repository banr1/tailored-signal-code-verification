/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB3
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopB2
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhC
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Fiedler–Günther `GapDH` reduction and bad events for `Auth`

Unfolds the `GdhSimSpec` Fiedler–Günther reduction `fgAuthGapDhAdv4` into pure candidate search,
proves its 2D index-guessing identity over `DH1` and `DH3`, and defines the sticky `G3 → G3.5`
cutoff bad events (`badAuthFgDh1LatchedAt`, `badAuthFgDh3At`, `badAuthFgAnyLatched`).
-/

@[expose] public section
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

@[simp] theorem fgGapDh_extractDh1_eq : FgGapDh.extractDh1 = extractDh1 := rfl
@[simp] theorem fgGapDh_extractDh3_eq : FgGapDh.extractDh3 = extractDh3 := rfl
@[simp] theorem fgGapDh_spkBundleFlatIdx_eq : FgGapDh.spkBundleFlatIdx = spkBundleFlatIdx := rfl

export _root_.SignalPqxdh.Security (FgRootEntry fgRootEntryMatches fgRootPatch AuthRespRecord FgAuthSimState fgRoQueryAuthGdh fgRoRootQueryAuthGdh fgRunSendAuthGdh fgFinishRecvStep2AuthGdh fgFinishRecvAuthGdh fgRunRecvOPKAuthGdh fgRunRecvNoOPKAuthGdh fgAuthStep isTargetPrinCorrupted fgAuthStepHalt sessionSenderIdx lookupSenderIkPk lookupAuthSpkSkFromPows initAuthDh1CandWithPowsGdh respAuthCandGdh respAuthDh1CandGdh respAuthDh3CandGdh initAuthDh3CandGdh extractCdhFromAuthSimState fgAuthGapDhRunAt fgAuthGapDhAdvAt fgAuthGapDhAdv4)

/-! ## Lazy root-KDF patching -/
def fgRootEntryMatchesPure (ddh : Bytes → Bytes → Bytes → Bool)
    (rk : Bytes) (dhPos : FgPoS) (e : FgRootEntry) : Bool :=
  if rk != e.rk then false else ddhEqPure ddh dhPos e.dhPos
@[simp]
theorem simulateQ_gapDhFullImpl_fgRootEntryMatches (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (rk : Bytes) (dhPos : FgPoS) (e : FgRootEntry) :
    simulateQ (gapDhFullImpl P ddh) (fgRootEntryMatches rk dhPos e) =
      pure (fgRootEntryMatchesPure ddh rk dhPos e) := by
  unfold fgRootEntryMatches fgRootEntryMatchesPure
  split_ifs
  · rfl
  · exact simulateQ_gapDhFullImpl_ddhEqGdh P ddh dhPos e.dhPos
def fgRootPatchPure (ddh : Bytes → Bytes → Bytes → Bool)
    (maxLen : ℕ) (rk : Bytes) (dhPos : FgPoS) (L : List FgRootEntry) :
    ProbComp ((Bytes × Bytes) × List FgRootEntry) := do
  match (L.take maxLen).find? (fgRootEntryMatchesPure ddh rk dhPos) with
  | some e => return ((e.rk1, e.ck1_0), L)
  | none =>
    let rk1 ← sampleBytes32
    let ck1_0 ← sampleBytes32
    return ((rk1, ck1_0), { rk := rk, dhPos := dhPos, rk1 := rk1, ck1_0 := ck1_0 } :: L)
@[simp]
theorem simulateQ_gapDhFullImpl_fgRootPatch (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (maxLen : ℕ) (rk : Bytes) (dhPos : FgPoS) (L : List FgRootEntry) :
    simulateQ (gapDhFullImpl P ddh) (fgRootPatch maxLen rk dhPos L) =
      fgRootPatchPure ddh maxLen rk dhPos L := by
  unfold fgRootPatch fgRootPatchPure
  rw [simulateQ_bind,
      simulateQ_gapDhFullImpl_findMGdh P ddh (fgRootEntryMatches rk dhPos)
        (fgRootEntryMatchesPure ddh rk dhPos)
        (simulateQ_gapDhFullImpl_fgRootEntryMatches P ddh rk dhPos) (L.take maxLen),
      pure_bind]
  cases (L.take maxLen).find? (fgRootEntryMatchesPure ddh rk dhPos) <;> simp

/-! ## Pure CDH candidate extraction and 2D index decomposition -/

@[simp]
theorem fgAuthStepHalt_false (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes)
    (q : AuthQuery S) (st : FgAuthSimState S) :
    fgAuthStepHalt false targetIdx targetSpkIdx S maxLen U V q st =
      fgAuthStep false targetIdx targetSpkIdx S maxLen U V q st := rfl

def initAuthDh3Cand {S : Setup} (P : Primitives) (s' : AuthInitiatorEntry S) : Bytes :=
  if s'.ekASk.isEmpty then List.replicate 32 0
  else P.x25519 s'.ekASk s'.peerSpkPk

/-- Looks up a non-erased SPK secret scalar matching `wSpk` in the first `S.N_dh` bundles, falling back to `advKeyPows`. -/
def lookupAuthSpkSkTake (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (spkPk : Bytes) : Bytes :=
  let wSpk := P.pow8 spkPk
  match (spkBundles.take S.N_dh).find?
      (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == wSpk) with
  | some (_, b) => b.spkSk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => sk
    | none => []
theorem lookupAuthSpkSkFromPows_map_eq (P : Primitives)
    (advKeyPows : List (Bytes × Bytes)) (wSpk : Bytes) :
    ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
      lookupAuthSpkSkFromPows (spkPowsPure P L) advKeyPows wSpk =
        match L.find? (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == wSpk) with
        | some (_, b) => b.spkSk
        | none =>
          match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
          | some (sk, _) => sk
          | none => []
  | [] => rfl
  | (_, b) :: tl => by
    unfold spkPowsPure lookupAuthSpkSkFromPows
    simp only [List.map_cons, List.find?_cons]
    cases (!b.spkSk.isEmpty && P.pow8 b.spkPk == wSpk)
    · exact lookupAuthSpkSkFromPows_map_eq P advKeyPows wSpk tl
    · rfl
def initAuthDh1Cand (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : AuthInitiatorEntry S) : Bytes :=
  let spkSk := lookupAuthSpkSkTake S P spkBundles advKeyPows s.peerSpkPk
  let ikAPk := lookupSenderIkPk principals (sessionSenderIdx s.sid)
  P.x25519 spkSk ikAPk
@[simp]
theorem simulateQ_gapDhFullImpl_initAuthDh1CandWithPowsGdh (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : AuthInitiatorEntry S) :
    simulateQ (gapDhFullImpl P ddh)
      (initAuthDh1CandWithPowsGdh principals
        (spkPowsPure P (spkBundles.take S.N_dh)) advKeyPows s) =
      pure (initAuthDh1Cand S P principals spkBundles advKeyPows s) := by
  unfold initAuthDh1CandWithPowsGdh initAuthDh1Cand lookupAuthSpkSkTake
  simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_pow8,
    simulateQ_gapDhFullImpl_primGdhQ_x25519, pure_bind]
  rw [lookupAuthSpkSkFromPows_map_eq P advKeyPows (P.pow8 s.peerSpkPk) (spkBundles.take S.N_dh)]
def respAuthCand (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bKey : Nat × Nat) (pk : Bytes) : Bytes :=
  let spkSk := match (spkBundles.take S.N_dh).find? (fun (idx, _) => idx == bKey) with
    | some (_, b) => b.spkSk
    | none => []
  P.x25519 spkSk pk
@[simp]
theorem simulateQ_gapDhFullImpl_respAuthCandGdh (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bKey : Nat × Nat) (pk : Bytes) :
    simulateQ (gapDhFullImpl P ddh) (respAuthCandGdh S spkBundles bKey pk) =
      pure (respAuthCand S P spkBundles bKey pk) := by
  unfold respAuthCandGdh respAuthCand; simp
  rcases List.find? (fun x => x.1 == bKey) (List.take S.N_dh spkBundles) with _ | ⟨_, _⟩ <;> rfl
abbrev respAuthDh1Cand (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (r : AuthRespRecord) : Bytes :=
  respAuthCand S P spkBundles r.bKey r.ikAPk
abbrev respAuthDh3Cand (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (r : AuthRespRecord) : Bytes :=
  respAuthCand S P spkBundles r.bKey r.ekAPk
@[simp]
theorem simulateQ_gapDhFullImpl_initAuthDh3CandGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (s' : AuthInitiatorEntry S) :
    simulateQ (gapDhFullImpl P ddh) (initAuthDh3CandGdh s') = pure (initAuthDh3Cand P s') := by
  unfold initAuthDh3CandGdh initAuthDh3Cand; split_ifs <;> simp
def pureExtractCdhFromAuthSimState (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (st : FgAuthSimState S) : Bytes :=
  if useDh1 then
    match ((st.advRoLog.take maxLen).map extractDh1).find? (fun z => ddh U V z) with
    | some z => z
    | none =>
      match ((st.base.sessions.take S.N_dh).map
          (initAuthDh1Cand S P st.base.principals st.base.spkBundles st.advKeyPows)).find?
          (fun z => ddh U V z) with
      | some z => z
      | none =>
        match ((st.respRecs.take S.N_sess_tot).map
            (respAuthDh1Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) with
        | some z => z
        | none   => List.replicate 32 0
  else
    match ((st.advRoLog.take maxLen).map extractDh3).find? (fun z => ddh U V z) with
    | some z => z
    | none =>
      match ((st.base.sessions.take S.N_dh).map (initAuthDh3Cand P)).find? (fun z => ddh U V z) with
      | some z => z
      | none =>
        match ((st.respRecs.take S.N_sess_tot).map
            (respAuthDh3Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) with
        | some z => z
        | none   => List.replicate 32 0
@[simp]
theorem simulateQ_gapDhFullImpl_extractCdhFromAuthSimState (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (st : FgAuthSimState S) :
    simulateQ (gapDhFullImpl P ddh) (extractCdhFromAuthSimState S useDh1 maxLen U V st) =
      pure (pureExtractCdhFromAuthSimState S P ddh useDh1 maxLen U V st) := by
  unfold extractCdhFromAuthSimState pureExtractCdhFromAuthSimState
  rw [fgGapDh_extractDh1_eq, fgGapDh_extractDh3_eq]
  split_ifs with hDh1
  · rw [simulateQ_bind,
        simulateQ_gapDhFullImpl_findMGdh P ddh (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
          (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z)
          ((st.advRoLog.take maxLen).map extractDh1),
        pure_bind]
    cases ((st.advRoLog.take maxLen).map extractDh1).find? (fun z => ddh U V z) with
    | some z => rfl
    | none =>
      rw [simulateQ_bind,
          simulateQ_gapDhFullImpl_spkPowsGdh P ddh (st.base.spkBundles.take S.N_dh),
          pure_bind, simulateQ_bind,
          simulateQ_gapDhFullImpl_findMapMGdh P ddh
            (initAuthDh1CandWithPowsGdh (S := S) st.base.principals
              (spkPowsPure P (st.base.spkBundles.take S.N_dh)) st.advKeyPows)
            (initAuthDh1Cand S P st.base.principals st.base.spkBundles st.advKeyPows) U V
            (fun s => simulateQ_gapDhFullImpl_initAuthDh1CandWithPowsGdh S P ddh
              st.base.principals st.base.spkBundles st.advKeyPows s)
            (st.base.sessions.take S.N_dh),
          pure_bind]
      cases ((st.base.sessions.take S.N_dh).map
          (initAuthDh1Cand S P st.base.principals st.base.spkBundles st.advKeyPows)).find?
          (fun z => ddh U V z) with
      | some z => rfl
      | none =>
        rw [simulateQ_bind,
            simulateQ_gapDhFullImpl_findMapMGdh P ddh
              (respAuthDh1CandGdh S st.base.spkBundles)
              (respAuthDh1Cand S P st.base.spkBundles) U V
              (fun r =>
                simulateQ_gapDhFullImpl_respAuthCandGdh S P ddh st.base.spkBundles r.bKey r.ikAPk)
              (st.respRecs.take S.N_sess_tot),
            pure_bind]
        cases ((st.respRecs.take S.N_sess_tot).map
            (respAuthDh1Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) <;> rfl
  · rw [simulateQ_bind,
        simulateQ_gapDhFullImpl_findMGdh P ddh (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
          (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z)
          ((st.advRoLog.take maxLen).map extractDh3),
        pure_bind]
    cases ((st.advRoLog.take maxLen).map extractDh3).find? (fun z => ddh U V z) with
    | some z => rfl
    | none =>
      rw [simulateQ_bind,
          simulateQ_gapDhFullImpl_findMapMGdh P ddh
            initAuthDh3CandGdh (initAuthDh3Cand P) U V
            (fun s' => simulateQ_gapDhFullImpl_initAuthDh3CandGdh P ddh s')
            (st.base.sessions.take S.N_dh),
          pure_bind]
      cases ((st.base.sessions.take S.N_dh).map (initAuthDh3Cand P)).find? (fun z => ddh U V z) with
      | some z => rfl
      | none =>
        rw [simulateQ_bind,
            simulateQ_gapDhFullImpl_findMapMGdh P ddh
              (respAuthDh3CandGdh S st.base.spkBundles)
              (respAuthDh3Cand S P st.base.spkBundles) U V
              (fun r =>
                simulateQ_gapDhFullImpl_respAuthCandGdh S P ddh st.base.spkBundles r.bKey r.ekAPk)
              (st.respRecs.take S.N_sess_tot),
            pure_bind]
        cases ((st.respRecs.take S.N_sess_tot).map
            (respAuthDh3Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) <;> rfl
noncomputable def fgAuthSimImpl (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (authSpec S) (StateT (FgAuthSimState S) ProbComp) :=
  fun gq => StateT.mk (fun st =>
    simulateQ (gapDhFullImpl P ddh)
      (fgAuthStepHalt useDh1 targetIdx targetSpkIdx S maxLen U V gq st))
theorem simulateQ_gapDhFullImpl_fgAuthGapDhRunAt
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (U V : Bytes) :
    simulateQ (gapDhFullImpl P ddh)
      (fgAuthGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V) =
    (do
      let secb ← $ᵗ Bool
      let initSt := FgAuthSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgAuthSimState S) ProbComp) +
        fgAuthSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return pureExtractCdhFromAuthSimState S P ddh useDh1 b.q_total U V finalSt) := by
  unfold fgAuthGapDhRunAt
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh]
  congr 1; ext secb
  rw [simulateQ_bind,
      simulateQ_gapDhFullImpl_runWithGdhStep P ddh
        (fgAuthStepHalt useDh1 targetIdx targetSpkIdx S b.q_total U V)
        (fgAuthSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V)
        (fun _ _ => rfl)]
  congr 1; ext res
  exact simulateQ_gapDhFullImpl_extractCdhFromAuthSimState S P ddh useDh1 b.q_total U V res.2
theorem gapDhExp_fgAuthGapDhAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    gapDhExp P ddh pow8 (fgAuthGapDhAdvAt useDh1 targetIdx targetSpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgAuthSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgAuthSimState S) ProbComp) +
        fgAuthSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdhFromAuthSimState S P ddh useDh1 b.q_total U V finalSt) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhExp fgAuthGapDhAdvAt
  dsimp only [gapDhFullImpl, gapDhDdhImpl]
  congr 1; ext u; congr 1; ext v
  change (simulateQ (gapDhFullImpl P ddh)
      (fgAuthGapDhRunAt useDh1 targetIdx targetSpkIdx S b A (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhFullImpl_fgAuthGapDhRunAt]
  simp only [bind_assoc, pure_bind]
theorem evalDist_gapDhExp_fgAuthGapDhAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[gapDhExp P ddh pow8 (fgAuthGapDhAdv4 S b A)] =
    𝒟[do
      let (flatIdx, bIdx) ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
      if flatIdx < S.N_id then
        gapDhExp P ddh pow8 (fgAuthGapDhAdvAt true flatIdx bIdx S b A)
      else
        gapDhExp P ddh pow8 (fgAuthGapDhAdvAt false (flatIdx - S.N_id) bIdx S b A)] := by
  have hSim : ∀ U V,
      simulateQ (gapDhFullImpl P ddh) ((fgAuthGapDhAdv4 S b A).run U V) =
      (do
        let (flatIdx, bIdx) ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        if flatIdx < S.N_id then
          simulateQ (gapDhFullImpl P ddh) (fgAuthGapDhRunAt true flatIdx bIdx S b A U V)
        else
          simulateQ (gapDhFullImpl P ddh)
            (fgAuthGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V)) := by
    intro U V
    change simulateQ (gapDhFullImpl P ddh)
      (unifGdh (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) >>= fun p =>
        if p.1 < S.N_id then
          fgAuthGapDhRunAt true p.1 p.2 S b A U V
        else
          fgAuthGapDhRunAt false (p.1 - S.N_id) p.2 S b A U V) = _
    rw [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh]
    congr 1; ext ⟨flatIdx, bIdx⟩; dsimp only; split_ifs <;> rfl
  have hStep1 :
      gapDhExp P ddh pow8 (fgAuthGapDhAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let (flatIdx, bIdx) ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let U := P.x25519Base u
        let V := P.x25519Base v
        let Z ← if flatIdx < S.N_id then
            simulateQ (gapDhFullImpl P ddh) (fgAuthGapDhRunAt true flatIdx bIdx S b A U V)
          else
            simulateQ (gapDhFullImpl P ddh)
              (fgAuthGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V)
        return (pow8 Z == pow8 (P.x25519 u V))) := by
    unfold gapDhExp
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhFullImpl P ddh)
        ((fgAuthGapDhAdv4 S b A).run (P.x25519Base u) (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [hSim, bind_assoc]
    congr 1; ext ⟨flatIdx, bIdx⟩; dsimp only; split_ifs <;> rfl
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let (flatIdx, bIdx) ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let U := P.x25519Base u
        let V := P.x25519Base v
        let Z ← if flatIdx < S.N_id then
            simulateQ (gapDhFullImpl P ddh) (fgAuthGapDhRunAt true flatIdx bIdx S b A U V)
          else
            simulateQ (gapDhFullImpl P ddh)
              (fgAuthGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V)
        return (pow8 Z == pow8 (P.x25519 u V))] =
      𝒟[do
        let u ← sampleScalar32
        let (flatIdx, bIdx) ← sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot
        let v ← sampleScalar32
        let U := P.x25519Base u
        let V := P.x25519Base v
        let Z ← if flatIdx < S.N_id then
            simulateQ (gapDhFullImpl P ddh) (fgAuthGapDhRunAt true flatIdx bIdx S b A U V)
          else
            simulateQ (gapDhFullImpl P ddh)
              (fgAuthGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V)
        return (pow8 Z == pow8 (P.x25519 u V))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)]
  refine OracleComp.evalDist_bind_congr_of_support
    (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot) _ _ (fun ⟨flatIdx, bIdx⟩ _ => ?_)
  dsimp only; split_ifs <;> rfl
/-- Decomposes `(S.N_id + S.N_send_tot) * S.N_spk_tot * GapDH P ddh pow8 (fgAuthGapDhAdv4 S b A)` into the sum over `DH1` and `DH3` target slots. -/
theorem sum_gapDh_fgAuthGapDhAdvAt_eq (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDH P ddh pow8 (fgAuthGapDhAdvAt true u bIdx S b A)) +
    (∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDH P ddh pow8 (fgAuthGapDhAdvAt false idx bIdx S b A)) =
    (S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) *
      GapDH P ddh pow8 (fgAuthGapDhAdv4 S b A) := by
  have hExp := evalDist_gapDhExp_fgAuthGapDhAdv4_eq P ddh pow8 S b A
  have hDouble := mul_toReal_sampleIndexRange2_bind_eq_double_sum_fg
    (S.N_id + S.N_send_tot) S.N_spk_tot
    (fun flatIdx bIdx =>
      if flatIdx < S.N_id then
        gapDhExp P ddh pow8 (fgAuthGapDhAdvAt true flatIdx bIdx S b A)
      else
        gapDhExp P ddh pow8 (fgAuthGapDhAdvAt false (flatIdx - S.N_id) bIdx S b A))
  have hRhs :
      (S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) *
        GapDH P ddh pow8 (fgAuthGapDhAdv4 S b A) =
      ∑ flatIdx ∈ Finset.range (S.N_id + S.N_send_tot), ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[if flatIdx < S.N_id then
            gapDhExp P ddh pow8 (fgAuthGapDhAdvAt true flatIdx bIdx S b A)
          else
            gapDhExp P ddh pow8
              (fgAuthGapDhAdvAt false (flatIdx - S.N_id) bIdx S b A)] {true}).toReal := by
    unfold GapDH; rw [hExp, ← hDouble]; push_cast; ring
  rw [hRhs, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun bIdx _ => ?_))
    rw [Finset.mem_range] at hu; simp [hu, GapDH]
  · refine Finset.sum_congr rfl (fun idx _ => Finset.sum_congr rfl (fun bIdx _ => ?_))
    have hnot : ¬ (S.N_id + idx < S.N_id) := by omega
    simp [hnot, GapDH]

/-! ## Cutoff bad events and union bound -/

/-- `Auth` state augmented with the adversary RO log, responder handshake records, and latched `DH1` pairs. -/
structure AuthFgCutoffState (S : Setup) where
  base       : AuthState S
  advRoLog   : List Bytes := []
  respRecs   : List AuthRespRecord := []
  latchedDh1 : List (Nat × Nat) := []
def AuthFgCutoffState.empty (S : Setup) (secb : Bool) : AuthFgCutoffState S :=
  { base := AuthState.empty S secb }
/-- Per-index `DH1 = CDH(ik_U*, spk_V*)` bad event at `(uIdx, bIdx)`. -/
def badAuthFgDh1At {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  match st.principals.find? (fun (u, _) => u == uIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some (_, uEntry), some (_, bEntry) =>
    let zTarget := P.x25519 uEntry.secIKA0 bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    let advKeyPows := st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))
    !uEntry.corrupted &&
    ((advRoLog.take maxLen).any (fun sec => extractDh1 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s =>
       initAuthDh1Cand S P st.principals spkErased advKeyPows s == zTarget) ||
     (respRecs.take S.N_sess_tot).any (fun r =>
       respAuthDh1Cand S P spkErased r == zTarget))
  | _, _ => false
/-- Per-index `DH3 = CDH(ek_U*, spk_V*)` bad event at `(sIdx, bIdx)`. -/
def badAuthFgDh3At {S : Setup} (P : Primitives) (maxLen sIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord) : Bool :=
  match st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some s, some (_, bEntry) =>
    let zTarget := P.x25519 s.ekASk bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    (P.pow8 s.peerSpkPk == P.pow8 bEntry.spkPk) &&
    ((advRoLog.take maxLen).any (fun sec => extractDh3 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s' =>
       initSessionSlotIdx s'.sid != sIdx && P.x25519 s'.ekASk s'.peerSpkPk == zTarget) ||
     (respRecs.take S.N_sess_tot).any (fun r =>
       respAuthDh3Cand S P spkErased r == zTarget))
  | _, _ => false
def latchDh1ForPrincipal (S : Setup) (P : Primitives) (uVal : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (latched : List (Nat × Nat)) : List (Nat × Nat) :=
  ((List.range S.N_spk_tot).filter (fun bIdx =>
    badAuthFgDh1At P advRoLog.length uVal bIdx st advRoLog respRecs)).map
      (fun bIdx => (uVal, bIdx)) ++ latched

/-- Sticky `DH1` bad event at `(uIdx, bIdx)`, latching before `.corruptIK` marks `uIdx` corrupted. -/
def badAuthFgDh1LatchedAt {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (hst : AuthFgCutoffState S) : Bool :=
  hst.latchedDh1.contains (uIdx, bIdx) ||
    badAuthFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog hst.respRecs

/-- Disjunction of `badAuthFgDh1LatchedAt` and `badAuthFgDh3At` over all target index pairs. -/
def badAuthFgAnyLatched {S : Setup} (P : Primitives) (maxLen : ℕ)
    (hst : AuthFgCutoffState S) : Bool :=
  ((List.range S.N_id).any (fun uIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badAuthFgDh1LatchedAt P maxLen uIdx bIdx hst))) ||
  ((List.range S.N_send_tot).any (fun sIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badAuthFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog hst.respRecs)))

theorem prob_badAuthFgAnyLatched_le_sum {S : Setup} (P : Primitives) (maxLen : ℕ)
    {α : Type} (mx : ProbComp α) (proj : α → AuthFgCutoffState S) :
    (𝒟[mx >>= fun x => pure (badAuthFgAnyLatched P maxLen (proj x))] {true}).toReal ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh1LatchedAt P maxLen uIdx bIdx (proj x))] {true}).toReal) +
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh3At P maxLen sIdx bIdx
            (proj x).base (proj x).advRoLog (proj x).respRecs)] {true}).toReal) := by
  unfold badAuthFgAnyLatched
  have hOr := prob_or_le_add_fg mx
    (fun x => (List.range S.N_id).any (fun uIdx =>
      (List.range S.N_spk_tot).any (fun bIdx =>
        badAuthFgDh1LatchedAt P maxLen uIdx bIdx (proj x))))
    (fun x => (List.range S.N_send_tot).any (fun sIdx =>
      (List.range S.N_spk_tot).any (fun bIdx =>
        badAuthFgDh3At P maxLen sIdx bIdx
          (proj x).base (proj x).advRoLog (proj x).respRecs)))
  have hDh1 := toReal_any_double_range_le_sum2 mx S.N_id S.N_spk_tot
    (fun uIdx bIdx x => badAuthFgDh1LatchedAt P maxLen uIdx bIdx (proj x))
  have hDh3 := toReal_any_double_range_le_sum2 mx S.N_send_tot S.N_spk_tot
    (fun sIdx bIdx x => badAuthFgDh3At P maxLen sIdx bIdx
      (proj x).base (proj x).advRoLog (proj x).respRecs)
  linarith

/-- Bounds the probability of `badAuthFgAnyLatched` by `(S.N_id + S.N_send_tot) * S.N_spk_tot` times the `GapDH` advantage of `fgAuthGapDhAdv4`. -/
theorem prob_badAuthFgAnyLatched_le_gapDh_of_dh1_dh3 {S : Setup} (b : QueryBudget)
    (P : Primitives) (A : BoundedAdv (AuthAdversary S) b)
    {α : Type} (mx : ProbComp α) (proj : α → AuthFgCutoffState S)
    (hDh1 : ∀ uIdx ∈ Finset.range S.N_id, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[mx >>= fun x =>
          pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx (proj x))] {true}).toReal ≤
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt true uIdx bIdx S b A))
    (hDh3 : ∀ sIdx ∈ Finset.range S.N_send_tot, ∀ bIdx ∈ Finset.range S.N_spk_tot,
      (𝒟[mx >>= fun x =>
          pure (badAuthFgDh3At P b.q_ro sIdx bIdx
            (proj x).base (proj x).advRoLog (proj x).respRecs)] {true}).toReal ≤
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt false sIdx bIdx S b A)) :
    (𝒟[mx >>= fun x => pure (badAuthFgAnyLatched P b.q_ro (proj x))] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) := by
  have hUnion := prob_badAuthFgAnyLatched_le_sum P b.q_ro mx proj
  have hSumDh1 :
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh1LatchedAt P b.q_ro uIdx bIdx (proj x))] {true}).toReal) ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt true uIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun uIdx huIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => hDh1 uIdx huIdx bIdx hbIdx))
  have hSumDh3 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badAuthFgDh3At P b.q_ro sIdx bIdx
            (proj x).base (proj x).advRoLog (proj x).respRecs)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdvAt false sIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => hDh3 sIdx hsIdx bIdx hbIdx))
  have hEq := sum_gapDh_fgAuthGapDhAdvAt_eq S P P.isValidDhTriple P.pow8 b A
  have hNonnegGdh : 0 ≤ GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) :=
    gapDh_nonneg P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A)
  have hExtraNonneg : 0 ≤ ((S.N_id : ℝ) * (S.N_send_tot : ℝ) +
      (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
      GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) := by
    positivity
  linarith

end Proofs.SignalPqxdh.Security
