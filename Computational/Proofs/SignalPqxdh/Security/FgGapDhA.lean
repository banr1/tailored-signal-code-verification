/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndGapDh
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.QueryTracking.SubSpec

@[expose] public section

/-!
# Query Bounds and Pure Semantics of the Fiedler–Günther `GapDH` Reduction

DDH- and primitive-query bounds for the helpers of the `KeyInd` → `GapDH` reduction, and the
`simulateQ` characterization of those helpers under `gapDhFullImpl` by pure functions.
-/

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh
export _root_.SignalPqxdh.Security.FgGapDh (embedUnif embedPrim unifGdh primGdhQ ddhGdhQ findMGdh anyMGdh findMapMGdh spkPowsGdh FgPoS FgPatchEntry mkSecretPos mkPairPos computeTwoSideOrPairPos computeOptPos ddhEqGdh ddhEqOptGdh fgEntryMatches fgPatch primQ findMPrim anyMPrim findHonestPrincipalPrim resolveSigPkPrim isHonestUncorruptedPeerPrim checkBundleProvenancePrim isAdvRegisteredPows koskSenderOkPrim isGameSpkPrim isGameOpkPrim koskBundleOkPrim lookupSpkSkPrim keyIndPartnerPrim choosePartnerDrKeyRandGdh chooseInitPartnerDrKeyRandGdh sampleIndexRange sampleIndexRange2 spkBundleFlatIdx initSessionSlotIdx respBundleKey extractDh1 extractDh2 extractDh3 extractDh4 extractKemSsNoOPK extractKemSsOPK parseRoSecrets FgKeyIndSimState fgRoQueryGdh fgRunInitiateGdh fgRunAcceptOPKGdh fgRunAcceptNoOPKGdh fgKeyIndStep runWithGdhStep extractCdhFromAdvRoLog lookupSpkSkFromPows initDh1CandWithPowsGdh respDh1CandGdh extractCdhFromSimState fgKeyIndGapDhRunAt fgKeyIndGapDhAdv fgKeyIndGapDhAdvAt)
abbrev FgKeyIndSimState.empty (S : Setup) (secb : Bool) : FgKeyIndSimState S :=
  _root_.SignalPqxdh.Security.FgGapDh.FgKeyIndSimState.empty S secb
@[simp]
theorem embedPrim_pure {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type} (a : α) :
    embedPrim (spec := spec) (pure a) = pure a := rfl

@[simp]
theorem embedPrim_query_bind {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (q : PrimBaseSpec.Domain)
    (k : PrimBaseSpec.Range q → OracleComp PrimBaseSpec α) :
    embedPrim (spec := spec) (liftM (OracleSpec.query q) >>= k) =
      (liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>=
        fun u => embedPrim (spec := spec) (k u)) := rfl

/-- Dual query bound on `OracleComp GdhSimSpec α`: at most `d` DDH queries and `p` primitive queries. -/
def GdhBounded {α : Type} (oa : OracleComp GdhSimSpec α) (d p : ℕ) : Prop :=
  IsQueryBoundP oa (fun q => q.isRight = true) d ∧
  IsQueryBoundP oa (fun q => isPrimQuery q = true) p

@[simp]
theorem runWithGdhStep_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSimSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithGdhStep step (pure a) st = pure (a, st) := rfl

@[simp]
theorem runWithGdhStep_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSimSpec (GSpec.Range q × St))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithGdhStep step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st =
      (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithGdhStep step (mx u) st) := rfl

@[simp]
theorem runWithGdhStep_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSimSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithGdhStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st =
      (step gq st >>= fun p => runWithGdhStep step (mx p.1) p.2) := rfl

/-! ## Pure semantics under `gapDhFullImpl` -/

def gapDhDdhImpl (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl gapDhOracleSpec ProbComp := fun (X, Y, Z) =>
  pure (isValidDhTriple X Y Z)

/-- Full `GdhSimSpec = PrimBaseSpec + gapDhOracleSpec` oracle implementation used by `gapDhExp`. -/
def gapDhFullImpl (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool) :
    QueryImpl GdhSimSpec ProbComp :=
  primBaseImpl P + gapDhDdhImpl isValidDhTriple

theorem simulateQ_embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (impl1 : QueryImpl PrimBaseSpec ProbComp) (impl2 : QueryImpl spec ProbComp)
    (mx : OracleComp PrimBaseSpec α) :
    simulateQ (impl1 + impl2) (embedPrim (spec := spec) mx) = simulateQ impl1 mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [embedPrim_query_bind, simulateQ_bind, simulateQ_bind, simulateQ_query, simulateQ_query]
    simp [ih]

theorem simulateQ_primBaseImpl_embedUnif {α : Type} (P : Primitives) (mx : ProbComp α) :
    simulateQ (primBaseImpl P) (embedUnif mx) = mx := by
  induction mx using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    change simulateQ (primBaseImpl P)
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl q)) >>= fun u => embedUnif (k u)) =
      (liftM (OracleSpec.query q) >>= k)
    rw [simulateQ_bind]
    change (simulateQ (primBaseImpl P) (liftM (OracleSpec.query (spec :=
      PrimBaseSpec) (Sum.inl q))) >>=
      fun u => simulateQ (primBaseImpl P) (embedUnif (k u))) =
      (liftM (OracleSpec.query q) >>= k)
    have hq : simulateQ (primBaseImpl P) (liftM (OracleSpec.query (spec :=
        PrimBaseSpec) (Sum.inl q))) =
        liftM (OracleSpec.query q) := by
      simp [primBaseImpl]
    rw [hq]
    congr 1
    ext u
    exact ih u

@[simp]
theorem simulateQ_gapDhFullImpl_unifGdh {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (mx : ProbComp α) :
    simulateQ (gapDhFullImpl P ddh) (unifGdh mx) = mx := by
  unfold gapDhFullImpl unifGdh
  rw [simulateQ_embedPrim, simulateQ_primBaseImpl_embedUnif]

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (op : PrimQuery) :
    simulateQ (gapDhFullImpl P ddh) (primGdhQ op) = primImpl P op := by
  unfold primGdhQ gapDhFullImpl
  simp [primBaseImpl]

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_x25519 (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk pk : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.x25519 sk pk)) =
      pure (P.x25519 sk pk) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_pow8 (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pk : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.pow8 pk)) =
      pure (P.pow8 pk) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_ddhGdhQ (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (X Y Z : Bytes) :
    simulateQ (gapDhFullImpl P ddh) (ddhGdhQ X Y Z) = pure (ddh X Y Z) := by
  unfold ddhGdhQ gapDhFullImpl gapDhDdhImpl
  simp

theorem simulateQ_gapDhFullImpl_findMGdh {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (p : α → OracleComp GdhSimSpec Bool) (pPure : α → Bool)
    (hp : ∀ a, simulateQ (gapDhFullImpl P ddh) (p a) = pure (pPure a)) :
    ∀ (L : List α), simulateQ (gapDhFullImpl P ddh) (findMGdh p L) = pure (L.find? pPure)
  | [] => by simp [findMGdh]
  | x :: xs => by
    simp only [findMGdh, simulateQ_bind, hp x, pure_bind, List.find?_cons]
    cases pPure x
    · exact simulateQ_gapDhFullImpl_findMGdh P ddh p pPure hp xs
    · rfl

/-- Pure deterministic `DDH-eq` corresponding to `ddhEqGdh` under `gapDhFullImpl P ddh`. -/
def ddhEqPure (ddh : Bytes → Bytes → Bytes → Bool) : FgPoS → FgPoS → Bool
  | .secret z1 _, .secret z2 _ =>
    z1 == z2
  | .pair _ _ w1 w2, .pair _ _ w3 w4 =>
    (w1 == w3 && w2 == w4) || (w1 == w4 && w2 == w3)
  | .pair pk1 pk2 _ _, .secret z isCanon =>
    if isCanon then ddh pk1 pk2 z else false
  | .secret z isCanon, .pair pk1 pk2 _ _ =>
    if isCanon then ddh pk1 pk2 z else false

@[simp]
theorem simulateQ_gapDhFullImpl_ddhEqGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (p1 p2 : FgPoS) :
    simulateQ (gapDhFullImpl P ddh) (ddhEqGdh p1 p2) = pure (ddhEqPure ddh p1 p2) := by
  cases p1 <;> cases p2 <;> simp only [ddhEqGdh, ddhEqPure]
  · rfl
  · split_ifs <;> simp
  · split_ifs <;> simp
  · rfl

def ddhEqOptPure (ddh : Bytes → Bytes → Bytes → Bool) : Option FgPoS → Option FgPoS → Bool
  | none, none => true
  | some p1, some p2 => ddhEqPure ddh p1 p2
  | _, _ => false

@[simp]
theorem simulateQ_gapDhFullImpl_ddhEqOptGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (o1 o2 : Option FgPoS) :
    simulateQ (gapDhFullImpl P ddh) (ddhEqOptGdh o1 o2) = pure (ddhEqOptPure ddh o1 o2) := by
  cases o1 <;> cases o2 <;> simp [ddhEqOptGdh, ddhEqOptPure]

def fgEntryMatchesPure (ddh : Bytes → Bytes → Bytes → Bool)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes) (e : FgPatchEntry) : Bool :=
  if ss != e.ss then
    false
  else
    ddhEqPure ddh pos1 e.pos1 &&
    ddhEqPure ddh pos2 e.pos2 &&
    ddhEqPure ddh pos3 e.pos3 &&
    ddhEqOptPure ddh pos4? e.pos4?

@[simp]
theorem simulateQ_gapDhFullImpl_fgEntryMatches (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes) (e : FgPatchEntry) :
    simulateQ (gapDhFullImpl P ddh) (fgEntryMatches pos1 pos2 pos3 pos4? ss e) =
      pure (fgEntryMatchesPure ddh pos1 pos2 pos3 pos4? ss e) := by
  unfold fgEntryMatches fgEntryMatchesPure
  split_ifs
  · rfl
  · simp

def fgPatchPure (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes)
    (L : List FgPatchEntry) : ProbComp (DRKey × List FgPatchEntry) := do
  match (L.take maxLen).find? (fgEntryMatchesPure ddh pos1 pos2 pos3 pos4? ss) with
  | some e => return (e.dk, L)
  | none =>
    let dk ← sampleDRKey96
    let newEntry : FgPatchEntry :=
      { pos1 := pos1, pos2 := pos2, pos3 := pos3, pos4? := pos4?, ss := ss, dk := dk }
    return (dk, newEntry :: L)

@[simp]
theorem simulateQ_gapDhFullImpl_fgPatch (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ)
    (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes) (L : List FgPatchEntry) :
    simulateQ (gapDhFullImpl P ddh) (fgPatch maxLen pos1 pos2 pos3 pos4? ss L) =
      fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss L := by
  unfold fgPatch fgPatchPure
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_findMGdh P ddh _ _
    (simulateQ_gapDhFullImpl_fgEntryMatches P ddh pos1 pos2 pos3 pos4? ss) (L.take maxLen),
    pure_bind]
  cases (L.take maxLen).find? (fgEntryMatchesPure ddh pos1 pos2 pos3 pos4? ss) <;> simp

def pureExtractCdhFromAdvRoLog (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) : Bytes :=
  let cands := (advRoLog.take maxLen).map (fun sec =>
    if useDh1 then extractDh1 sec else extractDh3 sec)
  match cands.find? (fun z => ddh U V z) with
  | some z => z
  | none   => List.replicate 32 0

@[simp]
theorem simulateQ_gapDhFullImpl_extractCdhFromAdvRoLog (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (advRoLog : List Bytes) :
    simulateQ (gapDhFullImpl P ddh) (extractCdhFromAdvRoLog useDh1 maxLen U V advRoLog) =
      pure (pureExtractCdhFromAdvRoLog ddh useDh1 maxLen U V advRoLog) := by
  unfold extractCdhFromAdvRoLog
  dsimp only [pureExtractCdhFromAdvRoLog]
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_findMGdh P ddh
    (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
    (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z), pure_bind]
  cases ((advRoLog.take maxLen).map
    (fun sec => if useDh1 then extractDh1 sec else extractDh3 sec)).find? (fun z =>
      ddh U V z) <;> simp

def lookupSpkSkTake (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (spkPk : Bytes) : Bytes :=
  let wSpk := P.pow8 spkPk
  match (spkBundles.take S.N_dh).find? (fun (_, b) => P.pow8 b.spkPk == wSpk) with
  | some (_, b) => b.spkSk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => sk
    | none => []

def spkPowsPure (P : Primitives) (L : List ((Nat × Nat) × SpkBundleEntry)) :
    List (Bytes × Bytes) :=
  L.map (fun x => (x.2.spkSk, P.pow8 x.2.spkPk))

theorem lookupSpkSkFromPows_map_eq (P : Primitives) (advKeyPows : List (Bytes × Bytes)) (wSpk :
    Bytes) :
    ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
      lookupSpkSkFromPows (spkPowsPure P L) advKeyPows wSpk =
        match L.find? (fun (_, b) => P.pow8 b.spkPk == wSpk) with
        | some (_, b) => b.spkSk
        | none =>
          match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
          | some (sk, _) => sk
          | none => []
  | [] => rfl
  | (_, b) :: tl => by
    unfold spkPowsPure lookupSpkSkFromPows
    simp only [List.map_cons, List.find?_cons]
    cases P.pow8 b.spkPk == wSpk
    · exact lookupSpkSkFromPows_map_eq P advKeyPows wSpk tl
    · rfl

/-- Candidate `dh1` secret reconstructed from an initiator session `s` using non-target SPK/KOSK
    scalars (`spkBundles` with `bIdx` erased and `advKeyPows`). -/
def initDh1Cand (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : KeyIndInitiatorEntry S) : Bytes :=
  let spkSk := lookupSpkSkTake S P spkBundles advKeyPows s.peerSpkPk
  P.x25519 spkSk s.hdr.ikAPk

/-- Candidate `dh1` secret reconstructed from a responder session `r` using non-target SPK
    scalars (`spkBundles` with `bIdx` erased). -/
def respDh1Cand (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : KeyIndRespEntry S) : Bytes :=
  let spkSk := match (spkBundles.take S.N_dh).find? (fun (idx, _) =>
    idx == respBundleKey r.sid) with
    | some (_, b) => b.spkSk
    | none => []
  P.x25519 spkSk r.hdr.ikAPk

theorem simulateQ_gapDhFullImpl_findMapMGdh {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (f : α → OracleComp GdhSimSpec Bytes) (fPure : α → Bytes)
    (U V : Bytes)
    (hf : ∀ a, simulateQ (gapDhFullImpl P ddh) (f a) = pure (fPure a)) :
    ∀ (L : List α),
      simulateQ (gapDhFullImpl P ddh) (findMapMGdh f U V L) =
        pure ((L.map fPure).find? (fun z => ddh U V z))
  | [] => by simp [findMapMGdh]
  | x :: xs => by
    simp only [findMapMGdh, simulateQ_bind, hf x, pure_bind,
      simulateQ_gapDhFullImpl_ddhGdhQ, List.map_cons, List.find?_cons]
    cases ddh U V (fPure x)
    · exact simulateQ_gapDhFullImpl_findMapMGdh P ddh f fPure U V hf xs
    · rfl

theorem simulateQ_gapDhFullImpl_spkPowsGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) :
    ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
      simulateQ (gapDhFullImpl P ddh) (spkPowsGdh L) =
        pure (spkPowsPure P L)
  | [] => by simp [spkPowsGdh, spkPowsPure]
  | (_, b) :: xs => by
    unfold spkPowsGdh spkPowsPure
    rw [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_pow8, pure_bind,
        simulateQ_bind, simulateQ_gapDhFullImpl_spkPowsGdh P ddh xs, pure_bind]
    rfl

theorem simulateQ_gapDhFullImpl_initDh1CandWithPowsGdh (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (s : KeyIndInitiatorEntry S) :
    simulateQ (gapDhFullImpl P ddh)
      (initDh1CandWithPowsGdh (spkPowsPure P (spkBundles.take S.N_dh)) advKeyPows s) =
      pure (initDh1Cand S P spkBundles advKeyPows s) := by
  unfold initDh1CandWithPowsGdh initDh1Cand lookupSpkSkTake
  simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_pow8,
    simulateQ_gapDhFullImpl_primGdhQ_x25519, pure_bind]
  rw [lookupSpkSkFromPows_map_eq P advKeyPows (P.pow8 s.peerSpkPk) (spkBundles.take S.N_dh)]

theorem simulateQ_gapDhFullImpl_respDh1CandGdh (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : KeyIndRespEntry S) :
    simulateQ (gapDhFullImpl P ddh) (respDh1CandGdh S spkBundles r) =
      pure (respDh1Cand S P spkBundles r) := by
  unfold respDh1CandGdh respDh1Cand
  simp; rfl

def pureExtractCdhFromSimState (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (st : FgKeyIndSimState S) : Bytes :=
  if useDh1 then
    match ((st.advRoLog.take maxLen).map extractDh1).find? (fun z => ddh U V z) with
    | some z => z
    | none =>
      match ((st.base.sessions.take S.N_dh).map
          (initDh1Cand S P st.base.spkBundles st.advKeyPows)).find? (fun z => ddh U V z) with
      | some z => z
      | none =>
        match ((st.base.respSessions.take S.N_sess_tot).map
            (respDh1Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) with
        | some z => z
        | none   => List.replicate 32 0
  else
    pureExtractCdhFromAdvRoLog ddh false maxLen U V st.advRoLog

@[simp]
theorem simulateQ_gapDhFullImpl_extractCdhFromSimState (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (extractCdhFromSimState S useDh1 maxLen U V st) =
      pure (pureExtractCdhFromSimState S P ddh useDh1 maxLen U V st) := by
  unfold extractCdhFromSimState pureExtractCdhFromSimState
  split_ifs with hDh1
  · rw [simulateQ_bind,
        simulateQ_gapDhFullImpl_findMGdh P ddh
          (fun z => ddhGdhQ U V z) (fun z => ddh U V z)
          (fun z => simulateQ_gapDhFullImpl_ddhGdhQ P ddh U V z)
          ((st.advRoLog.take maxLen).map extractDh1),
        pure_bind]
    cases ((st.advRoLog.take maxLen).map extractDh1).find? (fun z => ddh U V z) with
    | some z => rfl
    | none =>
      rw [simulateQ_bind,
          simulateQ_gapDhFullImpl_spkPowsGdh P ddh (st.base.spkBundles.take S.N_dh),
          pure_bind,
          simulateQ_bind,
          simulateQ_gapDhFullImpl_findMapMGdh P ddh
            (initDh1CandWithPowsGdh (S := S)
              (spkPowsPure P (st.base.spkBundles.take S.N_dh))
              st.advKeyPows)
            (initDh1Cand S P st.base.spkBundles st.advKeyPows) U V
            (fun s => simulateQ_gapDhFullImpl_initDh1CandWithPowsGdh S P ddh
              st.base.spkBundles st.advKeyPows s)
            (st.base.sessions.take S.N_dh),
          pure_bind]
      cases ((st.base.sessions.take S.N_dh).map
          (initDh1Cand S P st.base.spkBundles st.advKeyPows)).find? (fun z => ddh U V z) with
      | some z => rfl
      | none =>
        rw [simulateQ_bind,
            simulateQ_gapDhFullImpl_findMapMGdh P ddh
              (respDh1CandGdh S st.base.spkBundles)
              (respDh1Cand S P st.base.spkBundles) U V
              (fun r => simulateQ_gapDhFullImpl_respDh1CandGdh S P ddh st.base.spkBundles r)
              (st.base.respSessions.take S.N_sess_tot),
            pure_bind]
        cases ((st.base.respSessions.take S.N_sess_tot).map
            (respDh1Cand S P st.base.spkBundles)).find? (fun z => ddh U V z) <;> rfl
  · exact simulateQ_gapDhFullImpl_extractCdhFromAdvRoLog P ddh false maxLen U V st.advRoLog

theorem simulateQ_gapDhFullImpl_runWithGdhStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (step : (q : ιI) → St → OracleComp GdhSimSpec (GSpec.Range q × St))
    (stepImpl : QueryImpl GSpec (StateT St ProbComp))
    (h_step : ∀ gq st, simulateQ (gapDhFullImpl P ddh) (step gq st) = (stepImpl gq).run st)
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    simulateQ (gapDhFullImpl P ddh) (runWithGdhStep step mx st) =
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
        stepImpl) mx).run st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure x =>
    simp [runWithGdhStep_pure, simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    cases q with
    | inl n =>
      rw [runWithGdhStep_query_inl, simulateQ_bind]
      have hq : simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n)))) =
          liftM (OracleSpec.query (spec := unifSpec) n) := by
        simp [gapDhFullImpl, primBaseImpl]
      have h_rhs :
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
            stepImpl)
            (liftM (OracleSpec.query (Sum.inl n)) >>= mx)).run st =
          (liftM (OracleSpec.query (spec := unifSpec) n) >>= fun u =>
            (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
              stepImpl)
              (mx u)).run st) := by
        simp [QueryImpl.liftTarget, StateT.run_bind]
      rw [h_rhs]
      change (simulateQ (gapDhFullImpl P ddh)
          (liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n)))) >>=
        fun u => simulateQ (gapDhFullImpl P ddh) (runWithGdhStep step (mx u) st)) = _
      rw [hq]
      congr 1
      ext u
      exact ih u st
    | inr gq =>
      rw [runWithGdhStep_query_inr, simulateQ_bind, h_step gq st]
      change ((stepImpl gq).run st >>= fun p =>
        simulateQ (gapDhFullImpl P ddh) (runWithGdhStep step (mx p.1) p.2)) =
        ((stepImpl gq).run st >>= fun p =>
          (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
          stepImpl) (mx p.1)).run p.2)
      congr 1
      ext p
      exact ih p.1 p.2

/-- Pure `QueryImpl` induced by simulating `fgKeyIndStep` under `gapDhFullImpl P ddh`. -/
noncomputable def fgKeyIndSimImpl (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyIndSimState S) ProbComp) :=
  fun gq => StateT.mk (fun st =>
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStep useDh1 targetIdx targetSpkIdx S maxLen U V gq st))

theorem simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAt
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V) =
    (do
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return pureExtractCdhFromSimState S P ddh useDh1 b.q_total U V finalSt) := by
  unfold fgKeyIndGapDhRunAt
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh]
  congr 1
  ext secb
  rw [simulateQ_bind,
      simulateQ_gapDhFullImpl_runWithGdhStep P ddh
        (fgKeyIndStep useDh1 targetIdx targetSpkIdx S b.q_total U V)
        (fgKeyIndSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V)
        (fun _ _ => rfl)]
  congr 1
  ext res
  exact simulateQ_gapDhFullImpl_extractCdhFromSimState S P ddh useDh1 b.q_total U V res.2

end Proofs.SignalPqxdh.Security.FgGapDh
