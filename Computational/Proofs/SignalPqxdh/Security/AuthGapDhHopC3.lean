/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC1
public import Computational.Proofs.SignalPqxdh.Security.Collisions
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# `Auth` hop `G3 → G3.5`: lazy root-KDF coupling and target pre-sampling

Defines the `.g3` cutoff simulation `runAuthFgSim`, couples the lazy root-KDF cache (`FgRootCacheRel`),
and proves equivalence with the target-pre-sampled `.g3` oracle `pqxdhAuthFgPreImpl` for `DH1` and `DH3`.
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Cutoff simulation and lazy root-KDF cache relation -/

abbrev mkG3Hybrid {S : Setup} (base : AuthState S) : AuthHybridState S :=
  { base := base, initKemRecs := [], recvKemRecs := [], idealSessions := [] }
/-- `.g3` `Auth` oracle on `AuthFgCutoffState S` logging `.roQuery` inputs and responder handshakes. -/
def pqxdhAuthFgImpl (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .roQuery secrets => StateT.mk (fun hst => do
    let (resp, h') ←
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.roQuery secrets)).run (mkG3Hybrid hst.base)
    return (resp, { hst with base := h'.base, advRoLog := secrets :: hst.advRoLog }))
  | .recvOPK k j o msg => StateT.mk (fun hst => do
    let (resp, h') ←
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvOPK k j o msg)).run (mkG3Hybrid hst.base)
    let rRec : AuthRespRecord :=
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk }
    return (resp, { hst with base := h'.base, respRecs := rRec :: hst.respRecs }))
  | .recvNoOPK k j l msg => StateT.mk (fun hst => do
    let (resp, h') ←
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvNoOPK k j l msg)).run (mkG3Hybrid hst.base)
    let rRec : AuthRespRecord :=
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk }
    return (resp, { hst with base := h'.base, respRecs := rRec :: hst.respRecs }))
  | q => StateT.mk (fun hst => do
    let (resp, h') ← (pqxdhAuthHybridKoskImpl .g3 true false S P q).run (mkG3Hybrid hst.base)
    return (resp, { hst with base := h'.base }))
noncomputable def runAuthFgSim (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp (Bool × Bool × AuthFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (AuthFgCutoffState S) ProbComp) + pqxdhAuthFgImpl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)
/-- `DH3` per-index bad event at `(sIdx, bIdx)` without gating on `s.spkHonest`. -/
def badAuthFgDh3AtCore {S : Setup} (P : Primitives) (maxLen sIdx bIdx : ℕ)
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
theorem badAuthFgDh3At_imp_core {S : Setup} (P : Primitives) (maxLen sIdx bIdx : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (h : badAuthFgDh3At P maxLen sIdx bIdx st advRoLog respRecs = true) :
    badAuthFgDh3AtCore P maxLen sIdx bIdx st advRoLog respRecs = true := h
/-- Relates a symbolic `FgPoS` entry in `fgRootL` to a concrete DH byte string against right secret `vSk`. -/
def FgRootPosRep (P : Primitives) (vSk : Bytes) (pos : FgPoS) (dh : Bytes) : Prop :=
  pos = mkSecretPosPure P dh ∨
  ∃ pk1 pk2,
    pos = mkPairPosPure P pk1 pk2 ∧
    dh = P.x25519 vSk pk1 ∧
    onCurveKeyLocal P pk1 ∧
    P.pow8 pk2 = P.pow8 (P.x25519Base vSk) ∧
    ∀ z, P.isValidDhTriple pk1 pk2 z = P.isValidDhTriple pk1 (P.x25519Base vSk) z
theorem fgRootPosRep_mkSecret (P : Primitives) (vSk dh : Bytes) :
    FgRootPosRep P vSk (mkSecretPosPure P dh) dh :=
  Or.inl rfl
theorem fgRootPosRep_of_fgPosRightRep {P : Primitives} {vSk : Bytes} {pos : FgPoS} {dh : Bytes}
    (h : FgPosRightRep P vSk pos dh) : FgRootPosRep P vSk pos dh :=
  h.2
theorem ddhEqPure_of_fgRootPosRep (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {vSk : Bytes} (hv : vSk.length = 32) {p1 p2 : FgPoS} {dh1 dh2 : Bytes}
    (hp1 : FgRootPosRep P vSk p1 dh1) (hp2 : FgRootPosRep P vSk p2 dh2) :
    ddhEqPure P.isValidDhTriple p1 p2 = (dh1 == dh2) := by
  rcases hp1 with rfl | ⟨pk1, pk2, rfl, rfl, hpk1, hpow2, hddh1⟩ <;>
    rcases hp2 with rfl | ⟨pk3, pk4, rfl, rfl, hpk3, hpow4, hddh2⟩
  · rfl
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkSecretPosPure P dh1) (mkPairPosPure P pk3 pk4) =
        ddhEqPure P.isValidDhTriple (.secret dh1 (P.isCanonical dh1))
          (.pair pk3 (P.x25519Base vSk) (P.pow8 pk3) (P.pow8 pk4)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh2]
    rw [hEq]
    exact ddhEqPure_secret_pair_right_iff P hP.toWellFormedPrimitivesδ pk3 vSk
      (P.pow8 pk3) (P.pow8 pk4) dh1 hv (onCurveKeyLocal_length_eq_32 P hP hpk3) hpk3
  · apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq]
    have hEq : ddhEqPure P.isValidDhTriple (mkPairPosPure P pk1 pk2) (mkSecretPosPure P dh2) =
        ddhEqPure P.isValidDhTriple (.pair pk1 (P.x25519Base vSk) (P.pow8 pk1) (P.pow8 pk2))
          (.secret dh2 (P.isCanonical dh2)) := by
      simp only [ddhEqPure, mkSecretPosPure, mkPairPosPure, hddh1]
    rw [hEq]
    exact (ddhEqPure_pair_right_secret_iff P hP.toWellFormedPrimitivesδ pk1 vSk
      (P.pow8 pk1) (P.pow8 pk2) dh2 hv (onCurveKeyLocal_length_eq_32 P hP hpk1) hpk1).trans eq_comm
  · exact ddhEqPure_pair_pair_same_right_iff P hP vSk pk1 pk2 pk3 pk4 hv
      (onCurveKeyLocal_length_eq_32 P hP hpk1) (onCurveKeyLocal_length_eq_32 P hP hpk3)
      hpow2 hpow4
def FgRootEntryRel (P : Primitives) (vSk : Bytes)
    (e : FgRootEntry) (kv : (Bytes × Bytes) × (Bytes × Bytes)) : Prop :=
  e.rk = kv.1.1 ∧
  FgRootPosRep P vSk e.dhPos kv.1.2 ∧
  e.rk1 = kv.2.1 ∧
  e.ck1_0 = kv.2.2
/-- Coupling relation between the symbolic `fgRootL` cache and `rootRoCache` up to `maxLen`. -/
def FgRootCacheRel (P : Primitives) (vSk : Bytes) (maxLen : ℕ)
    (fgRootL : List FgRootEntry)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))) : Prop :=
  fgRootL.length ≤ maxLen ∧
  List.Forall₂ (FgRootEntryRel P vSk) fgRootL rootRoCache
theorem fgRootEntryMatchesPure_eq_beq_of_fgRootEntryRel (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) {vSk : Bytes} (hv : vSk.length = 32)
    {rk dh : Bytes} {dhPos : FgPoS} (hPos : FgRootPosRep P vSk dhPos dh)
    {e : FgRootEntry} {kv : (Bytes × Bytes) × (Bytes × Bytes)}
    (hE : FgRootEntryRel P vSk e kv) :
    fgRootEntryMatchesPure P.isValidDhTriple rk dhPos e = (kv.1 == (rk, dh)) := by
  rcases kv with ⟨⟨rk', dh'⟩, rk1', ck0'⟩
  rcases hE with ⟨hrk, hdh, _, _⟩
  dsimp only at hrk hdh ⊢
  unfold fgRootEntryMatchesPure
  rw [hrk, ddhEqPure_of_fgRootPosRep P hP hv hPos hdh]
  by_cases hEq : rk = rk'
  · subst hEq
    have hBne : (rk != rk) = false := bne_self_eq_false rk
    rw [hBne]
    by_cases hDh : dh = dh'
    · subst hDh
      simp
    · have h1 : (dh == dh') = false := beq_eq_false_iff_ne.mpr hDh
      have h2 : ((rk, dh') == (rk, dh)) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hDh (Prod.ext_iff.mp h).2.symm)
      rw [h1, h2]
      rfl
  · have hNe : (rk != rk') = true := bne_iff_ne.mpr hEq
    have hNe' : ((rk', dh') == (rk, dh)) = false :=
      beq_eq_false_iff_ne.mpr (fun h => hEq (Prod.ext_iff.mp h).1.symm)
    rw [hNe, hNe']
    rfl
theorem fgRootPatchPure_eq_or_sample (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {vSk : Bytes} (hv : vSk.length = 32)
    {maxLen : ℕ} {fgRootL : List FgRootEntry}
    {rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))}
    {rk dh : Bytes} {dhPos : FgPoS}
    (hCache : FgRootCacheRel P vSk maxLen fgRootL rootRoCache)
    (hPos : FgRootPosRep P vSk dhPos dh) :
    (∃ rk1 ck1_0,
      evalRootKdfOrRo true P rootRoCache rk dh = pure ((rk1, ck1_0), rootRoCache) ∧
      fgRootPatchPure P.isValidDhTriple maxLen rk dhPos fgRootL = pure ((rk1, ck1_0), fgRootL)) ∨
    (evalRootKdfOrRo true P rootRoCache rk dh =
      (do
        let rk1 ← sampleBytes32; let ck1_0 ← sampleBytes32
        pure ((rk1, ck1_0), ((rk, dh), (rk1, ck1_0)) :: rootRoCache)) ∧
     fgRootPatchPure P.isValidDhTriple maxLen rk dhPos fgRootL =
      (do
        let rk1 ← sampleBytes32; let ck1_0 ← sampleBytes32
        pure ((rk1, ck1_0), { rk := rk, dhPos := dhPos, rk1 := rk1, ck1_0 := ck1_0 } :: fgRootL)) ∧
     ∀ rk1 ck1_0, fgRootL.length < maxLen →
       FgRootCacheRel P vSk maxLen
         ({ rk := rk, dhPos := dhPos, rk1 := rk1, ck1_0 := ck1_0 } :: fgRootL)
         (((rk, dh), (rk1, ck1_0)) :: rootRoCache)) := by
  rcases hCache with ⟨hLen, hForall⟩
  have hTake : fgRootL.take maxLen = fgRootL := List.take_of_length_le hLen
  have hMapEq :
      (fgRootL.find? (fgRootEntryMatchesPure P.isValidDhTriple rk dhPos)).map
        (fun e => (e.rk1, e.ck1_0)) =
      (rootRoCache.find? (fun (k, _) => k == (rk, dh))).map Prod.snd := by
    exact forall₂_find?_map_eq hForall (fun e kv hE =>
      ⟨fgRootEntryMatchesPure_eq_beq_of_fgRootEntryRel P hP hv hPos hE,
       by rcases hE with ⟨_, _, h1, h2⟩; exact Prod.ext h1 h2⟩)
  unfold evalRootKdfOrRo fgRootPatchPure
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTake]
  cases hF1 : fgRootL.find? (fgRootEntryMatchesPure P.isValidDhTriple rk dhPos) <;>
    cases hF2 : rootRoCache.find? (fun (k, _) => k == (rk, dh))
  · right
    refine ⟨rfl, rfl, fun rk1 ck1_0 hLt => ⟨by simp; omega, ?_⟩⟩
    exact List.Forall₂.cons ⟨rfl, hPos, rfl, rfl⟩ hForall
  · rw [hF1, hF2] at hMapEq; simp at hMapEq
  · rw [hF1, hF2] at hMapEq; simp at hMapEq
  · rename_i e kv; rw [hF1, hF2] at hMapEq
    simp only [Option.map_some, Option.some.injEq] at hMapEq
    left; refine ⟨e.rk1, e.ck1_0, ?_, rfl⟩; rw [hMapEq]
noncomputable def fgRoQueryAuthPure {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (secrets : Bytes)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  let advRoLog' := secrets :: st.advRoLog
  match parseRoSecrets secrets with
  | some (dh1, dh2, dh3, dh4?, ss) =>
    let pos1 := mkSecretPosPure P dh1; let pos2 := mkSecretPosPure P dh2
    let pos3 := mkSecretPosPure P dh3
    let pos4? := dh4?.map (mkSecretPosPure P)
    let (dk, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
    return (.drKeyResp dk, { st with fgL := fgL', advRoLog := advRoLog' })
  | none =>
    match st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some (_, dk) =>
      return (.drKeyResp dk, { st with advRoLog := advRoLog' })
    | none =>
      let dk ← sampleDRKey96; return (.drKeyResp dk,
        { st with rawRoCache := (secrets, dk) :: st.rawRoCache, advRoLog := advRoLog' })
@[simp]
theorem simulateQ_gapDhFullImpl_fgRoQueryAuthGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (secrets : Bytes)
    (st : FgAuthSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRoQueryAuthGdh maxLen secrets st) =
      fgRoQueryAuthPure P ddh maxLen secrets st := by
  unfold fgRoQueryAuthGdh fgRoQueryAuthPure; cases parseRoSecrets secrets with
  | none =>
    cases st.rawRoCache.find? (fun (s, _) => s == secrets) <;> simp
  | some tup => rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩; cases dh4? <;> simp
theorem fgRoQueryAuthPure_eq_or_sample {S : Setup} {P : Primitives} (R : FgSlotReps P)
    {maxLen : ℕ} {secrets : Bytes} {hst : AuthFgCutoffState S} {st : FgAuthSimState S}
    (hCache : FgCacheRel R maxLen st.fgL st.rawRoCache hst.base.roCache) :
    (∃ dk,
      evalHkdfOrRo true P hst.base.roCache secrets = pure (dk, hst.base.roCache) ∧
      fgRoQueryAuthPure P P.isValidDhTriple maxLen secrets st =
        pure (.drKeyResp dk, { st with advRoLog := secrets :: st.advRoLog })) ∨
    (∃ (newRaw : DRKey → List (Bytes × DRKey)) (newFgL : DRKey → List FgPatchEntry),
      evalHkdfOrRo true P hst.base.roCache secrets =
        (sampleDRKey96 >>= fun dk => pure (dk, (secrets, dk) :: hst.base.roCache)) ∧
      fgRoQueryAuthPure P P.isValidDhTriple maxLen secrets st =
        (sampleDRKey96 >>= fun dk =>
          pure (.drKeyResp dk, { st with
            rawRoCache := newRaw dk
            fgL        := newFgL dk
            advRoLog   := secrets :: st.advRoLog })) ∧
      (∀ dk, st.fgL.length < maxLen →
        (newFgL dk).length ≤ st.fgL.length + 1 ∧
        FgCacheRel R maxLen (newFgL dk) (newRaw dk) ((secrets, dk) :: hst.base.roCache))) := by
  unfold fgRoQueryAuthPure
  cases hParse : parseRoSecrets secrets with
  | none =>
    rcases hCache with ⟨hLen, hRaw, hForall⟩
    have hFiltFind :
        st.rawRoCache.find? (fun (s, _) => s == secrets) =
        hst.base.roCache.find? (fun (s, _) => s == secrets) := by
      rw [hRaw]; apply find?_filter_eq_find?_of_imp; rintro ⟨s, dk⟩ hs
      simp only [beq_iff_eq] at hs; subst hs; simp [hParse]
    unfold evalHkdfOrRo
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFiltFind]
    cases hst.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p => rcases p with ⟨_, dk⟩; left; exact ⟨dk, rfl, by simp⟩
    | none =>
      right; refine ⟨fun dk => (secrets, dk) :: st.rawRoCache, fun _ => st.fgL, rfl, by simp, ?_⟩
      intro dk _; refine ⟨by dsimp; omega, hLen, ?_, ?_⟩
      · rw [hRaw, List.filter_cons_of_pos (by simp [hParse])]
      · rw [List.filter_cons_of_neg (by simp [hParse])]
        exact hForall
  | some tup =>
    rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
    rcases buildSecrets_of_parseRoSecrets hParse with ⟨hSecEq, h1, h2, h3, h4, hss⟩
    have hT : FgTupleRel R (mkSecretPosPure P dh1) (mkSecretPosPure P dh2)
        (mkSecretPosPure P dh3) (dh4?.map (mkSecretPosPure P)) dh1 dh2 dh3 dh4? ss :=
      ⟨R.sec1 dh1 h1, R.sec2 dh2 h2, R.sec3 dh3 h3, R.sec4 dh4? h4, hss⟩
    have hPatch := fgPatchPure_eq_or_sample R hCache hT
    dsimp only at hPatch; rw [← hSecEq] at hPatch
    rcases hPatch with ⟨dk, hEval, hFg⟩ | ⟨hEval, hFg, hCache'⟩
    · left; refine ⟨dk, hEval, ?_⟩; dsimp only; rw [hFg, pure_bind]
    · right
      refine ⟨fun _ => st.rawRoCache,
        fun dk => { pos1 := mkSecretPosPure P dh1, pos2 := mkSecretPosPure P dh2,
                    pos3 := mkSecretPosPure P dh3, pos4? := dh4?.map (mkSecretPosPure P),
                    ss := ss, dk := dk } :: st.fgL,
        hEval, ?_, ?_⟩
      · dsimp only; rw [hFg, bind_assoc]; simp only [pure_bind]
      · intro dk hLt; exact ⟨by simp, hCache' dk hLt⟩
noncomputable def fgRoRootQueryAuthPure {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (rk dh : Bytes)
    (st : FgAuthSimState S) : ProbComp (AuthResponse × FgAuthSimState S) := do
  let pos := mkSecretPosPure P dh
  let ((rk1, ck1_0), fgRootL') ← fgRootPatchPure ddh maxLen rk pos st.fgRootL
  return (.rootKdfResp rk1 ck1_0, { st with fgRootL := fgRootL' })
@[simp]
theorem simulateQ_gapDhFullImpl_fgRoRootQueryAuthGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (rk dh : Bytes)
    (st : FgAuthSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRoRootQueryAuthGdh maxLen rk dh st) =
      fgRoRootQueryAuthPure P ddh maxLen rk dh st := by
  unfold fgRoRootQueryAuthGdh fgRoRootQueryAuthPure; simp
theorem fgRoRootQueryAuthPure_eq_or_sample {S : Setup} {P : Primitives}
    (hP : CryptoWellFormedPrimitivesδ P) {vSk : Bytes} (hv : vSk.length = 32)
    {maxLen : ℕ} {rk dh : Bytes} {hst : AuthFgCutoffState S} {st : FgAuthSimState S}
    (hCache : FgRootCacheRel P vSk maxLen st.fgRootL hst.base.rootRoCache) :
    (∃ rk1 ck1_0,
      evalRootKdfOrRo true P hst.base.rootRoCache rk dh =
        pure ((rk1, ck1_0), hst.base.rootRoCache) ∧
      fgRoRootQueryAuthPure P P.isValidDhTriple maxLen rk dh st =
        pure (.rootKdfResp rk1 ck1_0, st)) ∨
    (evalRootKdfOrRo true P hst.base.rootRoCache rk dh =
      (do
        let rk1 ← sampleBytes32; let ck1_0 ← sampleBytes32
        pure ((rk1, ck1_0), ((rk, dh), (rk1, ck1_0)) :: hst.base.rootRoCache)) ∧
     fgRoRootQueryAuthPure P P.isValidDhTriple maxLen rk dh st =
      (do
        let rk1 ← sampleBytes32; let ck1_0 ← sampleBytes32
        pure (.rootKdfResp rk1 ck1_0,
          { st with fgRootL :=
              { rk := rk, dhPos := mkSecretPosPure P dh, rk1 := rk1, ck1_0 := ck1_0 } ::
                st.fgRootL })) ∧
     ∀ rk1 ck1_0, st.fgRootL.length < maxLen →
       FgRootCacheRel P vSk maxLen
         ({ rk := rk, dhPos := mkSecretPosPure P dh, rk1 := rk1, ck1_0 := ck1_0 } :: st.fgRootL)
         (((rk, dh), (rk1, ck1_0)) :: hst.base.rootRoCache)) := by
  unfold fgRoRootQueryAuthPure
  have hPos := fgRootPosRep_mkSecret P vSk dh
  rcases fgRootPatchPure_eq_or_sample P hP hv hCache hPos with
    ⟨rk1, ck1_0, hEval, hFg⟩ | ⟨hEval, hFg, hStep⟩
  · left; refine ⟨rk1, ck1_0, hEval, ?_⟩; dsimp only; rw [hFg, pure_bind]
  · right; refine ⟨hEval, ?_, hStep⟩; dsimp only; rw [hFg, bind_assoc]
    simp only [bind_assoc, pure_bind]

/-! ## State erasure and `FgAuthBaseRel` -/
def ValidAuthEcFg (S : Setup) (P : Primitives) (st : AuthState S) : Prop :=
  ValidPrincipals S st.principals ∧ ValidSpkBundles S st.spkBundles ∧
  ValidOpkEntries S st.opkEntries ∧
  ValidSessionIds S ((sessPksAuth S P st).map Prod.fst) ∧
  st.usedSendSessions = (sessPksAuth S P st).map Prod.fst
theorem validAuthEcFg_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidAuthEcFg S P (AuthState.empty S secb) := by
  have hNil := validEcLists_nil S
  exact ⟨hNil.1, hNil.2.1, hNil.2.2.1, hNil.2.2.2, rfl⟩
theorem validAuthEc_lengths_le_fg (S : Setup) (P : Primitives) (st : AuthState S)
    (hV : ValidAuthEcFg S P st) :
    st.principals.length ≤ S.N_dh ∧ st.spkBundles.length ≤ S.N_dh ∧
    st.opkEntries.length ≤ S.N_dh ∧ st.sessions.length ≤ S.N_dh := by
  have hTag := validTaggedPks_ecTaggedFromLists S P
    st.principals st.spkBundles st.opkEntries (sessPksAuth S P st)
    ⟨hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1⟩
  have hLen := validTaggedPks_length_le_fg hTag
  unfold ecTaggedFromLists sessPksAuth at hLen
  simp only [List.length_append, List.length_map] at hLen
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem validAuthEcFg_of_fields_eq {S : Setup} {P : Primitives} {st1 st2 : AuthState S}
    (hV : ValidAuthEcFg S P st1)
    (hP : st2.principals = st1.principals := by rfl)
    (hS : st2.spkBundles = st1.spkBundles := by rfl)
    (hO : st2.opkEntries = st1.opkEntries := by rfl)
    (hSess : st2.sessions = st1.sessions := by rfl)
    (hUsed : st2.usedSendSessions = st1.usedSendSessions := by rfl) :
    ValidAuthEcFg S P st2 := by
  rcases hV with ⟨hVP, hVS, hVO, hVSess, hUsed1⟩
  refine ⟨by rw [hP]; exact hVP, by rw [hS]; exact hVS, by rw [hO]; exact hVO, ?_, ?_⟩
  · unfold sessPksAuth at hVSess ⊢; rw [hSess]; exact hVSess
  · unfold sessPksAuth at hUsed1 ⊢; rw [hUsed, hSess]; exact hUsed1
def erasePrincipalsOptFg (useDh1 : Bool) (targetIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) : List (Nat × PrincipalEntry) :=
  if useDh1 then erasePrincipalsFg targetIdx principals else principals
def eraseAuthSessionEntryOptFg {S : Setup} (useDh1 : Bool) (targetIdx : ℕ)
    (s : AuthInitiatorEntry S) : AuthInitiatorEntry S :=
  { s with
    opkHonest := false
    ekASk     := if !useDh1 && (initSessionSlotIdx s.sid == targetIdx) then [] else s.ekASk }
def eraseAuthSessionsOptFg {S : Setup} (useDh1 : Bool) (targetIdx : ℕ)
    (sessions : List (AuthInitiatorEntry S)) : List (AuthInitiatorEntry S) :=
  sessions.map (eraseAuthSessionEntryOptFg useDh1 targetIdx)
/-- State-erasure relation between simulator state `stBase` and cutoff game state `hstBase`. -/
structure FgAuthBaseRel {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (stBase hstBase : AuthState S) : Prop where
  secb_eq             : stBase.secb = hstBase.secb
  principals_eq       : stBase.principals = erasePrincipalsOptFg useDh1 targetIdx hstBase.principals
  spkBundles_eq       : stBase.spkBundles = eraseSpkBundlesFg S targetSpkIdx hstBase.spkBundles
  opkEntries_eq       : stBase.opkEntries = hstBase.opkEntries
  sessions_eq         : stBase.sessions = eraseAuthSessionsOptFg useDh1 targetIdx hstBase.sessions
  usedSendSessions_eq : stBase.usedSendSessions = hstBase.usedSendSessions
  usedRecvOPK_eq      : stBase.usedRecvOPK = hstBase.usedRecvOPK
  usedRecvNoOPK_eq    : stBase.usedRecvNoOPK = hstBase.usedRecvNoOPK
  usedKyberTriples_eq : stBase.seenKyberBaseKeys = hstBase.seenKyberBaseKeys
theorem fgAuthBaseRel_empty (S : Setup) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (secb : Bool) :
    FgAuthBaseRel useDh1 targetIdx targetSpkIdx
      (AuthState.empty S secb) (AuthState.empty S secb) where
  secb_eq := rfl; principals_eq := by cases useDh1 <;> rfl
  spkBundles_eq := rfl; opkEntries_eq := rfl; sessions_eq := rfl
  usedSendSessions_eq := rfl; usedRecvOPK_eq := rfl
  usedRecvNoOPK_eq := rfl; usedKyberTriples_eq := rfl
@[simp]
theorem spkHon_eraseSpkBundlesFg (S : Setup) (bIdx k : ℕ) (spkB : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).any (fun ((u, _), b) => u == k && b.spkPk == spkB) =
      spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == spkB) := by
  unfold eraseSpkBundlesFg
  rw [List.any_map]
  congr 1; funext ⟨⟨u, j⟩, b⟩
  dsimp only [Function.comp_apply, eraseSpkBundleEntryFg]
  split_ifs <;> rfl
@[simp]
theorem pqspkHon_eraseSpkBundlesFg (S : Setup) (bIdx k : ℕ) (pqspkB : Bytes)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).any (fun ((u, _), b) => u == k && b.pqspkPk == pqspkB) =
      spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == pqspkB) := by
  unfold eraseSpkBundlesFg
  rw [List.any_map]
  congr 1; funext ⟨⟨u, j⟩, b⟩
  dsimp only [Function.comp_apply, eraseSpkBundleEntryFg]
  split_ifs <;> rfl
@[simp]
theorem lookupSenderIkPk_erasePrincipalsFg (uIdx u0 : ℕ)
    (principals : List (Nat × PrincipalEntry)) :
    lookupSenderIkPk (erasePrincipalsFg uIdx principals) u0 =
      lookupSenderIkPk principals u0 := by
  unfold lookupSenderIkPk; rw [find?_idx_erasePrincipalsFg]
  cases principals.find? (fun (idx, _) => idx == u0) with
  | none => rfl
  | some p =>
    rcases p with ⟨idx, e⟩
    dsimp only [Option.map, erasePrincipalEntryFg]
    split_ifs <;> rfl

/-! ## Target pre-sampling for `.g3` -/
def hasFiredAuthSpk (S : Setup) (bIdx : ℕ) (hst : AuthFgCutoffState S) : Prop :=
  ∃ (u₀ : Fin S.N_id) (j₀ : Fin S.N_recv),
    spkBundleFlatIdx S u₀ j₀ = bIdx ∧
    hst.base.spkBundles.any (fun (k, _) => k == (u₀.val, j₀.val)) = true
theorem spkBundles_any_of_hasFiredAuthSpk (S : Setup) (bIdx : ℕ) (hst : AuthFgCutoffState S)
    (hFired : hasFiredAuthSpk S bIdx hst) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hb : (spkBundleFlatIdx S u j == bIdx) = true) :
    hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = true := by
  rcases hFired with ⟨u₀, j₀, hidx₀, hany₀⟩
  have heq : spkBundleFlatIdx S u j = spkBundleFlatIdx S u₀ j₀ :=
    (beq_iff_eq.mp hb).trans hidx₀.symm
  rcases FgGapDh.spkBundleFlatIdx_inj S u u₀ j j₀ heq with ⟨rfl, rfl⟩
  exact hany₀
def hasFiredAuthPrin (S : Setup) (uIdx : ℕ) (hst : AuthFgCutoffState S) : Prop :=
  hst.base.principals.any (fun (idx, _) => idx == uIdx) = true
def hasFiredAuthSess (S : Setup) (sIdx : ℕ) (hst : AuthFgCutoffState S) : Prop :=
  hst.base.usedSendSessions.any (fun sid => initSessionSlotIdx sid == sIdx) = true
theorem usedSendSessions_contains_of_hasFiredAuthSess {S : Setup} (sIdx : ℕ)
    (hst : AuthFgCutoffState S) (hFired : hasFiredAuthSess S sIdx hst) (sid : SessionId S)
    (hs : (initSessionSlotIdx sid == sIdx) = true)
    (hlt : initSessionSlotIdx sid < S.N_send_tot) :
    hst.base.usedSendSessions.contains sid = true := by
  unfold hasFiredAuthSess at hFired; rw [List.contains_iff_exists_mem_beq]
  rw [List.any_eq_true] at hFired; rcases hFired with ⟨sid0, hmem, hidx⟩
  have heq : sid0 = sid :=
    initSessionSlotIdx_inj_of_lt ((beq_iff_eq.mp hidx).trans (beq_iff_eq.mp hs).symm) hlt
  exact ⟨sid0, hmem, beq_iff_eq.mpr heq.symm⟩
def liftAuthFgBase {S : Setup} (m : StateT (AuthState S) ProbComp AuthResponse) :
    StateT (AuthFgCutoffState S) ProbComp AuthResponse :=
  StateT.mk (fun hst => do
    let (r, b') ← m.run hst.base
    return (r, { hst with base := b' }))
def liftAuthFgHybrid {S : Setup} (m : StateT (AuthHybridState S) ProbComp AuthResponse) :
    StateT (AuthFgCutoffState S) ProbComp AuthResponse :=
  StateT.mk (fun hst => do
    let (resp, h') ← m.run (mkG3Hybrid hst.base)
    return (resp, { hst with base := h'.base }))
@[simp]
theorem liftAuthFgHybrid_liftAuthBase_eq {S : Setup}
    (m : StateT (AuthState S) ProbComp AuthResponse) :
    liftAuthFgHybrid (do let hst ← get; let _ := hst.base; liftAuthBase m) =
      liftAuthFgBase m := by
  apply StateT.ext; intro hst
  unfold liftAuthFgHybrid liftAuthFgBase liftAuthBase mkG3Hybrid
  simp [StateT.run_bind, StateT.run_get, StateT.run_monadLift,
    monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind, map_eq_bind_pure_comp]
noncomputable def fgPreAuthInitPrin (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let secIKA0 ← liftM (match optUsk with
    | some uSk => if useDh1 && (u.val == targetIdx) then pure uSk else sampleScalar32
    | none => sampleScalar32)
  let ikAPk := P.x25519Base secIKA0
  let secIKAsign ← liftM sampleScalar32; let ikSignPk := P.sigPkGen secIKAsign
  let entry : PrincipalEntry :=
    { secIKA0 := secIKA0, ikAPk := ikAPk, secIKAsign := secIKAsign,
      ikSignPk := ikSignPk, corrupted := false }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp ikAPk ikSignPk
noncomputable def fgPreAuthGenSPK (targetSpkIdx : ℕ) (optVsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (AuthState S) ProbComp AuthResponse := do
  let st ← get
  if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val) | return .noneResp
  let spkSk ← liftM (match optVsk with
    | some vSk => if spkBundleFlatIdx S u j == targetSpkIdx then pure vSk else sampleScalar32
    | none => sampleScalar32)
  let spkPk := P.x25519Base spkSk
  let rSpk ← liftM sampleRandom64
  let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
  let rPq ← liftM sampleRandom64
  let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry :=
    { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
  set { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
  let bundleOut : PreKeyBundleInput :=
    { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
  return .bundleResp bundleOut
noncomputable def fgPreAuthSendHybrid (stage : AuthHybridStage) (useRo : Bool)
    (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) :
    StateT (AuthHybridState S) ProbComp AuthResponse := do
  let hst ← get; let st := hst.base
  if m0.length != m1.length then return .noneResp
  if st.usedSendSessions.contains sid then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  if !isFreshPeer && m0 != m1 then return .noneResp
  let msgPlain :=
    if isFreshPeer then
      if stage.idealFreshAead then m0 else (if st.secb then m1 else m0)
    else
      m0
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM (match optUsk with
    | some uSk =>
      if !useDh1 && (initSessionSlotIdx sid == targetIdx) then pure uSk else sampleScalar32
    | none => sampleScalar32)
  let kemCoins ← liftM sampleCoins32; let ephASk ← liftM sampleScalar32
  let spqrCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
  let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB; let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ←
    if isIdealSend && stage.idealDrKey then do
      let dk ← liftM sampleDRKey96; pure (dk, st.roCache)
    else
      liftM (evalHkdfOrRo useRo P st.roCache secrets)
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ←
    if isIdealSend && stage.idealRk then do
      let r ← liftM sampleBytes32; let c ← liftM sampleBytes32
      pure ((r, c), st.rootRoCache)
    else
      liftM (evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet)
  let (mkSeed, ck1_1) ←
    if isIdealSend && stage.idealCk then do
      let ms ← liftM sampleBytes32; let cn ← liftM sampleBytes32; pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return .noneResp
  let deriveMessageKeys ←
    if isIdealSend && stage.idealMsgKeys then
      liftM sampleMessageKeys80
    else
      pure (P.deriveMsgKeys mkSeed spqrSalt?)
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr :=
    { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
      opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let wireMsg : PreKeyMsg :=
    { hdr := hdr, ephAPk := ephAPk, pqRatchetMsg := pqRatchetMsg, aeadCt := aeadCt }
  let sessEntry : AuthInitiatorEntry S :=
    { sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
      peerOpkPk? := bundle.opkB?.map Prod.snd,
      peerPqspkPk := bundle.pqspkB, spkHonest := spkHon, opkHonest := opkHon,
      pqspkHonest := pqspkHon,
      ekASk := ekASk, ephASk := ephASk, fresh := isFreshPeer,
      challenged := isFreshPeer && (m0 != m1) }
  let (sentOPK', sentNoOPK') :=
    match peerPrincipal?, bundle.opkB? with
    | some (_, pEntry), some (_, opkPk) =>
      (({ a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, ob := opkPk,
          a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain,
          matched := false } : SentOPKEvent) :: st.sentOPKEvents,
       st.sentNoOPKEvents)
    | some (_, pEntry), none =>
      (st.sentOPKEvents,
       ({ a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB,
          a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain,
          matched := false } : SentNoOPKEvent) :: st.sentNoOPKEvents)
    | none, _ => (st.sentOPKEvents, st.sentNoOPKEvents)
  let initRec : _root_.SignalPqxdh.Security.InitKemRecord S :=
    { sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss }
  let idealSessions' :=
    if isIdealSend then
      ({ sid := sid, ikAPk := uEntry.ikAPk, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
         peerOpkPk? := bundle.opkB?.map Prod.snd, ekAPk := ekAPk, peerPqspkPk := bundle.pqspkB,
         kemCt := kemCt, ephAPk := ephAPk, spqrSalt? := spqrSalt?, pqRatchetMsg := pqRatchetMsg,
         ad := ad, aeadCt := aeadCt, msgPlain := msgPlain, drKey := drKey, rk1 := rk1,
         ck1_0 := ck1_0, mkSeed := mkSeed, ck1_1 := ck1_1,
         deriveMessageKeys := deriveMessageKeys } : IdealAuthSession S) :: hst.idealSessions
    else hst.idealSessions
  set { hst with
    base := { st with
      sessions := sessEntry :: st.sessions, usedSendSessions := sid :: st.usedSendSessions,
      sentOPKEvents := sentOPK', sentNoOPKEvents := sentNoOPK',
      roCache := roCache', rootRoCache := rootRoCache' },
    initKemRecs := initRec :: hst.initKemRecs, idealSessions := idealSessions' }
  if peerPrincipal?.isSome then
    return .sendFreshResp wireMsg
  else
    return .sendUnfreshResp drKey rk1 ck1_1 wireMsg
noncomputable def pqxdhAuthFgPreImpl (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (authSpec S) (StateT (AuthFgCutoffState S) ProbComp)
  | .initPrin u => liftAuthFgHybrid (do
      let hst ← get; let _ := hst.base
      liftAuthBase (fgPreAuthInitPrin useDh1 targetIdx optUsk S P u))
  | .genSPK u j => liftAuthFgHybrid (do
      let hst ← get; let _ := hst.base
      liftAuthBase (fgPreAuthGenSPK targetSpkIdx optVsk S P u j))
  | .sendOPK u i bundle m0 m1 =>
    liftAuthFgHybrid (do
      let hst ← get; let _ := hst.base
      if bundle.opkB?.isNone then return .noneResp
      fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P (.sendOPK u i) u bundle m0 m1)
  | .sendNoOPK u i bundle m0 m1 =>
    liftAuthFgHybrid (do
      let hst ← get; let _ := hst.base
      if bundle.opkB?.isSome then return .noneResp
      fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P (.sendNoOPK u i) u bundle m0 m1)
  | q => pqxdhAuthFgImpl S P q
theorem pqxdhAuthFgPreImpl_none_none_eq {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (P : Primitives) :
    pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx none none S P =
      pqxdhAuthFgImpl S P := by
  funext q; cases q <;> rfl
def sampleAuthSendCoins : ProbComp (Bytes × Bytes × Bytes) := do
  let kemCoins ← sampleCoins32; let ephASk ← sampleScalar32
  let spqrCoins ← sampleCoins32
  return (kemCoins, ephASk, spqrCoins)
noncomputable def fgPreAuthSendAfterCoins {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthFgCutoffState S) (ekASk : Bytes) (coins : Bytes × Bytes × Bytes) :
    ProbComp (AuthResponse × AuthFgCutoffState S) := do
  let (kemCoins, ephASk, spqrCoins) := coins
  let st := hst.base
  let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, hst)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.noneResp, hst)
  let ekAPk := P.x25519Base ekASk
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB; let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
  let ephAPk := P.x25519Base ephASk
  let dhRatchet := P.x25519 ephASk bundle.spkB
  let ((rk1, ck1_0), rootRoCache') ←
    evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) := (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  let some (_pqrStA, spqrSalt?, pqRatchetMsg) := P.spqrInitSend drKey.pqrKey spqrCoins
    | return (.noneResp, hst)
  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let hdr : HandshakeHdr :=
    { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
      opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let wireMsg : PreKeyMsg :=
    { hdr := hdr, ephAPk := ephAPk, pqRatchetMsg := pqRatchetMsg, aeadCt := aeadCt }
  let sessEntry : AuthInitiatorEntry S :=
    { sid := sid, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
      peerOpkPk? := bundle.opkB?.map Prod.snd,
      peerPqspkPk := bundle.pqspkB, spkHonest := spkHon, opkHonest := opkHon,
      pqspkHonest := pqspkHon,
      ekASk := ekASk, ephASk := ephASk, fresh := isFreshPeer,
      challenged := isFreshPeer && (m0 != m1) }
  let (sentOPK', sentNoOPK') :=
    match peerPrincipal?, bundle.opkB? with
    | some (_, pEntry), some (_, opkPk) =>
      (({ a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB, ob := opkPk,
          a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain,
          matched := false } : SentOPKEvent) :: st.sentOPKEvents,
       st.sentNoOPKEvents)
    | some (_, pEntry), none =>
      (st.sentOPKEvents,
       ({ a0 := uEntry.ikAPk, b0 := pEntry.ikAPk, sb := bundle.spkB,
          a1 := ekAPk, pk1 := bundle.pqspkB, ct := kemCt, m := msgPlain,
          matched := false } : SentNoOPKEvent) :: st.sentNoOPKEvents)
    | none, _ => (st.sentOPKEvents, st.sentNoOPKEvents)
  let base' : AuthState S := { st with
    sessions := sessEntry :: st.sessions, usedSendSessions := sid :: st.usedSendSessions,
    sentOPKEvents := sentOPK', sentNoOPKEvents := sentNoOPK',
    roCache := roCache', rootRoCache := rootRoCache' }
  let resp : AuthResponse :=
    if peerPrincipal?.isSome then
      .sendFreshResp wireMsg
    else
      .sendUnfreshResp drKey rk1 ck1_1 wireMsg
  return (resp, { hst with base := base' })
theorem fgPreAuthSendHybrid_run_eq_afterCoins {S : Setup} (useDh1 : Bool) (targetIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthFgCutoffState S)
    (hLen : (m0.length != m1.length) = false)
    (hSid : hst.base.usedSendSessions.contains sid = false)
    (uEntry : PrincipalEntry)
    (hPrin : ∃ idx0, hst.base.principals.find? (fun (idx, _) => idx == u.val) = some (idx0, uEntry))
    (hFreshM : (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
      | some (_, pEntry) => !pEntry.corrupted
      | none => false) && (m0 != m1)) = false)
    (hKosk : koskBundleOk P hst.base.principals hst.base.spkBundles
      hst.base.opkEntries hst.base.advKeys bundle = true) :
    (liftAuthFgHybrid
      (fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P sid u bundle m0 m1)).run hst =
      ((match optUsk with
        | some uSk =>
          if !useDh1 && (initSessionSlotIdx sid == targetIdx) then pure uSk else sampleScalar32
        | none => sampleScalar32) >>= fun ekASk =>
        sampleAuthSendCoins >>= fun coins =>
        fgPreAuthSendAfterCoins P sid uEntry bundle m0 m1 hst ekASk coins) := by
  rcases hPrin with ⟨idx0, hP⟩
  unfold liftAuthFgHybrid fgPreAuthSendHybrid fgPreAuthSendAfterCoins sampleAuthSendCoins mkG3Hybrid
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
    hLen, hSid, hP, hFreshM, hKosk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    AuthHybridStage.idealFreshAead, AuthHybridStage.idealDrKey,
    AuthHybridStage.idealRk, AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
    Bool.and_false, StateT.run_monadLift, monadLift_self, bind_assoc]
  congr 1; funext ekASk
  congr 1; funext kemCoins
  congr 1; funext ephASk
  congr 1; funext spqrCoins
  by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
        (encodeEC bundle.spkB) bundle.spkSig &&
      P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
        (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
  · simp [hSig, StateT.run_pure]
  · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => simp [StateT.run_pure]
    | some sc =>
      rcases sc with ⟨ss, kemCt⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        bind_assoc, pure_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitSend drKey.pqrKey spqrCoins with
      | none => simp [StateT.run_pure]
      | some spqr =>
        rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_set, pure_bind]
        split_ifs <;> simp [StateT.run_pure]
theorem fgPreAuthSend_before_c0 {S : Setup} (targetIdx : ℕ)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthFgCutoffState S) :
    (∀ uSk, (liftAuthFgHybrid
      (fgPreAuthSendHybrid .g3 true false targetIdx (some uSk) S P sid u bundle m0 m1)).run hst =
      (liftAuthFgHybrid
        (fgPreAuthSendHybrid .g3 true false targetIdx none S P sid u bundle m0 m1)).run hst) ∨
    ∃ (fPre : Bytes → Bytes × Bytes × Bytes → ProbComp (AuthResponse × AuthFgCutoffState S)),
      (∀ uSk, (liftAuthFgHybrid
        (fgPreAuthSendHybrid .g3 true false targetIdx (some uSk) S P sid u bundle m0 m1)).run hst =
        (sampleAuthSendCoins >>= fPre uSk)) ∧
      (∀ obs : AuthResponse × AuthFgCutoffState S → ProbComp Bool,
        𝒟[(liftAuthFgHybrid
          (fgPreAuthSendHybrid .g3 true false targetIdx none S P sid u bundle m0 m1)).run hst >>=
          obs] =
        𝒟[sampleAuthSendCoins >>= fun coins => sampleScalar32 >>= fun uSk =>
          fPre uSk coins >>= obs]) ∧
      (∀ coins,
        (∃ x0, ∀ uSk, fPre uSk coins = pure x0) ∨
        (∀ uSk, ∀ x ∈ support (fPre uSk coins), hasFiredAuthSess S targetIdx x.2)) := by
  by_cases hSlot : (initSessionSlotIdx sid == targetIdx) = true
  · by_cases hLen : (m0.length != m1.length) = true
    · refine Or.inl (fun uSk => ?_)
      unfold liftAuthFgHybrid fgPreAuthSendHybrid mkG3Hybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hLen, ↓reduceIte]
    · have hLenF : (m0.length != m1.length) = false := Bool.eq_false_iff.mpr hLen
      cases hSid : hst.base.usedSendSessions.contains sid
      · cases hPrin : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          refine Or.inl (fun uSk => ?_)
          unfold liftAuthFgHybrid fgPreAuthSendHybrid mkG3Hybrid
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
            hLenF, hSid, hPrin, Bool.false_eq_true, ↓reduceIte]
        | some p =>
          rcases p with ⟨idx0, uEntry⟩
          by_cases hFreshM : (!(match findHonestPrincipal P hst.base.principals bundle.ikB with
              | some (_, pEntry) => !pEntry.corrupted
              | none => false) && (m0 != m1)) = true
          · refine Or.inl (fun uSk => ?_)
            unfold liftAuthFgHybrid fgPreAuthSendHybrid mkG3Hybrid
            simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
              hLenF, hSid, hPrin, hFreshM, Bool.false_eq_true, ↓reduceIte]
          · have hFreshMF := Bool.eq_false_iff.mpr hFreshM
            by_cases hKosk : koskBundleOk P hst.base.principals hst.base.spkBundles
              hst.base.opkEntries hst.base.advKeys bundle = true
            · refine Or.inr ⟨fgPreAuthSendAfterCoins P sid uEntry bundle m0 m1 hst,
                fun uSk => ?_, fun obs => ?_, fun ⟨kemCoins, ephASk, spqrCoins⟩ => ?_⟩
              · rw [fgPreAuthSendHybrid_run_eq_afterCoins false targetIdx (some uSk) P
                  sid u bundle m0 m1 hst
                  hLenF hSid uEntry ⟨idx0, hPrin⟩ hFreshMF hKosk]
                simp [hSlot]
              · rw [fgPreAuthSendHybrid_run_eq_afterCoins false targetIdx none P
                  sid u bundle m0 m1 hst
                  hLenF hSid uEntry ⟨idx0, hPrin⟩ hFreshMF hKosk]
                simp only [bind_assoc]
                exact OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleAuthSendCoins _
              · unfold fgPreAuthSendAfterCoins
                dsimp only
                by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                      (encodeEC bundle.spkB) bundle.spkSig &&
                    P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                      (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
                · refine Or.inl ⟨(.noneResp, hst), fun _ => ?_⟩
                  simp only [hSig, ↓reduceIte]
                · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemEncaps bundle.pqspkB kemCoins with
                  | none => exact Or.inl ⟨(.noneResp, hst), fun _ => rfl⟩
                  | some sc =>
                    rcases sc with ⟨ss, kemCt⟩
                    refine Or.inr (fun uSk x hx => ?_)
                    dsimp only at hx
                    simp only [MonadAttach.mem_support_bind] at hx
                    rcases hx with ⟨⟨drKey, roCache'⟩, _, ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, hx⟩
                    have hSpqrSome :=
                      hP.toWellFormedPrimitivesδ.spqrInitSend_some drKey.pqrKey spqrCoins
                    rcases Option.isSome_iff_exists.mp hSpqrSome with
                      ⟨⟨pqrStA, spqrSalt?, pqRatchetMsg⟩, hSpqr⟩
                    rw [hSpqr] at hx
                    dsimp only at hx
                    simp only [support_pure, Set.mem_singleton_iff] at hx
                    have hB := (Prod.mk.inj hx).2
                    unfold hasFiredAuthSess
                    rw [hB]
                    simp [hSlot]
            · have hKoskF := Bool.eq_false_iff.mpr hKosk
              refine Or.inl (fun uSk => ?_)
              unfold liftAuthFgHybrid fgPreAuthSendHybrid mkG3Hybrid
              simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
                hLenF, hSid, hPrin, hFreshMF, hKoskF, Bool.not_false,
                Bool.false_eq_true, ↓reduceIte]
      · refine Or.inl (fun uSk => ?_)
        unfold liftAuthFgHybrid fgPreAuthSendHybrid mkG3Hybrid
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind,
          hLenF, hSid, Bool.false_eq_true, ↓reduceIte]
  · refine Or.inl (fun uSk => ?_)
    have hSlotF : (!false && (initSessionSlotIdx sid == targetIdx)) = false := by simp [hSlot]
    unfold fgPreAuthSendHybrid
    simp only [hSlotF, Bool.false_eq_true, ↓reduceIte]
theorem mem_support_liftAuthFgBase {S : Setup}
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support ((liftAuthFgBase m).run hst)) :
    (x.1, x.2.base) ∈ support (m.run hst.base) ∧
    x.2.advRoLog = hst.advRoLog ∧
    x.2.respRecs = hst.respRecs := by
  unfold liftAuthFgBase at hx
  simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨r, b'⟩, hb, rfl⟩
  exact ⟨hb, rfl, rfl⟩
private theorem SatisfiesAt.set_bind_fg {St R : Type} (Q : St → Prop) (st st' : St)
    {f : PUnit → StateT St ProbComp R}
    (hf : SatisfiesAt Q st' (f PUnit.unit)) :
    SatisfiesAt Q st (set st' >>= f) := by
  intro x hx
  simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
  exact hf x hx
def SendHybridPost {S : Setup} (sid : SessionId S) (spkB : Bytes)
    (h h' : AuthHybridState S) : Prop :=
  h'.base.principals = h.base.principals ∧
  h'.base.spkBundles = h.base.spkBundles ∧
  (h'.base = h.base ∨
    (h.base.usedSendSessions.contains sid = false ∧
     h'.base.usedSendSessions = sid :: h.base.usedSendSessions ∧
     ∃ sessEntry : AuthInitiatorEntry S,
       sessEntry.sid = sid ∧ sessEntry.peerSpkPk = spkB ∧
       h'.base.sessions = sessEntry :: h.base.sessions))
theorem fgPreAuthSendHybrid_satisfies (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    {S : Setup} (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (h : AuthHybridState S) :
    SatisfiesAt (SendHybridPost sid bundle.spkB h) h
      (fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P sid u bundle m0 m1) := by
  have h0 : SendHybridPost sid bundle.spkB h h := ⟨rfl, rfl, Or.inl rfl⟩
  unfold fgPreAuthSendHybrid
  apply SatisfiesAt.get_bind; dsimp only
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro hSid
  cases h.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some p =>
    rcases p with ⟨_, uEntry⟩; dsimp only
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.liftM_bind; intro ekASk
    apply SatisfiesAt.liftM_bind; intro kemCoins
    apply SatisfiesAt.liftM_bind; intro ephASk
    apply SatisfiesAt.liftM_bind; intro spqrCoins
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    cases P.kemEncaps bundle.pqspkB kemCoins with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some sc =>
      rcases sc with ⟨ss, kemCt⟩; dsimp only
      rcases checkBundleProvenanceExact P h.base.principals h.base.spkBundles
          h.base.opkEntries bundle with
        ⟨spkHon, opkHon, pqspkHon⟩; dsimp only
      simp only [AuthHybridStage.idealDrKey, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      apply SatisfiesAt.liftM_bind; rintro ⟨drKey, roCache'⟩
      simp only [AuthHybridStage.idealRk, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      apply SatisfiesAt.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      simp only [AuthHybridStage.idealCk, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [pure_bind]; dsimp only
      cases P.spqrInitSend drKey.pqrKey spqrCoins with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some spqr =>
        rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
        simp only [AuthHybridStage.idealMsgKeys, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [pure_bind]
        apply SatisfiesAt.set_bind_fg
        split_ifs <;> exact SatisfiesAt.pure _ _ _ ⟨rfl, rfl, Or.inr ⟨hSid, rfl, _, rfl, rfl, rfl⟩⟩
theorem fgPreAuthSendHybrid_support (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    {S : Setup} (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support ((liftAuthFgHybrid
      (fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P sid u bundle m0 m1)).run hst)) :
    x.2.base.principals = hst.base.principals ∧
    x.2.base.spkBundles = hst.base.spkBundles ∧
    (x.2.base = hst.base ∨
      (hst.base.usedSendSessions.contains sid = false ∧
       x.2.base.usedSendSessions = sid :: hst.base.usedSendSessions ∧
       ∃ sessEntry : AuthInitiatorEntry S,
         sessEntry.sid = sid ∧ sessEntry.peerSpkPk = bundle.spkB ∧
         x.2.base.sessions = sessEntry :: hst.base.sessions)) := by
  unfold liftAuthFgHybrid at hx
  simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨resp, h'⟩, hh, rfl⟩
  exact fgPreAuthSendHybrid_satisfies useDh1 targetIdx optUsk P sid u bundle m0 m1
    (mkG3Hybrid hst.base) (resp, h') hh
def PreservesPrinSpkSess {S : Setup} (h h' : AuthHybridState S) : Prop :=
  h'.base.principals = h.base.principals ∧
  h'.base.spkBundles = h.base.spkBundles ∧
  h'.base.usedSendSessions = h.base.usedSendSessions ∧
  h'.base.sessions = h.base.sessions
theorem pqxdhAuthHybridKoskImpl_recvOPK_preserves {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) :
    SatisfiesAt (PreservesPrinSpkSess h) h
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvOPK k j o msg)) := by
  have h0 : PreservesPrinSpkSess h h := ⟨rfl, rfl, rfl, rfl⟩
  unfold pqxdhAuthHybridKoskImpl
  apply SatisfiesAt.get_bind; dsimp only
  iterate 4 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      cases h.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some op =>
        rcases op with ⟨_, oEntry⟩; dsimp only
        apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some ss =>
          dsimp only
          apply SatisfiesAt.set_bind_fg
          apply SatisfiesAt.liftM_bind; intro schedOut
          cases schedOut with
          | none => exact SatisfiesAt.pure _ _ _ h0
          | some tup =>
            rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
            cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
            | none =>
              apply SatisfiesAt.set_bind_fg; exact SatisfiesAt.pure _ _ _ h0
            | some sp =>
              rcases sp with ⟨_, senderEntry⟩; dsimp only
              cases !senderEntry.corrupted <;>
              · simp only [Bool.false_eq_true, ↓reduceIte]
                apply SatisfiesAt.set_bind_fg; exact SatisfiesAt.pure _ _ _ h0
theorem pqxdhAuthHybridKoskImpl_recvNoOPK_preserves {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (h : AuthHybridState S) :
    SatisfiesAt (PreservesPrinSpkSess h) h
      (pqxdhAuthHybridKoskImpl .g3 true false S P (.recvNoOPK k j l msg)) := by
  have h0 : PreservesPrinSpkSess h h := ⟨rfl, rfl, rfl, rfl⟩
  unfold pqxdhAuthHybridKoskImpl
  apply SatisfiesAt.get_bind; dsimp only
  iterate 4 (apply SatisfiesAt.ite_return _ _ _ _ h0; intro _)
  cases h.base.principals.find? (fun (idx, _) => idx == k.val) with
  | none => exact SatisfiesAt.pure _ _ _ h0
  | some kp =>
    rcases kp with ⟨_, kEntry⟩; dsimp only
    cases h.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => exact SatisfiesAt.pure _ _ _ h0
    | some bp =>
      rcases bp with ⟨_, bEntry⟩; dsimp only
      apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
      cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => exact SatisfiesAt.pure _ _ _ h0
      | some ss =>
        dsimp only
        apply SatisfiesAt.set_bind_fg
        apply SatisfiesAt.liftM_bind; intro schedOut
        cases schedOut with
        | none => exact SatisfiesAt.pure _ _ _ h0
        | some tup =>
          rcases tup with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
          cases findHonestPrincipal P h.base.principals msg.hdr.ikAPk with
          | none =>
            apply SatisfiesAt.set_bind_fg; exact SatisfiesAt.pure _ _ _ h0
          | some sp =>
            rcases sp with ⟨_, senderEntry⟩; dsimp only
            cases !senderEntry.corrupted <;>
            · simp only [Bool.false_eq_true, ↓reduceIte]
              apply SatisfiesAt.set_bind_fg; exact SatisfiesAt.pure _ _ _ h0
theorem pqxdhAuthFgImpl_preserves_prin_spk_sess {S : Setup} (P : Primitives)
    (q : AuthQuery S)
    (hNotInit : ∀ u, q ≠ .initPrin u)
    (hNotCorr : ∀ u, q ≠ .corruptIK u)
    (hNotSpk : ∀ u j, q ≠ .genSPK u j)
    (hNotSendOPK : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hNotSendNoOPK : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support ((pqxdhAuthFgImpl S P q).run hst)) :
    x.2.base.principals = hst.base.principals ∧
    x.2.base.spkBundles = hst.base.spkBundles ∧
    x.2.base.usedSendSessions = hst.base.usedSendSessions ∧
    x.2.base.sessions = hst.base.sessions := by
  cases q with
  | initPrin u => exact absurd rfl (hNotInit u)
  | corruptIK u => exact absurd rfl (hNotCorr u)
  | genSPK u j => exact absurd rfl (hNotSpk u j)
  | sendOPK u i b m0 m1 => exact absurd rfl (hNotSendOPK u i b m0 m1)
  | sendNoOPK u i b m0 m1 => exact absurd rfl (hNotSendNoOPK u i b m0 m1)
  | recvOPK k j o msg =>
    unfold pqxdhAuthFgImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact pqxdhAuthHybridKoskImpl_recvOPK_preserves P k j o msg (mkG3Hybrid hst.base) (resp, h') hh
  | recvNoOPK k j l msg =>
    unfold pqxdhAuthFgImpl at hx
    simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, h'⟩, hh, rfl⟩
    exact pqxdhAuthHybridKoskImpl_recvNoOPK_preserves P k j l msg
      (mkG3Hybrid hst.base) (resp, h') hh
  | genOPK u j o =>
    change x ∈ support ((liftAuthFgHybrid (do
      let h ← get; let _ := h.base
      liftAuthBase (pqxdhAuthImpl true false S P (.genOPK u j o)))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
  | roQuery secrets =>
    unfold pqxdhAuthFgImpl pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl mkG3Hybrid at hx
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, Bool.false_and, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨dk, roCache'⟩, _, hEq⟩
    rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
  | roRootQuery rk dh =>
    change x ∈ support ((liftAuthFgHybrid (do
      let h ← get; let _ := h.base
      liftAuthBase (pqxdhAuthImpl true false S P (.roRootQuery rk dh)))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hb
    rcases hb with ⟨⟨out, rootRoCache'⟩, _, hEq⟩
    rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
  | revealDhSecrets =>
    change x ∈ support ((liftAuthFgHybrid (do
      let h ← get; let _ := h.base
      liftAuthBase (pqxdhAuthImpl true false S P .revealDhSecrets))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ↓reduceIte, pure_bind,
      support_pure, Set.mem_singleton_iff] at hb
    rw [(Prod.mk.inj hb).2]; exact ⟨rfl, rfl, rfl, rfl⟩
  | registerKey sk =>
    change x ∈ support ((liftAuthFgHybrid (do
      let h ← get; let _ := h.base
      liftAuthBase (pqxdhAuthImpl true false S P (.registerKey sk)))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases registerAdvKey P hst.base.advKeys sk with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]; exact ⟨rfl, rfl, rfl, rfl⟩
theorem pqxdhAuthFgPreImpl_preserves_hasFired {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (x : AuthResponse × AuthFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst)) :
    (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
  have unchanged :
      x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.usedSendSessions = hst.base.usedSendSessions →
      (∀ bIdx, hasFiredAuthSpk S bIdx hst → hasFiredAuthSpk S bIdx x.2) ∧
      (∀ uIdx, hasFiredAuthPrin S uIdx hst → hasFiredAuthPrin S uIdx x.2) ∧
      (∀ sIdx, hasFiredAuthSess S sIdx hst → hasFiredAuthSess S sIdx x.2) := by
    intro hP hS hSe
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
      fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hP]; exact h,
      fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hSe]; exact h⟩
  cases q with
  | initPrin u =>
    unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold fgPreAuthInitPrin at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, _, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
        fun uIdx h => ?_,
        fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩
      unfold hasFiredAuthPrin at h ⊢; rw [hB]; simp [h]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
  | corruptIK u =>
    change x ∈ support ((liftAuthFgHybrid (do
      let h ← get; let _ := h.base
      liftAuthBase (pqxdhAuthImpl true false S P (.corruptIK u)))).run hst) at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold pqxdhAuthImpl at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
    | some p =>
      rcases p with ⟨_, entry⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
        fun uIdx h => ?_,
        fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩
      unfold hasFiredAuthPrin at h ⊢; rw [hB]; dsimp only
      rw [List.any_map]
      have hfn : ((fun (x : Nat × PrincipalEntry) => x.1 == uIdx) ∘ fun (idx, e) =>
          if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) =
          (fun (x : Nat × PrincipalEntry) => x.1 == uIdx) := by
        funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
      rw [hfn]; exact h
  | genSPK u j =>
    unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx
    rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
    rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
    unfold fgPreAuthGenSPK at hb
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, _, _, _, _, hEq⟩
        have hB := (Prod.mk.inj hEq).2
        refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; simp [h2]⟩,
          fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hB]; exact h,
          fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hB]; exact h⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl at hx
    by_cases hOpt : bundle.opkB?.isNone = true
    · unfold liftAuthFgHybrid mkG3Hybrid at hx
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      have hB := (Prod.mk.inj hx).2
      exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isNone then return .noneResp
          fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P
            (.sendOPK u i) u bundle m0 m1)).run hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P
          (.sendOPK u i) u bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq] at hx
      rcases fgPreAuthSendHybrid_support useDh1 targetIdx optUsk P
          (.sendOPK u i) u bundle m0 m1 hst x hx with
        ⟨hP, hS, hBase | ⟨_, hSe, _⟩⟩
      · exact unchanged (by rw [hBase]) (by rw [hBase]) (by rw [hBase])
      · refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
          fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hP]; exact h,
          fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hSe]; simp [h]⟩
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthFgPreImpl at hx
    by_cases hOpt : bundle.opkB?.isSome = true
    · unfold liftAuthFgHybrid mkG3Hybrid at hx
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      have hB := (Prod.mk.inj hx).2
      exact unchanged (by rw [hB]) (by rw [hB]) (by rw [hB])
    · have hRunEq : (liftAuthFgHybrid (do
          let hst ← get; let _ := hst.base
          if bundle.opkB?.isSome then return .noneResp
          fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P
            (.sendNoOPK u i) u bundle m0 m1)).run hst =
        (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true useDh1 targetIdx optUsk S P
          (.sendNoOPK u i) u bundle m0 m1)).run hst := by
        unfold liftAuthFgHybrid; simp [hOpt]
      rw [hRunEq] at hx
      rcases fgPreAuthSendHybrid_support useDh1 targetIdx optUsk P
          (.sendNoOPK u i) u bundle m0 m1 hst x hx with
        ⟨hP, hS, hBase | ⟨_, hSe, _⟩⟩
      · exact unchanged (by rw [hBase]) (by rw [hBase]) (by rw [hBase])
      · refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
          fun uIdx h => by unfold hasFiredAuthPrin at h ⊢; rw [hP]; exact h,
          fun sIdx h => by unfold hasFiredAuthSess at h ⊢; rw [hSe]; simp [h]⟩
  | genOPK u j o =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.genOPK u j o)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | recvOPK k j o msg =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvOPK k j o msg)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | recvNoOPK k j l msg =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvNoOPK k j l msg)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | roQuery secrets =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roQuery secrets)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | roRootQuery rk dh =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roRootQuery rk dh)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | revealDhSecrets =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P .revealDhSecrets
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
  | registerKey sk =>
    rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.registerKey sk)
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) hst x hx with ⟨hP, hS, hSe, _⟩
    exact unchanged hP hS hSe
theorem evalDist_preSample_V_pqxdhAuthFgPreImpl {S : Setup} {α : Type}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredAuthSpk S targetSpkIdx)
    (pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhAuthFgPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgPreImpl_preserves_hasFired useDh1 targetIdx targetSpkIdx optUsk none P q s x hx).1
        targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      unfold fgPreAuthGenSPK liftAuthFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · have hany := spkBundles_any_of_hasFiredAuthSpk S targetSpkIdx s hFired u j hSlot
        simp [hany]
      · cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => rfl
  · cases q with
    | genSPK u j =>
      unfold pqxdhAuthFgPreImpl
      simp only [liftAuthFgHybrid_liftAuthBase_eq]
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · unfold fgPreAuthGenSPK liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact Or.inl (fun _ => rfl)
          | some p =>
            rcases p with ⟨_, uEntry⟩
            dsimp only
            refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨rSpk, _, pqPair, _, rPq, _, hEq⟩
              have hB := (Prod.mk.inj hEq).2
              exact ⟨u, j, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold fgPreAuthGenSPK liftAuthFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => exact Or.inl (fun _ => rfl)
theorem fgPreAuthSendHybrid_eq_of_hasFiredAuthSess {S : Setup} (targetIdx : ℕ) (uSk : Bytes)
    (P : Primitives) (sid : SessionId S) (hSidLt : initSessionSlotIdx sid < S.N_send_tot)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s : AuthFgCutoffState S) (hFired : hasFiredAuthSess S targetIdx s) :
    (fgPreAuthSendHybrid .g3 true false targetIdx (some uSk) S P sid u bundle m0 m1).run
        (mkG3Hybrid s.base) =
      (fgPreAuthSendHybrid .g3 true false targetIdx none S P sid u bundle m0 m1).run
        (mkG3Hybrid s.base) := by
  by_cases hSlot : (initSessionSlotIdx sid == targetIdx) = true
  · have hany := usedSendSessions_contains_of_hasFiredAuthSess targetIdx s hFired sid hSlot hSidLt
    unfold fgPreAuthSendHybrid mkG3Hybrid
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases (m0.length != m1.length) <;> simp only [hany, Bool.false_eq_true, ↓reduceIte]
  · have hSlotF : (!false && (initSessionSlotIdx sid == targetIdx)) = false := by simp [hSlot]
    unfold fgPreAuthSendHybrid
    simp only [hSlotF, Bool.false_eq_true, ↓reduceIte]
theorem evalDist_preSample_U_dh3_pqxdhAuthFgPreImpl {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (oa : OracleComp (unifSpec + authSpec S) α) (hst : AuthFgCutoffState S)
    (obs : α × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl false targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl false targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq_c0
    sampleScalar32
    sampleAuthSendCoins
    (hasFiredAuthSess S targetIdx)
    (pqxdhAuthFgPreImpl false targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhAuthFgPreImpl false targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhAuthFgPreImpl_preserves_hasFired false targetIdx targetSpkIdx
        none optVsk P q s x hx).2.2
        targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl liftAuthFgHybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isNone
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fgPreAuthSendHybrid_eq_of_hasFiredAuthSess targetIdx uSk P (.sendOPK u i)
          (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
          u bundle m0 m1 s hFired]
      · rfl
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl liftAuthFgHybrid
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      cases bundle.opkB?.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [fgPreAuthSendHybrid_eq_of_hasFiredAuthSess targetIdx uSk P (.sendNoOPK u i)
          (initSessionSlotIdx_sendNoOPK_lt u i) u bundle m0 m1 s hFired]
      · rfl
    | _ => rfl
  · cases q with
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl
      by_cases hOpt : bundle.opkB?.isNone = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftAuthFgHybrid; simp [hOpt]
      · have hEqPre : ∀ optU, (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isNone then return .noneResp
            fgPreAuthSendHybrid .g3 true false targetIdx optU S P
              (.sendOPK u i) u bundle m0 m1)).run s =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false targetIdx optU S P
            (.sendOPK u i) u bundle m0 m1)).run s := by
          intro optU; unfold liftAuthFgHybrid; simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreAuthSend_before_c0 targetIdx P hP (.sendOPK u i) u bundle m0 m1 s
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl
      by_cases hOpt : bundle.opkB?.isSome = true
      · refine Or.inl (fun uSk => ?_)
        unfold liftAuthFgHybrid; simp [hOpt]
      · have hEqPre : ∀ optU, (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isSome then return .noneResp
            fgPreAuthSendHybrid .g3 true false targetIdx optU S P
              (.sendNoOPK u i) u bundle m0 m1)).run s =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false targetIdx optU S P
            (.sendNoOPK u i) u bundle m0 m1)).run s := by
          intro optU; unfold liftAuthFgHybrid; simp [hOpt]
        simp_rw [hEqPre]
        exact fgPreAuthSend_before_c0 targetIdx P hP (.sendNoOPK u i) u bundle m0 m1 s
    | _ => exact Or.inl (fun _ => rfl)
theorem evalDist_runAuthFgSim_eq_preSample_dh3 {S : Setup}
    (sIdx bIdx : ℕ) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (A : AuthAdversary S)
    (obs : Bool × Bool × AuthFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (AuthFgCutoffState S) ProbComp) +
      pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := AuthFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
    𝒟[runAuthFgSim S P A >>= obs] := by
  intro fullPre
  unfold runAuthFgSim
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (AuthFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthFgCutoffState S) ProbComp) +
        pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) none S P) A.run).run
          (AuthFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_V_pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) P A.run
      (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_U_dh3_pqxdhAuthFgPreImpl sIdx bIdx none P hP A.run
    (AuthFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhAuthFgPreImpl_none_none_eq]
  simp only [pure_bind]

/-! ## Target abort flags -/
def spkTargetIsVAuth {S : Setup} (bIdx : ℕ) (V : Bytes) (hst : AuthFgCutoffState S) : Bool :=
  hst.base.spkBundles.all (fun (k, bEntry) =>
    !(spkBundleFlatIdxVal S k == bIdx) || (bEntry.spkPk == V))
def deadAuthDh3 {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    (hst : AuthFgCutoffState S) : Bool :=
  spkTargetIsVAuth bIdx V hst &&
  hst.base.usedSendSessions.any (fun sid => initSessionSlotIdx sid == sIdx) &&
  match hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | some s => P.pow8 s.peerSpkPk != P.pow8 V
  | none   => false
theorem badAuthFgDh3AtCore_eq_false_of_deadAuthDh3 {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (V : Bytes) (hst : AuthFgCutoffState S)
    (hDead : deadAuthDh3 P sIdx bIdx V hst = true) :
    badAuthFgDh3AtCore P maxLen sIdx bIdx hst.base hst.advRoLog hst.respRecs = false := by
  unfold deadAuthDh3 spkTargetIsVAuth at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨h1, hSess⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨hAll, _⟩
  unfold badAuthFgDh3AtCore
  cases hF1 : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s =>
    rw [hF1] at hSess
    cases hF2 : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨k, bEntry⟩; dsimp only
      have hMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hF2
      have hIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
        List.find?_some
          (p := fun (x : (Nat × Nat) × SpkBundleEntry) => spkBundleFlatIdxVal S x.1 == bIdx) hF2
      have hItem := List.all_eq_true.mp hAll (k, bEntry) hMem
      simp only [hIdx, Bool.not_true, Bool.false_or, beq_iff_eq] at hItem
      rw [hItem]
      have hNe : (P.pow8 s.peerSpkPk == P.pow8 V) = false := by simpa [bne] using hSess
      simp [hNe]
theorem pqxdhAuthFgPreImpl_preserves_deadAuthDh3 {S : Setup} (P : Primitives)
    (sIdx bIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : AuthQuery S) (hst : AuthFgCutoffState S)
    (hDead : deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhAuthFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadAuthDh3 P sIdx bIdx (P.x25519Base vSk) x.2 = true := by
  set V := P.x25519Base vSk
  have hUnchanged : ∀ x : AuthResponse × AuthFgCutoffState S,
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.usedSendSessions = hst.base.usedSendSessions →
      x.2.base.sessions = hst.base.sessions →
      deadAuthDh3 P sIdx bIdx V x.2 = true := by
    intro x hSpk hUsed hSess
    unfold deadAuthDh3 spkTargetIsVAuth at hDead ⊢
    rw [hSpk, hUsed, hSess]; exact hDead
  unfold deadAuthDh3 at hDead
  rcases Bool.and_eq_true_iff.mp hDead with ⟨h1, hSessFind⟩
  rcases Bool.and_eq_true_iff.mp h1 with ⟨hAll, hFired⟩
  cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rw [hFS] at hSessFind; cases hSessFind
  | some s0 =>
    rw [hFS] at hSessFind
    intro x hx
    cases q with
    | initPrin u =>
      unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx; rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
      unfold fgPreAuthInitPrin at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hst.base.principals.any (fun (idx, _) => idx == u.val)
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
    | corruptIK u =>
      change x ∈ support ((liftAuthFgHybrid (do
        let h ← get; let _ := h.base
        liftAuthBase (pqxdhAuthImpl true false S P (.corruptIK u)))).run hst) at hx
      rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
      unfold pqxdhAuthImpl at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
      | some p =>
        rcases p with ⟨_, _⟩
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
    | genSPK u j =>
      unfold pqxdhAuthFgPreImpl at hx; dsimp only at hx; rw [liftAuthFgHybrid_liftAuthBase_eq] at hx
      rcases mem_support_liftAuthFgBase _ hst x hx with ⟨hb, _⟩
      unfold fgPreAuthGenSPK at hb
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb
      cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
        | some p =>
          rcases p with ⟨_, uEntry⟩
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
            support_pure, Set.mem_singleton_iff]
          rintro ⟨spkSk, hSk, rSpk, _, pqPair, _, rPq, _, hEq⟩
          have hB := (Prod.mk.inj hEq).2
          unfold deadAuthDh3
          rw [hB]; dsimp only
          rw [hFired, hFS]
          simp only [hSessFind, Bool.and_true]
          unfold spkTargetIsVAuth at hAll ⊢
          rw [hB]; dsimp only
          rw [List.all_cons, hAll, Bool.and_true]
          by_cases hSlot : (spkBundleFlatIdx S u j == bIdx) = true
          · simp only [hSlot, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSk
            subst hSk
            have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = true := by
              simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
            simp [hSlotV, V]
          · have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
              simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
            simp [hSlotV]
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
    | sendOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl at hx
      by_cases hOpt : bundle.opkB?.isNone = true
      · unfold liftAuthFgHybrid mkG3Hybrid at hx
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        have hB := (Prod.mk.inj hx).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
      · have hRunEq : (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isNone then return .noneResp
            fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P
              (.sendOPK u i) u bundle m0 m1)).run hst =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P
            (.sendOPK u i) u bundle m0 m1)).run hst := by
          unfold liftAuthFgHybrid; simp [hOpt]
        rw [hRunEq] at hx
        rcases fgPreAuthSendHybrid_support false sIdx (some uSk) P
            (.sendOPK u i) u bundle m0 m1 hst x hx with
          ⟨_, hS, hBase | ⟨hNotUsed, hUsed, sessEntry, hSid, _, hSess⟩⟩
        · exact hUnchanged x (by rw [hBase]) (by rw [hBase]) (by rw [hBase])
        · have hSlotF : (initSessionSlotIdx sessEntry.sid == sIdx) = false := by
            cases hSl : (initSessionSlotIdx sessEntry.sid == sIdx)
            · rfl
            · have hCont :=
                usedSendSessions_contains_of_hasFiredAuthSess sIdx hst hFired sessEntry.sid hSl
                (by rw [beq_iff_eq.mp hSl]; exact hsIdx)
              rw [hSid, hNotUsed] at hCont; cases hCont
          unfold deadAuthDh3; unfold spkTargetIsVAuth at hAll ⊢
          rw [hS, hUsed, hSess]
          simp [hAll, hFired, hSlotF, hFS, hSessFind]
    | sendNoOPK u i bundle m0 m1 =>
      unfold pqxdhAuthFgPreImpl at hx
      by_cases hOpt : bundle.opkB?.isSome = true
      · unfold liftAuthFgHybrid mkG3Hybrid at hx
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hOpt, ↓reduceIte,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
        have hB := (Prod.mk.inj hx).2
        exact hUnchanged x (by rw [hB]) (by rw [hB]) (by rw [hB])
      · have hRunEq : (liftAuthFgHybrid (do
            let hst ← get; let _ := hst.base
            if bundle.opkB?.isSome then return .noneResp
            fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P
              (.sendNoOPK u i) u bundle m0 m1)).run hst =
          (liftAuthFgHybrid (fgPreAuthSendHybrid .g3 true false sIdx (some uSk) S P
            (.sendNoOPK u i) u bundle m0 m1)).run hst := by
          unfold liftAuthFgHybrid; simp [hOpt]
        rw [hRunEq] at hx
        rcases fgPreAuthSendHybrid_support false sIdx (some uSk) P
            (.sendNoOPK u i) u bundle m0 m1 hst x hx with
          ⟨_, hS, hBase | ⟨hNotUsed, hUsed, sessEntry, hSid, _, hSess⟩⟩
        · exact hUnchanged x (by rw [hBase]) (by rw [hBase]) (by rw [hBase])
        · have hSlotF : (initSessionSlotIdx sessEntry.sid == sIdx) = false := by
            cases hSl : (initSessionSlotIdx sessEntry.sid == sIdx)
            · rfl
            · have hCont :=
                usedSendSessions_contains_of_hasFiredAuthSess sIdx hst hFired sessEntry.sid hSl
                (by rw [beq_iff_eq.mp hSl]; exact hsIdx)
              rw [hSid, hNotUsed] at hCont; cases hCont
          unfold deadAuthDh3; unfold spkTargetIsVAuth at hAll ⊢
          rw [hS, hUsed, hSess]
          simp [hAll, hFired, hSlotF, hFS, hSessFind]
    | genOPK u j o =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.genOPK u j o)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | recvOPK k j o msg =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvOPK k j o msg)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | recvNoOPK k j l msg =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.recvNoOPK k j l msg)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | roQuery secrets =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roQuery secrets)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | roRootQuery rk dh =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.roRootQuery rk dh)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | revealDhSecrets =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P .revealDhSecrets
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
    | registerKey sk =>
      rcases pqxdhAuthFgImpl_preserves_prin_spk_sess P (.registerKey sk)
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
        hst x hx with ⟨_, hS, hSe, hSs⟩
      exact hUnchanged x hS hSe hSs
end Proofs.SignalPqxdh.Security
