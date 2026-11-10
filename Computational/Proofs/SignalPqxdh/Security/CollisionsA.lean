/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem
public import Computational.Specifications.Pqxdh.Bound
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Assumptions
public import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
public import Computational.Specifications.Assumptions.KemCorrect
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# PQXDH Hybrid Games and Collision Predicates

Defines real-valued `boolBias` / `boolDist` inequalities, per-sample X25519 and Kyber-1024
fixed-key collision bounds, and the intermediate hybrid games (`G0`–`G3`) and bad-event
predicates for `KeyInd` and `Auth`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

theorem boolBias_le_add_two_mul_boolDist (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.boolBias ≤ ν.boolBias + 2 * μ.boolDist ν := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν, Measure.boolDist]
  calc 2 * ENNReal.absDiff (μ {true}) (1 / 2)
      ≤ 2 * (ENNReal.absDiff (μ {true}) (ν {true}) + ENNReal.absDiff (ν {true}) (1 / 2)) := by
        gcongr
        exact ENNReal.absDiff_triangle _ _ _
    _ = _ := by ring

theorem boolBias_toReal_le_add_two_mul_abs_sub (E₁ E₂ : ProbComp Bool) :
    (𝒟[E₁].boolBias).toReal ≤
      (𝒟[E₂].boolBias).toReal + 2 * |(𝒟[E₁] {true}).toReal - (𝒟[E₂] {true}).toReal| := by
  have hle := boolBias_le_add_two_mul_boolDist 𝒟[E₁] 𝒟[E₂]
  have hfin2 : 𝒟[E₂].boolBias ≠ ⊤ := Measure.boolBias_ne_top 𝒟[E₂]
  have hfind : 𝒟[E₁].boolDist 𝒟[E₂] ≠ ⊤ := Measure.boolDist_ne_top 𝒟[E₁] 𝒟[E₂]
  have hfin_mul : (2 : ℝ≥0∞) * 𝒟[E₁].boolDist 𝒟[E₂] ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfind
  have hfin_rhs : 𝒟[E₂].boolBias + 2 * 𝒟[E₁].boolDist 𝒟[E₂] ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfin2, hfin_mul⟩
  have hreal := (ENNReal.toReal_le_toReal (Measure.boolBias_ne_top 𝒟[E₁]) hfin_rhs).mpr hle
  rw [ENNReal.toReal_add hfin2 hfin_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    Measure.toReal_boolDist] at hreal
  exact hreal

theorem abs_sub_boolBias_toReal_le_two_mul_abs_sub (E₁ E₂ : ProbComp Bool) :
    |(𝒟[E₁].boolBias).toReal - (𝒟[E₂].boolBias).toReal| ≤
      2 * |(𝒟[E₁] {true}).toReal - (𝒟[E₂] {true}).toReal| := by
  have h1 := boolBias_toReal_le_add_two_mul_abs_sub E₁ E₂
  have h2 := boolBias_toReal_le_add_two_mul_abs_sub E₂ E₁
  rw [abs_sub_comm (𝒟[E₂] {true}).toReal (𝒟[E₁] {true}).toReal] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem gapDh_nonneg (P : Primitives) (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (pow8 : Bytes → Bytes) (A : GapDhAdv) :
    0 ≤ GapDH P isValidDhTriple pow8 A :=
  ENNReal.toReal_nonneg

theorem aeadIndCpa_nonneg (P : Primitives) (A : AeadIndCpaAdv) :
    0 ≤ AeadIndCpaReal P A :=
  ENNReal.toReal_nonneg

theorem sigEufCma_nonneg (P : Primitives) (A : SigEufCmaAdv) :
    0 ≤ SigEufCma P A :=
  ENNReal.toReal_nonneg

theorem keyIndAdvantage_nonneg (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    0 ≤ KeyIndAdvantage S P A :=
  ENNReal.toReal_nonneg

theorem authAdvantage_nonneg (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    0 ≤ AuthAdvantageReal S P A :=
  ENNReal.toReal_nonneg

noncomputable def Pfixed_pk_ec : ℝ := 1 / (2 : ℝ) ^ 250

noncomputable def Pfixed_pk_kem : ℝ := 1 / (2 : ℝ) ^ 255

theorem pfixed_pk_ec_nonneg : 0 ≤ Pfixed_pk_ec := by
  unfold Pfixed_pk_ec; positivity

theorem pfixed_pk_kem_nonneg : 0 ≤ Pfixed_pk_kem := by
  unfold Pfixed_pk_kem; positivity

def hasBadKemShCrRecords {S : Setup} (P : Primitives)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord) : Bool :=
  initRecs.any (fun i =>
    recvRecs.any (fun r =>
      P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs &&
      (r.kemCt != i.kemCt || i.pqspkPk != r.pqspkPk)))

/-! ## `KeyInd` hybrids -/

structure KeyIndHybridState (S : Setup) where
  base        : KeyIndState S
  initKemRecs : List (InitKemRecord S)
  recvKemRecs : List RecvKemRecord

def KeyIndHybridState.empty (S : Setup) (secb : Bool) : KeyIndHybridState S :=
  { base        := KeyIndState.empty S secb
    initKemRecs := []
    recvKemRecs := [] }

/-- Recovers the KEM shared secret encapsulated by initiator session `s` from `st.roCache` or
    `P.kemDecaps`. -/
def recoverKeyIndSessionKemSs {S : Setup} (P : Primitives) (st : KeyIndState S)
    (s : KeyIndInitiatorEntry S) : Option Bytes :=
  match st.principals.find? (fun (_, e) => e.ikAPk == s.hdr.ikAPk) with
  | some (_, uEntry) =>
    let dh1 := P.x25519 uEntry.secIKA0 s.peerSpkPk
    let dh2 := P.x25519 s.ekASk s.peerIkPk
    let dh3 := P.x25519 s.ekASk s.peerSpkPk
    let dh4? := s.peerOpkPk?.map (fun opkPk => P.x25519 s.ekASk opkPk)
    let pfx := match dh4? with
      | none     => F_X25519 ++ dh1 ++ dh2 ++ dh3
      | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4
    match st.roCache.find? (fun (sec, _) =>
        sec.take pfx.length == pfx && sec.length == pfx.length + 32) with
    | some (sec, _) => some (sec.drop pfx.length)
    | none =>
      match st.spkBundles.find? (fun (_, b) => b.pqspkPk == s.peerPqspkPk) with
      | some (_, b) => P.kemDecaps b.pqspkSk s.hdr.kemCt
      | none        => none
  | none => none

class HasKeyIndState (σ : Type) (S : outParam Setup) where
  toKeyIndState : σ → KeyIndState S
  toInitKemRecs : Primitives → σ → List (InitKemRecord S)
  toRecvKemRecs : Primitives → σ → List RecvKemRecord

instance {S : Setup} : HasKeyIndState (KeyIndState S) S where
  toKeyIndState st := st
  toInitKemRecs P st :=
    st.sessions.filterMap (fun s =>
      (recoverKeyIndSessionKemSs P st s).map (fun ss =>
        { sid := s.sid, pqspkPk := s.peerPqspkPk, kemCt := s.hdr.kemCt, kemSs := ss }))
  toRecvKemRecs P st :=
    st.spkBundles.flatMap (fun ((k, j), b) =>
      st.sessions.filterMap (fun s =>
        (P.kemDecaps b.pqspkSk s.hdr.kemCt).map (fun ss =>
          { k := k, j := j, pqspkPk := b.pqspkPk, pqspkSk := b.pqspkSk,
            kemCt := s.hdr.kemCt, kemSs := ss })))

instance {S : Setup} : HasKeyIndState (KeyIndHybridState S) S where
  toKeyIndState st := st.base
  toInitKemRecs _ st := st.initKemRecs
  toRecvKemRecs _ st := st.recvKemRecs

def allHonestEcPksKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S]
    (P : Primitives) (st : σ) : List Bytes :=
  let s0 := HasKeyIndState.toKeyIndState st
  (s0.principals.map (fun (_, e) => P.pow8 e.ikAPk)) ++
  (s0.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)) ++
  (s0.opkEntries.map (fun (_, o) => P.pow8 o.opkPk)) ++
  (s0.sessions.map (fun s => P.pow8 s.hdr.ekAPk))

def allHonestKemPksKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S] (st : σ) : List Bytes :=
  (HasKeyIndState.toKeyIndState st).spkBundles.map (fun (_, b) => b.pqspkPk)

def allInitDh2sKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S]
    (P : Primitives) (st : σ) : List Bytes :=
  let s0 := HasKeyIndState.toKeyIndState st
  s0.sessions.map (fun s => P.x25519 s.ekASk s.peerIkPk)

/-- Checks whether two honest X25519 keys collide in `pow8` or two initiator sessions produce
    colliding `dh2` secrets. -/
def hasEcPkCollisionKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S]
    (P : Primitives) (st : σ) : Bool :=
  hasDuplicateBytes (allHonestEcPksKeyInd P st) ||
  hasDuplicateBytes (allInitDh2sKeyInd P st)

/-- Checks whether two honest Kyber-1024 public keys collide. -/
def hasKemPkCollisionKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S] (st : σ) : Bool :=
  hasDuplicateBytes (allHonestKemPksKeyInd st)

/-- Checks whether any fresh initiator session accepted a forged `spkSig` or `pqspkSig`. -/
def hasBadSigKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S] (st : σ) : Bool :=
  (HasKeyIndState.toKeyIndState st).sessions.any (fun s =>
    s.fresh && (!s.spkHonest || !s.pqspkHonest))

def hasBadKemShCrKeyInd {S : Setup} {σ : Type} [HasKeyIndState σ S]
    (P : Primitives) (st : σ) : Bool :=
  hasBadKemShCrRecords P (HasKeyIndState.toInitKemRecs P st) (HasKeyIndState.toRecvKemRecs P st)

def liftKeyIndBase {S : Setup} {α : Type}
    (m : StateT (KeyIndState S) ProbComp α) : StateT (KeyIndHybridState S) ProbComp α := do
  let st ← get
  let (a, base') ← liftM (m.run st.base)
  set { st with base := base' }
  return a

def runKeyIndHybridInitiate (idealFreshDrKey useRo : Bool) (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndHybridState S) ProbComp KeyIndResponse := do
  let hst ← get
  let st := hst.base
  if st.sessions.any (fun e => e.sid == sid) then return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val) | return .noneResp
  let ekASk ← liftM sampleScalar32
  let kemCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB
  let (drKeyReal, roCache') ←
    if idealFreshDrKey && honestPeer.isSome then do
      let dk ← liftM sampleDRKey96
      pure (dk, st.roCache)
    else
      liftM (evalHkdfOrRo useRo P st.roCache secrets)
  let drKeyRand ← liftM sampleDRKey96
  let hdr : HandshakeHdr := {
    ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
    opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S := {
    sid := sid, honestPeer := honestPeer, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
    peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB,
    spkHonest := spkHon, opkHonest := opkHon, pqspkHonest := pqspkHon,
    ekASk := ekASk, fresh := honestPeer.isSome, drKeyReal := drKeyReal, drKeyRand := drKeyRand,
    hdr := hdr, tested := false }
  let initRec : InitKemRecord S := {
    sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss }
  set { hst with
    base := { st with sessions := sessEntry :: st.sessions, roCache := roCache' }
    initKemRecs := initRec :: hst.initKemRecs }
  match findHonestPrincipal P st.principals bundle.ikB with
  | some _ => return .hdrResp hdr
  | none   => return .initUnfreshResp drKeyReal hdr

def pqxdhKeyIndHybridImpl (idealFreshDrKey useRo : Bool) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndHybridState S) ProbComp) := fun q => do
  match q with
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then return .noneResp
    runKeyIndHybridInitiate idealFreshDrKey useRo S P (.sendOPK u i) u bundle
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then return .noneResp
    runKeyIndHybridInitiate idealFreshDrKey useRo S P (.sendNoOPK u i) u bundle
  | .acceptOPK k j o hdr =>
    let resp ← liftKeyIndBase (pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr))
    let hst ← get
    match resp with
    | .noneResp => return .noneResp
    | _ =>
      match hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | some (_, bEntry) =>
        match P.kemDecaps bEntry.pqspkSk hdr.kemCt with
        | some ss =>
          let rRec : RecvKemRecord := {
            k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
            pqspkSk := bEntry.pqspkSk, kemCt := hdr.kemCt, kemSs := ss }
          set { hst with recvKemRecs := rRec :: hst.recvKemRecs }
          return resp
        | none => return resp
      | none => return resp
  | .acceptNoOPK k j l hdr =>
    let resp ← liftKeyIndBase (pqxdhKeyIndImpl useRo S P (.acceptNoOPK k j l hdr))
    let hst ← get
    match resp with
    | .noneResp => return .noneResp
    | _ =>
      match hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | some (_, bEntry) =>
        match P.kemDecaps bEntry.pqspkSk hdr.kemCt with
        | some ss =>
          let rRec : RecvKemRecord := {
            k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
            pqspkSk := bEntry.pqspkSk, kemCt := hdr.kemCt, kemSs := ss }
          set { hst with recvKemRecs := rRec :: hst.recvKemRecs }
          return resp
        | none => return resp
      | none => return resp
  | q_other =>
    liftKeyIndBase (pqxdhKeyIndImpl useRo S P q_other)

noncomputable def keyIndExpG0 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  pqxdhKeyIndExp S P A

/-- `KeyInd` hybrid `G1`, aborting on X25519 key collision or bundle signature forgery. -/
noncomputable def keyIndExpG1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) +
    pqxdhKeyIndImpl true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.principals finalSt.spkBundles
          finalSt.respSessions s) &&
    finalSt.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.principals finalSt.spkBundles
          finalSt.sessions r)
  if !allTestedClean || hasEcPkCollisionKeyInd P finalSt || hasBadSigKeyInd finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndExpG2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool :=
  keyIndExpG1 S P A

/-- `KeyInd` hybrid `G3`, additionally aborting on KEM public-key or `KemShCr` collision. -/
noncomputable def keyIndExpG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndHybridState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndHybridState S)
    ProbComp) +
    pqxdhKeyIndHybridImpl false true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allTestedClean :=
    finalSt.base.sessions.all (fun s =>
      !s.tested || isKeyIndInitStillFresh P true finalSt.base.principals finalSt.base.spkBundles
          finalSt.base.respSessions s) &&
    finalSt.base.respSessions.all (fun r =>
      !r.tested || isKeyIndRespStillFresh P true finalSt.base.principals finalSt.base.spkBundles
          finalSt.base.sessions r)
  if !allTestedClean || hasEcPkCollisionKeyInd P finalSt || hasBadSigKeyInd finalSt ||
     hasKemPkCollisionKeyInd finalSt || hasBadKemShCrKeyInd P finalSt then
    let coin ← $ᵗ Bool
    return coin
  else
    return (b' == secb)

noncomputable def keyIndAdvG0 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG0 S P A].boolBias).toReal

noncomputable def keyIndAdvG1 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG1 S P A].boolBias).toReal

noncomputable def keyIndAdvG2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG2 S P A].boolBias).toReal

noncomputable def keyIndAdvG3 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) : ℝ :=
  (𝒟[keyIndExpG3 S P A].boolBias).toReal

@[simp]
theorem keyIndAdvG0_eq (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndAdvG0 S P A = KeyIndAdvantage S P A := rfl

@[simp]
theorem keyIndAdvG1_eq_G2 (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    keyIndAdvG1 S P A = keyIndAdvG2 S P A := rfl

/-! ## `Auth` hybrids -/

def allHonestEcPksAuth {S : Setup} {σ : Type} [HasAuthState σ S]
    (P : Primitives) (st : σ) : List Bytes :=
  let s0 := HasAuthState.toAuthState st
  (s0.principals.map (fun (_, e) => P.pow8 e.ikAPk)) ++
  (s0.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)) ++
  (s0.opkEntries.map (fun (_, o) => P.pow8 o.opkPk)) ++
  (s0.sessions.map (fun s => P.pow8 (P.x25519Base s.ekASk)))

def hasEcPkCollisionAuth {S : Setup} {σ : Type} [HasAuthState σ S]
    (P : Primitives) (st : σ) : Bool :=
  hasDuplicateBytes (allHonestEcPksAuth P st)

/-- Checks whether an honest receiver bundle decapsulates a KEM ciphertext to an honest initiator
    session's shared secret under a distinct `(kemCt, pqspkPk)` pair. -/
def hasBadKemShCrAuth {S : Setup} {σ : Type} [HasAuthState σ S]
    (P : Primitives) (st : σ) : Bool :=
  hasBadKemShCrRecords P (HasAuthState.toInitKemRecs P st) (HasAuthState.toRecvKemRecs P st)

def liftAuthBase {S : Setup} {α : Type}
    (m : StateT (AuthState S) ProbComp α) : StateT (AuthHybridState S) ProbComp α := do
  let st ← get
  let (a, base') ← liftM (m.run st.base)
  set { st with base := base' }
  return a

/-- Checks whether an incoming receiver handshake header matches the handshake tuple of a fresh
    initiator session `s`. -/
def matchIdealAuthHandshake {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) : Bool :=
  P.pow8 hdr.ikAPk == P.pow8 s.ikAPk &&
  P.pow8 ikBPk == P.pow8 s.peerIkPk &&
  P.pow8 spkBPk == P.pow8 s.peerSpkPk &&
  (match opkBPk?, s.peerOpkPk? with
   | none, none => true
   | some pk1, some pk2 => P.pow8 pk1 == P.pow8 pk2
   | _, _ => false) &&
  P.pow8 hdr.ekAPk == P.pow8 s.ekAPk &&
  pqspkBPk == s.peerPqspkPk &&
  hdr.kemCt == s.kemCt

/-- Stage-parameterized receiver key-schedule and AEAD helper for `Auth` hybrids `G3`–`G5`. -/
def evalAuthHybridRecvSchedule {S : Setup} (stage : AuthHybridStage) (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg) :
    ProbComp (Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) := do
  let st := hst.base
  let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
  let isUncorruptedHonestSender : Bool :=
    match senderPrincipal? with
    | some (_, sEntry) => !sEntry.corrupted
    | none             => false
  let matchedSess? : Option (IdealAuthSession S) :=
    hst.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
  let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
  let (drKey, roCache') ←
    if useIdealBranch && stage.idealDrKey then
      match matchedSess? with
      | some s => pure (s.drKey, st.roCache)
      | none   => do
        let dk ← sampleDRKey96
        pure (dk, st.roCache)
    else
      evalHkdfOrRo useRo P st.roCache secrets
  let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
  let sameEph : Bool :=
    match matchedSess? with
    | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk
    | none   => false
  let ((rk1, ck1_0), rootRoCache') ←
    if useIdealBranch && stage.idealRk then
      match matchedSess? with
      | some s =>
        if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
        else do
          let r ← sampleBytes32
          let c ← sampleBytes32
          pure ((r, c), st.rootRoCache)
      | none => do
        let r ← sampleBytes32
        let c ← sampleBytes32
        pure ((r, c), st.rootRoCache)
    else
      evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey dhRatchet
  let (mkSeed, ck1_1) ←
    if useIdealBranch && stage.idealCk then
      match matchedSess? with
      | some s =>
        if sameEph then pure (s.mkSeed, s.ck1_1)
        else do
          let ms ← sampleBytes32
          let cn ← sampleBytes32
          pure (ms, cn)
      | none => do
        let ms ← sampleBytes32
        let cn ← sampleBytes32
        pure (ms, cn)
    else
      pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0)
  match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
  | none => return none
  | some (_pqrStB, spqrSalt?) =>
    let sameMsgKeys : Bool :=
      match matchedSess? with
      | some s => sameEph && (spqrSalt? == s.spqrSalt?)
      | none   => false
    let deriveMessageKeys ←
      if useIdealBranch && stage.idealMsgKeys then
        match matchedSess? with
        | some s =>
          if sameMsgKeys then pure s.deriveMessageKeys
          else sampleMessageKeys80
        | none => sampleMessageKeys80
      else
        pure (P.deriveMsgKeys mkSeed spqrSalt?)
    let ad := firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
    let pt? : Option Bytes :=
      if useIdealBranch then
        if sameMsgKeys && stage.idealFreshAead then
          match matchedSess? with
          | some s => if ad == s.ad && msg.aeadCt == s.aeadCt then some s.msgPlain else none
          | none   => none
        else if !sameMsgKeys && isUncorruptedHonestSender && stage.idealUnmatchedRecvAead then
          none
        else
          P.aeadDec deriveMessageKeys ad msg.aeadCt
      else
        P.aeadDec deriveMessageKeys ad msg.aeadCt
    match pt? with
    | none    => return none
    | some pt => return some (drKey, rk1, ck1_1, pt, roCache', rootRoCache')

noncomputable def authExpG0 (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool :=
  pqxdhAuthExp S P A

/-- `Auth` hybrid `G1`, aborting on X25519 key collision or bundle signature forgery. -/
noncomputable def authExpG1 (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthImpl true true S P
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  let allChallengedClean := finalSt.sessions.all (fun s =>
    !s.challenged || authInitCorruptionClause P true finalSt.principals s)
  if hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt then
    $ᵗ Bool
  else if finalSt.hasWonAuth then
    return true
  else if !allChallengedClean then
    $ᵗ Bool
  else
    return (b' == secb)

end SignalPqxdh.Security
