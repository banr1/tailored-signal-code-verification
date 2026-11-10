/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import Computational.Specifications.Assumptions.Assumptions
public import Computational.Specifications.Assumptions.KemCorrect
public import Computational.Specifications.Assumptions.KeyInd1KeyRo
public import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# PQXDH Kyber Ciphertext and Public-Key Length Guards

**Checked by Lean.** Verifies strict `1568`-byte length rejection (`kyberCtLen`, `kyberPkLen`) for
Kyber-1024 ciphertexts and public keys across `modelPrims`, `Model.acceptKeys`, `KeyInd`, and
`KemShCr`. Contrasts `modelPrims` against a `u8Vec`-truncating control (`truncatingModelPrims`) on
zero-padded inputs `ct ++ [0]` and `pk ++ [0]`, and proves that padded-ciphertext, padded-`pqspkB`
KCI, and padded `KemShCr` adversaries achieve advantage `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Guards

open CryptoVerification.E2E SignalPqxdh OracleComp OracleSpec ENNReal MeasureTheory

theorem u8Vec_kyberCtLen_append_zero (ct : Bytes) (h : ct.length = kyberCtLen) :
    u8Vec kyberCtLen (ct ++ [0]) = u8Vec kyberCtLen ct := by
  unfold u8Vec fitVec ofU8
  apply Subtype.ext
  simp only [List.map_append, List.append_assoc]
  rw [List.take_append_of_le_length (by simp [h]), List.take_append_of_le_length (by simp [h])]

theorem u8Vec_kyberPkLen_append_zero (pk : Bytes) (h : pk.length = kyberPkLen) :
    u8Vec kyberPkLen (pk ++ [0]) = u8Vec kyberPkLen pk := by
  unfold u8Vec fitVec ofU8
  apply Subtype.ext
  simp only [List.map_append, List.append_assoc]
  rw [List.take_append_of_le_length (by simp [h]), List.take_append_of_le_length (by simp [h])]

/-- Control variant of `modelPrims` that passes `u8Vec`-truncated inputs to `W.Q` without length
checks. -/
def truncatingModelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) : Primitives :=
  { modelPrims X W with
    kemEncaps := fun pk r =>
      let (ct, ss) := W.Q.encaps (u8Vec kyberPkLen pk) (u8Vec 32 r)
      some (vecU8 ss, vecU8 ct)
    kemDecaps := fun sk ct =>
      some (vecU8 (W.Q.decaps (u8Vec 3168 sk) (u8Vec kyberCtLen ct))) }

theorem truncatingModelPrims_kemDecaps_append_zero_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (sk ct : Bytes) (h : ct.length = kyberCtLen) :
    (truncatingModelPrims X W).kemDecaps sk (ct ++ [0]) =
      (truncatingModelPrims X W).kemDecaps sk ct := by
  dsimp only [truncatingModelPrims]
  rw [u8Vec_kyberCtLen_append_zero ct h]

theorem truncatingModelPrims_kemEncaps_append_zero_eq (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk r : Bytes) (h : pk.length = kyberPkLen) :
    (truncatingModelPrims X W).kemEncaps (pk ++ [0]) r =
      (truncatingModelPrims X W).kemEncaps pk r := by
  dsimp only [truncatingModelPrims]
  rw [u8Vec_kyberPkLen_append_zero pk h]

theorem modelPrims_kemDecaps_append_zero_eq_none (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (sk ct : Bytes) (h : ct.length = kyberCtLen) :
    (modelPrims X W).kemDecaps sk (ct ++ [0]) = none := by
  have hne : ct.length + 1 ≠ kyberCtLen := by omega
  simp [modelPrims, blockLevelPrims, hne]

theorem modelPrims_kemEncaps_append_zero_eq_none (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk r : Bytes) (h : pk.length = kyberPkLen) :
    (modelPrims X W).kemEncaps (pk ++ [0]) r = none := by
  have hne : pk.length + 1 ≠ kyberPkLen := by omega
  simp [modelPrims, blockLevelPrims, hne]

theorem acceptKeys_append_zero_eq_none (P : Primitives) (inp : AcceptKeysInput)
    (h : inp.hdr.kemCt.length = kyberCtLen) :
    Model.acceptKeys P
      { inp with hdr := { inp.hdr with kemCt := inp.hdr.kemCt ++ [0] } } = none := by
  have hne : inp.hdr.kemCt.length + 1 ≠ kyberCtLen := by omega
  cases hopk : inp.hdr.opkId? <;> cases inp.opkBSk? <;>
    simp [Model.acceptKeys, _root_.guard, hne, hopk]

theorem acceptKeys_modelPrims_append_zero_eq_none (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (inp : AcceptKeysInput) (h : inp.hdr.kemCt.length = kyberCtLen) :
    Model.acceptKeys (modelPrims X W)
      { inp with hdr := { inp.hdr with kemCt := inp.hdr.kemCt ++ [0] } } = none :=
  acceptKeys_append_zero_eq_none (modelPrims X W) inp h

theorem keyIndPartner_pad {S : Setup} (P : Primitives) (s : KeyIndInitiatorEntry S)
    (r : KeyIndRespEntry S) (h : r.hdr.kemCt = s.hdr.kemCt ++ [0]) :
    keyIndPartner P s r = false := by
  have hne : s.hdr.kemCt ≠ r.hdr.kemCt := by
    rw [h]; intro e; have := congrArg List.length e; simp at this
  simp [keyIndPartner, hne]

theorem keyIndPartner_pqspk_pad {S : Setup} (P : Primitives) (s : KeyIndInitiatorEntry S)
    (r : KeyIndRespEntry S) (h : s.peerPqspkPk = r.pqspkPk ++ [0]) :
    keyIndPartner P s r = false := by
  have hne : s.peerPqspkPk ≠ r.pqspkPk := by
    rw [h]; intro e; have := congrArg List.length e; simp at this
  simp [keyIndPartner, hne]

theorem matchSentOPK_pad (P : Primitives) (r : RecvdOPKEvent) (s : SentOPKEvent)
    (h : r.ct = s.ct ++ [0]) : matchSentOPK P r s = false := by
  have hne : r.ct ≠ s.ct := by
    rw [h]; intro e; have := congrArg List.length e; simp at this
  simp [matchSentOPK, hne]

private theorem prob_true_eq_zero_of_notMem_support {E : ProbComp Bool}
    (hnot : true ∉ support E) : 𝒟[E] {true} = 0 := by
  by_contra hne
  exact hnot ((OracleComp.mem_support_iff_evalDist_singleton_pos _ _).mpr (pos_iff_ne_zero.mpr hne))

private theorem evalDist_eq_pure_of_support (oa : ProbComp Bool) (a : Bool)
    (h : ∀ z ∈ support oa, z = a) : 𝒟[oa] = 𝒟[(pure a : ProbComp Bool)] := by
  rw [← bind_pure oa, OracleComp.evalDist_bind_congr_of_support oa pure (fun _ => pure a)]
  · exact OracleComp.evalDist_bind_const oa (pure a)
  · intro z hz; rw [h z hz]

private theorem evalDist_uniformBool_beq (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases b
  · simpa using ProbComp.evalDist_bind_not_uniformBool (fun z => (pure z : ProbComp Bool))
  · simp

private theorem simulateQ_run_query_inr {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (gq : ι)
    (oa : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
    ((impl gq).run st >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa y.1)).run y.2) := by
  simp [simulateQ_bind, StateT.run_bind]

private theorem mem_support_sampleBytes32_len {b : Bytes} (h : b ∈ support sampleBytes32) :
    b.length = 32 := by
  simp only [sampleBytes32, support_map, Set.mem_image] at h
  rcases h with ⟨w, _, rfl⟩
  simp [word256ToBytes]

private theorem mem_support_sampleRandom64_len {r : Bytes} (h : r ∈ support sampleRandom64) :
    r.length = 64 := by
  simp only [sampleRandom64, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
  rcases h with ⟨b1, hb1, b2, hb2, rfl⟩
  simp [mem_support_sampleBytes32_len hb1, mem_support_sampleBytes32_len hb2]

private theorem mem_support_sampleKemKeyGen_pk_len {P : Primitives}
    (hKg : ∀ seed, seed.length = 64 → (P.kemKeyGen seed).1.length = kyberPkLen)
    {pair : Bytes × Bytes} (h : pair ∈ support (sampleKemKeyGen P)) :
    pair.1.length = kyberPkLen := by
  simp only [sampleKemKeyGen, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h
  rcases h with ⟨seed, hseed, rfl⟩
  exact hKg seed (mem_support_sampleRandom64_len hseed)

private theorem modelPrims_kemEncaps_ct_len (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk r ss ct : Bytes) (h : (modelPrims X W).kemEncaps pk r = some (ss, ct)) :
    ct.length = kyberCtLen := by
  dsimp only [modelPrims, blockLevelPrims] at h
  split at h
  · injection h with hpair; injection hpair with _ hct; subst hct
    simp [vecU8, toU8, List.Vector.toList_length, kyberCtLen]
  · cases h

/-- `KemShCr` adversary returning `pk` unchanged and padded ciphertext `ct ++ [0]`. -/
def shCrPadCtAdv : KemShCrAdv where
  State := Unit
  choosePk := fun pk _ => pure (pk, ())
  findCollision := fun _ _ ct => pure (ct ++ [0])
  q_prim := 0

theorem shCrPadCtAdv_bounded : shCrPadCtAdv.Bounded :=
  ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩

theorem kemShCr_shCrPadCtAdv_of_encaps_len (P : Primitives)
    (hLen : ∀ pk r ss ct, P.kemEncaps pk r = some (ss, ct) → ct.length = kyberCtLen) :
    KemShCr P shCrPadCtAdv = 0 := by
  unfold KemShCr
  have hnot : true ∉ support (kemShCrExp P shCrPadCtAdv) := by
    intro hmem
    simp only [kemShCrExp, shCrPadCtAdv, simulateQ_pure, pure_bind,
      MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨pk, sk⟩, _, r, _, hmem⟩
    cases hEnc : P.kemEncaps pk r with
    | none => simp [hEnc] at hmem
    | some pair =>
      rcases pair with ⟨ss, ct⟩
      have hct : ct.length = kyberCtLen := hLen pk r ss ct hEnc
      simp [hEnc] at hmem
      omega
  rw [prob_true_eq_zero_of_notMem_support hnot]

theorem kemShCr_shCrPadCtAdv_eq_zero (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    KemShCr P shCrPadCtAdv = 0 :=
  kemShCr_shCrPadCtAdv_of_encaps_len P (fun pk r ss ct h => (hWF.kemEncaps_len pk r ss ct h).2)

theorem kemShCr_shCrPadCtAdv_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    KemShCr (modelPrims X W) shCrPadCtAdv = 0 :=
  kemShCr_shCrPadCtAdv_of_encaps_len (modelPrims X W) (modelPrims_kemEncaps_ct_len X W)

/-- `KemShCr` adversary returning padded public key `pk ++ [0]` and `ct` unchanged. -/
def shCrPadPkAdv : KemShCrAdv where
  State := Unit
  choosePk := fun pk _ => pure (pk ++ [0], ())
  findCollision := fun _ _ ct => pure ct
  q_prim := 0

theorem shCrPadPkAdv_bounded : shCrPadPkAdv.Bounded :=
  ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩

theorem kemShCr_shCrPadPkAdv_of_keyGen_len (P : Primitives)
    (hKg : ∀ seed, seed.length = 64 → (P.kemKeyGen seed).1.length = kyberPkLen) :
    KemShCr P shCrPadPkAdv = 0 := by
  unfold KemShCr
  have hnot : true ∉ support (kemShCrExp P shCrPadPkAdv) := by
    intro hmem
    simp only [kemShCrExp, shCrPadPkAdv, simulateQ_pure, pure_bind,
      MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨⟨pk, sk⟩, hpk_mem, r, _, hmem⟩
    have hpk : pk.length = kyberPkLen := mem_support_sampleKemKeyGen_pk_len hKg hpk_mem
    cases hEnc : P.kemEncaps (pk ++ [0]) r with
    | none => simp [hEnc] at hmem
    | some pair =>
      rcases pair with ⟨ss, ct⟩
      simp [hEnc] at hmem
      omega
  rw [prob_true_eq_zero_of_notMem_support hnot]

theorem kemShCr_shCrPadPkAdv_eq_zero (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    KemShCr P shCrPadPkAdv = 0 :=
  kemShCr_shCrPadPkAdv_of_keyGen_len P (fun seed _ => (hWF.kemKeyGen_valid seed).1)

theorem kemShCr_shCrPadPkAdv_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (hKg : ∀ seed, seed.length = 64 → (X.kemKeyGen seed).1.length = kyberPkLen) :
    KemShCr (modelPrims X W) shCrPadPkAdv = 0 :=
  kemShCr_shCrPadPkAdv_of_keyGen_len (modelPrims X W) hKg

/-- Minimal two-party setup in which principal `0` initiates and principal `1` receives without an
OPK. -/
def paddedKeyIndSetup : Setup :=
  { N_id := 2, N_recv := 1, N_opk := 0, N_no_opk := 1, N_send_opk := 0, N_send_no_opk := 1 }

def kiQuery {S : Setup} (q : KeyIndQuery S) :
    OracleComp (unifSpec + keyIndSpec S) KeyIndResponse :=
  liftM (OracleSpec.query (spec := unifSpec + keyIndSpec S) (Sum.inr q))

theorem acceptNoOPK_pad_eq_noneResp (useRo : Bool) (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : KeyIndState S) (hct : hdr.kemCt.length = kyberCtLen) :
    (pqxdhKeyIndImpl useRo S P
      (.acceptNoOPK k j l { hdr with kemCt := hdr.kemCt ++ [0] })).run st =
    pure (.noneResp, st) := by
  unfold pqxdhKeyIndImpl
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_pure]
  · simp only [StateT.run_pure]
  · simp only [StateT.run_pure]
  · cases st.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp only [StateT.run_pure]
    | some kp =>
      rcases kp with ⟨_, kEntry⟩
      cases st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp only [StateT.run_pure]
      | some bp =>
        rcases bp with ⟨_, bEntry⟩
        let accInp0 : AcceptKeysInput := {
          ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
          spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
          opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
          trustedPeer := true,
          replayOk := (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk).1,
          hdr := hdr }
        have hAcc : Model.acceptKeys P
            { ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
              spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
              opkBSk? := none, pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
              trustedPeer := true,
              replayOk := (checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk).1,
              hdr := { hdr with kemCt := hdr.kemCt ++ [0] } } = none :=
          acceptKeys_append_zero_eq_none P accInp0 hct
        dsimp only
        rw [hAcc]
        simp only [StateT.run_pure]

theorem acceptNoOPK_pad_eq_noneResp_1KeyRo (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : KeyIndState S) (hct : hdr.kemCt.length = kyberCtLen) :
    (pqxdhKeyIndImpl1KeyRo S P
      (.acceptNoOPK k j l { hdr with kemCt := hdr.kemCt ++ [0] })).run st =
    pure (.noneResp, st) :=
  acceptNoOPK_pad_eq_noneResp true S P k j l hdr st hct

theorem acceptNoOPK_pad_eq_noneResp_1KeyReal (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : KeyIndState S) (hct : hdr.kemCt.length = kyberCtLen) :
    (pqxdhKeyIndImpl1KeyReal S P
      (.acceptNoOPK k j l { hdr with kemCt := hdr.kemCt ++ [0] })).run st =
    pure (.noneResp, st) :=
  acceptNoOPK_pad_eq_noneResp false S P k j l hdr st hct

/-- `KeyInd` adversary that initiates honestly from principal `0` to `1`, submits `hdr.kemCt ++ [0]`
to `.acceptNoOPK`, attempts to reveal the responder session, and tests the initiator session. -/
def paddedKemCtKeyIndAdv : KeyIndAdversary paddedKeyIndSetup where
  run := do
    let _ ← kiQuery (.initPrin ⟨0, by decide⟩)
    let _ ← kiQuery (.initPrin ⟨1, by decide⟩)
    let bResp ← kiQuery (.genSPK ⟨1, by decide⟩ ⟨0, by decide⟩)
    let .bundleResp bundle := bResp | return false
    let iResp ← kiQuery (.initiateNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩ bundle)
    let .hdrResp hdr := iResp | return false
    let _ ← kiQuery (.acceptNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩
      { hdr with kemCt := hdr.kemCt ++ [0] })
    let revResp ← kiQuery (.revealSessionKey (.recvNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩))
    let testResp ← kiQuery (.testSession (.sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩))
    match revResp, testResp with
    | .drKeyResp dkResp, .drKeyResp dkTest => return (dkResp == dkTest)
    | _, _ => return false

/-- End-of-game freshness predicate shared by `pqxdhKeyInd1KeyExpForHandshake` and
`pqxdhKeyIndExp`. -/
def allTestedCleanKeyInd {S : Setup} (P : Primitives) (st : KeyIndState S) : Bool :=
  st.sessions.all (fun s =>
    !s.tested || isKeyIndInitStillFresh P true st.principals st.spkBundles st.respSessions s) &&
  st.respSessions.all (fun r =>
    !r.tested || isKeyIndRespStillFresh P true st.principals st.spkBundles st.sessions r)

/-- Fixed-bit branch of `pqxdhKeyInd1KeyExpForHandshake`. -/
private noncomputable def keyIndHandshakeBranch (S : Setup) (P : Primitives)
    (ki : QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp))
    (A : KeyIndAdversary S) (secb : Bool) : ProbComp Bool := do
  let initSt := KeyIndState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) + ki
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  if !(allTestedCleanKeyInd P finalSt) then
    $ᵗ Bool
  else
    pure b'

private theorem boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero {S : Setup} (P : Primitives)
    (ki : QueryImpl (keyIndSpec S) (StateT (KeyIndState S) ProbComp))
    (A : KeyIndAdversary S)
    (hSupp : ∀ secb z,
      z ∈ support ((simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (KeyIndState S) ProbComp) + ki)
        A.run).run (KeyIndState.empty S secb)) →
      z.1 = false ∧ allTestedCleanKeyInd P z.2 = true) :
    𝒟[pqxdhKeyInd1KeyExpForHandshake S P ki A].boolBias = 0 := by
  have hExp :
      𝒟[pqxdhKeyInd1KeyExpForHandshake S P ki A] =
      𝒟[do
        let secb ← ($ᵗ Bool : ProbComp Bool)
        let z ← if secb then keyIndHandshakeBranch S P ki A true
                else keyIndHandshakeBranch S P ki A false
        return (secb == z)] := by
    unfold pqxdhKeyInd1KeyExpForHandshake keyIndHandshakeBranch allTestedCleanKeyInd
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun secb _ => ?_
    cases secb <;>
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun ⟨b', finalSt⟩ _ => ?_
      split_ifs
      · exact (evalDist_uniformBool_beq _).symm
      · simp [Bool.beq_comm]
  have hBr : ∀ secb, 𝒟[keyIndHandshakeBranch S P ki A secb] = 𝒟[(pure false : ProbComp Bool)] := by
    intro secb
    apply evalDist_eq_pure_of_support
    intro w hw
    unfold keyIndHandshakeBranch at hw
    rw [MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨⟨b', finalSt⟩, hz, hw⟩
    obtain ⟨hb', hclean⟩ := hSupp secb (b', finalSt) hz
    dsimp only at hb' hclean
    subst hb'
    simp [hclean] at hw
    exact hw
  rw [hExp, evalDist_boolBias_bind_uniformBool, hBr true, hBr false, Measure.boolDist_self]

private theorem findHonestPrincipal_isSome_of_mem (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (u : Nat) (e : PrincipalEntry)
    (hmem : (u, e) ∈ principals) :
    (findHonestPrincipal P principals e.ikAPk).isSome = true := by
  unfold findHonestPrincipal
  rw [List.find?_isSome]
  exact ⟨(u, e), hmem, by simp⟩

private theorem isHonestUncorruptedPeer_isSome_of_all_uncorrupted (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes)
    (hFind : (findHonestPrincipal P principals ikB).isSome = true)
    (hUncorr : ∀ p ∈ principals, p.2.corrupted = false) :
    (isHonestUncorruptedPeer P principals ikB).isSome = true := by
  unfold isHonestUncorruptedPeer
  unfold findHonestPrincipal at hFind ⊢
  cases h : principals.find? (fun (_, entry) => P.pow8 ikB == P.pow8 entry.ikAPk) with
  | none => simp [h] at hFind
  | some ke =>
    have hke_mem : ke ∈ principals := List.mem_of_find?_eq_some h
    have hc : ke.2.corrupted = false := hUncorr ke hke_mem
    simp [hc]

/-- Every run of `paddedKemCtKeyIndAdv` returns `false` with no responder sessions and clean tested
sessions. -/
theorem paddedKemCtKeyIndAdv_support (useRo : Bool) (P : Primitives)
    (ki : QueryImpl (keyIndSpec paddedKeyIndSetup) (StateT (KeyIndState paddedKeyIndSetup) ProbComp))
    (hInit : ∀ (u : Fin paddedKeyIndSetup.N_id) (st : KeyIndState paddedKeyIndSetup) z,
      z ∈ support ((ki (.initPrin u)).run st) →
      z.2.sessions = st.sessions ∧ z.2.respSessions = st.respSessions ∧
      z.2.spkBundles = st.spkBundles ∧
      (∀ p ∈ st.principals, p ∈ z.2.principals) ∧
      (∀ p ∈ z.2.principals, p ∈ st.principals ∨ p.2.corrupted = false) ∧
      (st.principals.all (fun (idx, _) => idx != u.val) = true →
        ∃ e, (u.val, e) ∈ z.2.principals ∧ e.corrupted = false))
    (hOther : ∀ q, (∀ u, q ≠ .initPrin u) → (∀ s, q ≠ .roQuery s) → q ≠ .revealDhSecrets →
      ki q = pqxdhKeyIndImpl useRo paddedKeyIndSetup P q)
    (hEncLen : ∀ pk r ss ct, P.kemEncaps pk r = some (ss, ct) → ct.length = kyberCtLen)
    (secb : Bool) (z : Bool × KeyIndState paddedKeyIndSetup)
    (hz : z ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState paddedKeyIndSetup) ProbComp) + ki)
      paddedKemCtKeyIndAdv.run).run (KeyIndState.empty paddedKeyIndSetup secb))) :
    z.1 = false ∧ z.2.respSessions = [] ∧ allTestedCleanKeyInd P z.2 = true := by
  unfold paddedKemCtKeyIndAdv kiQuery at hz
  rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨_, st1⟩, h1, hz⟩
  obtain ⟨hs1, hr1, _, _, hcorr1, _⟩ :=
    hInit ⟨0, by decide⟩ (KeyIndState.empty paddedKeyIndSetup secb) _ h1
  have h1_uncorr : ∀ p ∈ st1.principals, p.2.corrupted = false := by
    intro p hp; rcases hcorr1 p hp with hp0 | hc
    · simp [KeyIndState.empty] at hp0
    · exact hc
  rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨_, st2⟩, h2, hz⟩
  obtain ⟨hs2, hr2, _, _, hcorr2, _⟩ := hInit ⟨1, by decide⟩ st1 _ h2
  have h2_uncorr : ∀ p ∈ st2.principals, p.2.corrupted = false := by
    intro p hp; rcases hcorr2 p hp with hp1 | hc
    · exact h1_uncorr p hp1
    · exact hc
  have hs2_nil : st2.sessions = [] := by rw [hs2, hs1]; rfl
  have hr2_nil : st2.respSessions = [] := by rw [hr2, hr1]; rfl
  rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨bResp, st3⟩, h3, hz⟩
  cases bResp with
  | bundleResp bundle =>
    have h3_props : st3.sessions = [] ∧ st3.respSessions = [] ∧ st3.principals = st2.principals ∧
        ∃ bEnt, (1, bEnt) ∈ st3.principals ∧ bundle.ikB = bEnt.ikAPk := by
      unfold pqxdhKeyIndImpl at h3
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h3
      split_ifs at h3
      · simp at h3
      · cases hfind : st2.principals.find? (fun (idx, _) => idx == 1) with
        | none => simp [hfind] at h3
        | some kp =>
          rcases kp with ⟨idx, uEnt⟩
          have hmem : (idx, uEnt) ∈ st2.principals := List.mem_of_find?_eq_some hfind
          have hidx : idx = 1 := by
            have := List.find?_some hfind; simpa using this
          subst hidx
          simp only [hfind, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
            pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h3
          rcases h3 with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, h3⟩
          have hb_eq := congrArg Prod.fst h3
          have hst3 := congrArg Prod.snd h3
          injection hb_eq with hb_eq; subst hb_eq; subst hst3
          exact ⟨hs2_nil, hr2_nil, rfl, uEnt, hmem, rfl⟩
    obtain ⟨hs3_nil, hr3_nil, hp3_eq, bEnt, hbEnt_mem, hbundle_ikB⟩ := h3_props
    have h3_uncorr : ∀ p ∈ st3.principals, p.2.corrupted = false := by
      rw [hp3_eq]; exact h2_uncorr
    have hFindB : (findHonestPrincipal P st3.principals bundle.ikB).isSome = true := by
      rw [hbundle_ikB]; exact findHonestPrincipal_isSome_of_mem P st3.principals 1 bEnt hbEnt_mem
    have hHonB : (isHonestUncorruptedPeer P st3.principals bundle.ikB).isSome = true :=
      isHonestUncorruptedPeer_isSome_of_all_uncorrupted P st3.principals bundle.ikB hFindB h3_uncorr
    rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨iResp, st4⟩, h4, hz⟩
    cases iResp with
    | hdrResp hdr =>
      have h4_props : hdr.kemCt.length = kyberCtLen ∧ st4.respSessions = [] ∧
          st4.principals = st3.principals ∧
          ∃ sEntry, st4.sessions = [sEntry] ∧
            sEntry.sid = .sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩ ∧
            sEntry.peerIkPk = bundle.ikB ∧ sEntry.fresh = true ∧ sEntry.revealed = false := by
        unfold pqxdhKeyIndImpl at h4
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at h4
        by_cases hopk : bundle.opkB?.isSome = true
        · rw [ite_eq_left hopk] at h4; simp at h4
        · rw [ite_eq_right hopk] at h4
          unfold runKeyIndInitiate at h4
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at h4
          by_cases hany : (st3.sessions.any (fun e => e.sid == .sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩)) = true
          · rw [ite_eq_left hany] at h4; simp at h4
          · rw [ite_eq_right hany] at h4
            cases hfind0 : st3.principals.find? (fun (idx, _) => idx == 0) with
            | none => simp [hfind0] at h4
            | some up =>
              rcases up with ⟨_, uEntry⟩
              simp only [hfind0] at h4
              by_cases hkosk : (!koskBundleOk P st3.principals st3.spkBundles st3.opkEntries st3.advKeys bundle) = true
              · rw [ite_eq_left hkosk] at h4; simp at h4
              · rw [ite_eq_right hkosk] at h4
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind] at h4
                rcases h4 with ⟨ekASk, _, kemCoins, _, h4⟩
                split_ifs at h4
                · simp at h4
                · cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
                  | none => simp [hEnc] at h4
                  | some pair =>
                    rcases pair with ⟨ss, kemCt⟩
                    have hct_len : kemCt.length = kyberCtLen :=
                      hEncLen bundle.pqspkB kemCoins ss kemCt hEnc
                    simp only [hEnc, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
                      pure_bind, MonadAttach.mem_support_bind] at h4
                    rcases h4 with ⟨⟨drKeyReal, roCache'⟩, _, h4⟩
                    cases hFindPeer : findHonestPrincipal P st3.principals bundle.ikB with
                    | none => simp [hFindPeer] at hFindB
                    | some _ =>
                      simp only [hr3_nil, keyIndPartnerRandKey?, List.find?_nil, Option.map_none,
                        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
                        hFindPeer, MonadAttach.mem_support_bind,
                        support_pure, Set.mem_singleton_iff] at h4
                      rcases h4 with ⟨drKeyRand, _, h4⟩
                      have hhdr_eq := congrArg Prod.fst h4
                      have hst4 := congrArg Prod.snd h4
                      injection hhdr_eq with hhdr_eq; subst hhdr_eq; subst hst4
                      exact ⟨hct_len, rfl, rfl, _, by rw [hs3_nil], rfl, rfl, hHonB, rfl⟩
      obtain ⟨hct_len, hr4_nil, hp4_eq, sEntry, hs4_eq, hsid, hpeer, hfresh, hrev⟩ := h4_props
      rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
        acceptNoOPK_pad_eq_noneResp useRo paddedKeyIndSetup P _ _ _ hdr st4 hct_len, pure_bind] at hz
      have hRev : (pqxdhKeyIndImpl useRo paddedKeyIndSetup P
          (.revealSessionKey (.recvNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩))).run st4 =
          pure (.noneResp, st4) := by
        unfold pqxdhKeyIndImpl
        simp [hs4_eq, hr4_nil, hsid]
      rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun), hRev, pure_bind] at hz
      rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨⟨testResp, st6⟩, h6, hz⟩
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      unfold pqxdhKeyIndImpl at h6
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h6
      by_cases hntest : (!isKeyIndSessionTestable st4 (.sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩)) = true
      · rw [ite_eq_left hntest] at h6
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h6
        have hst6 := congrArg Prod.snd h6; subst hst6
        refine ⟨rfl, hr4_nil, ?_⟩
        unfold allTestedCleanKeyInd isKeyIndInitStillFresh keyIndInitCorruptionClause
        rw [hs4_eq, hr4_nil, hp4_eq]
        simp [hpeer, hfresh, hrev, hHonB]
      · rw [ite_eq_right hntest] at h6
        simp only [hs4_eq, hsid, beq_self_eq_true, List.find?_cons_of_pos, List.map_cons,
          List.map_nil, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at h6
        have hst6 := congrArg Prod.snd h6; subst hst6
        refine ⟨rfl, hr4_nil, ?_⟩
        unfold allTestedCleanKeyInd isKeyIndInitStillFresh keyIndInitCorruptionClause
        rw [hr4_nil, hp4_eq]
        simp [hpeer, hfresh, hrev, hHonB]
    | _ =>
      have h4_fail : st4.sessions = [] ∧ st4.respSessions = [] := by
        unfold pqxdhKeyIndImpl at h4
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at h4
        by_cases hopk : bundle.opkB?.isSome = true
        · rw [ite_eq_left hopk] at h4
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
          have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
        · rw [ite_eq_right hopk] at h4
          unfold runKeyIndInitiate at h4
          simp only [StateT.run_bind, StateT.run_get, pure_bind] at h4
          by_cases hany : (st3.sessions.any (fun e => e.sid == .sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩)) = true
          · rw [ite_eq_left hany] at h4
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
            have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
          · rw [ite_eq_right hany] at h4
            cases hfind0 : st3.principals.find? (fun (idx, _) => idx == 0) with
            | none =>
              simp only [hfind0, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
              have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
            | some up =>
              rcases up with ⟨_, uEntry⟩
              simp only [hfind0] at h4
              by_cases hkosk : (!koskBundleOk P st3.principals st3.spkBundles st3.opkEntries st3.advKeys bundle) = true
              · rw [ite_eq_left hkosk] at h4
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
                have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
              · rw [ite_eq_right hkosk] at h4
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind] at h4
                rcases h4 with ⟨_, _, kemCoins, _, h4⟩
                split_ifs at h4
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
                  have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
                · cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
                  | none =>
                    simp only [hEnc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
                    have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
                  | some pair =>
                    rcases pair with ⟨ss, kemCt⟩
                    simp only [hEnc, StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc,
                      pure_bind, MonadAttach.mem_support_bind] at h4
                    rcases h4 with ⟨_, _, h4⟩
                    cases hFindPeer : findHonestPrincipal P st3.principals bundle.ikB with
                    | none => simp [hFindPeer] at hFindB
                    | some _ =>
                      simp only [hr3_nil, keyIndPartnerRandKey?, List.find?_nil, Option.map_none,
                        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
                        hFindPeer, MonadAttach.mem_support_bind,
                        support_pure, Set.mem_singleton_iff] at h4
                      rcases h4 with ⟨_, _, h4⟩
                      have hfalse := congrArg Prod.fst h4
                      cases hfalse
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [allTestedCleanKeyInd, h4_fail.1, h4_fail.2]
  | _ =>
    have h3_fail : st3.sessions = [] ∧ st3.respSessions = [] := by
      unfold pqxdhKeyIndImpl at h3
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h3
      split_ifs at h3
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h3
        have hst3 := congrArg Prod.snd h3; subst hst3; exact ⟨hs2_nil, hr2_nil⟩
      · cases hfind : st2.principals.find? (fun (idx, _) => idx == 1) with
        | none =>
          simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h3
          have hst3 := congrArg Prod.snd h3; subst hst3; exact ⟨hs2_nil, hr2_nil⟩
        | some kp =>
          rcases kp with ⟨_, uEnt⟩
          simp only [hfind, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
            pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h3
          rcases h3 with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, h3⟩
          have hfalse := congrArg Prod.fst h3
          cases hfalse
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [allTestedCleanKeyInd, h3_fail.1, h3_fail.2]

private theorem initPrin_1Key_props (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) (z : KeyIndResponse × KeyIndState S)
    (hz : z ∈ support ((pqxdhKeyIndImpl1KeyReal S P (.initPrin u)).run st)) :
    z.2.sessions = st.sessions ∧ z.2.respSessions = st.respSessions ∧
    z.2.spkBundles = st.spkBundles ∧
    (∀ p ∈ st.principals, p ∈ z.2.principals) ∧
    (∀ p ∈ z.2.principals, p ∈ st.principals ∨ p.2.corrupted = false) ∧
    (st.principals.all (fun (idx, _) => idx != u.val) = true →
      ∃ e, (u.val, e) ∈ z.2.principals ∧ e.corrupted = false) := by
  unfold pqxdhKeyIndImpl1KeyReal at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hany
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, rfl⟩
    refine ⟨rfl, rfl, rfl, fun _ h => h, fun _ h => Or.inl h, fun hall => ?_⟩
    exfalso
    rw [List.any_eq_true] at hany
    rcases hany with ⟨⟨idx, e⟩, hmem, hbeq⟩
    have hne := List.all_eq_true.mp hall (idx, e) hmem
    simp [beq_iff_eq] at hbeq hne
    exact hne hbeq
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨secIKA0, _, _, rfl⟩
    refine ⟨rfl, rfl, rfl, fun p hp => List.mem_cons_of_mem _ hp, ?_, fun _ => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact Or.inr rfl
      · exact Or.inl hp'
    · exact ⟨_, List.mem_cons_self, rfl⟩

private theorem initPrin_2Key_props (useRo : Bool) (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) (z : KeyIndResponse × KeyIndState S)
    (hz : z ∈ support ((pqxdhKeyIndImpl useRo S P (.initPrin u)).run st)) :
    z.2.sessions = st.sessions ∧ z.2.respSessions = st.respSessions ∧
    z.2.spkBundles = st.spkBundles ∧
    (∀ p ∈ st.principals, p ∈ z.2.principals) ∧
    (∀ p ∈ z.2.principals, p ∈ st.principals ∨ p.2.corrupted = false) ∧
    (st.principals.all (fun (idx, _) => idx != u.val) = true →
      ∃ e, (u.val, e) ∈ z.2.principals ∧ e.corrupted = false) := by
  unfold pqxdhKeyIndImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with hany
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, rfl⟩
    refine ⟨rfl, rfl, rfl, fun _ h => h, fun _ h => Or.inl h, fun hall => ?_⟩
    exfalso
    rw [List.any_eq_true] at hany
    rcases hany with ⟨⟨idx, e⟩, hmem, hbeq⟩
    have hne := List.all_eq_true.mp hall (idx, e) hmem
    simp [beq_iff_eq] at hbeq hne
    exact hne hbeq
  · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
    rcases hz with ⟨secIKA0, _, secIKAsign, _, _, rfl⟩
    refine ⟨rfl, rfl, rfl, fun p hp => List.mem_cons_of_mem _ hp, ?_, fun _ => ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact Or.inr rfl
      · exact Or.inl hp'
    · exact ⟨_, List.mem_cons_self, rfl⟩

theorem keyInd1KeyRoAdvantage_paddedKemCt_of_encaps_len (P : Primitives)
    (hEncLen : ∀ pk r ss ct, P.kemEncaps pk r = some (ss, ct) → ct.length = kyberCtLen) :
    KeyInd1KeyRoAdvantage paddedKeyIndSetup P paddedKemCtKeyIndAdv = 0 := by
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedKemCtKeyIndAdv_support true P
    (pqxdhKeyIndImpl1KeyRo paddedKeyIndSetup P)
    (initPrin_1Key_props paddedKeyIndSetup P)
    (fun q hq _ _ => by cases q with | initPrin u => exact absurd rfl (hq u) | _ => rfl)
    hEncLen secb z hz
  exact ⟨h.1, h.2.2⟩

theorem keyInd1KeyRealAdvantage_paddedKemCt_of_encaps_len (P : Primitives)
    (hEncLen : ∀ pk r ss ct, P.kemEncaps pk r = some (ss, ct) → ct.length = kyberCtLen) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup P paddedKemCtKeyIndAdv = 0 := by
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedKemCtKeyIndAdv_support false P
    (pqxdhKeyIndImpl1KeyReal paddedKeyIndSetup P)
    (initPrin_1Key_props paddedKeyIndSetup P)
    (fun q h1 h2 h3 => by
      cases q with
      | initPrin u => exact absurd rfl (h1 u)
      | roQuery s => exact absurd rfl (h2 s)
      | revealDhSecrets => exact absurd rfl h3
      | _ => rfl)
    hEncLen secb z hz
  exact ⟨h.1, h.2.2⟩

theorem keyIndAdvantage_paddedKemCt (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    KeyIndAdvantage paddedKeyIndSetup P paddedKemCtKeyIndAdv = 0 := by
  change (𝒟[pqxdhKeyInd1KeyExpForHandshake paddedKeyIndSetup P
    (pqxdhKeyIndImpl true paddedKeyIndSetup P) paddedKemCtKeyIndAdv].boolBias).toReal = 0
  suffices h0 : 𝒟[pqxdhKeyInd1KeyExpForHandshake paddedKeyIndSetup P
      (pqxdhKeyIndImpl true paddedKeyIndSetup P) paddedKemCtKeyIndAdv].boolBias = 0 by
    rw [h0, ENNReal.toReal_zero]
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedKemCtKeyIndAdv_support true P
    (pqxdhKeyIndImpl true paddedKeyIndSetup P)
    (initPrin_2Key_props true paddedKeyIndSetup P)
    (fun _ _ _ _ => rfl)
    (fun pk r ss ct h => (hWF.kemEncaps_len pk r ss ct h).2) secb z hz
  exact ⟨h.1, h.2.2⟩

theorem keyInd1KeyRoAdvantage_paddedKemCt (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    KeyInd1KeyRoAdvantage paddedKeyIndSetup P paddedKemCtKeyIndAdv = 0 :=
  keyInd1KeyRoAdvantage_paddedKemCt_of_encaps_len P
    (fun pk r ss ct h => (hWF.kemEncaps_len pk r ss ct h).2)

theorem keyInd1KeyRealAdvantage_paddedKemCt (P : Primitives) (hWF : WellFormedPrimitivesδ P) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup P paddedKemCtKeyIndAdv = 0 :=
  keyInd1KeyRealAdvantage_paddedKemCt_of_encaps_len P
    (fun pk r ss ct h => (hWF.kemEncaps_len pk r ss ct h).2)

theorem keyInd1KeyRoAdvantage_paddedKemCt_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    KeyInd1KeyRoAdvantage paddedKeyIndSetup (modelPrims X W) paddedKemCtKeyIndAdv = 0 :=
  keyInd1KeyRoAdvantage_paddedKemCt_of_encaps_len (modelPrims X W) (modelPrims_kemEncaps_ct_len X W)

theorem keyInd1KeyRealAdvantage_paddedKemCt_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup (modelPrims X W) paddedKemCtKeyIndAdv = 0 :=
  keyInd1KeyRealAdvantage_paddedKemCt_of_encaps_len (modelPrims X W) (modelPrims_kemEncaps_ct_len X W)

theorem initiateNoOPK_bad_pqspk_support (useRo : Bool) (S : Setup) (P : Primitives)
    (hEncRej : ∀ pk r, pk.length ≠ kyberPkLen → P.kemEncaps pk r = none)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hbad : bundle.pqspkB.length ≠ kyberPkLen) (st : KeyIndState S)
    (z : KeyIndResponse × KeyIndState S)
    (hz : z ∈ support ((pqxdhKeyIndImpl useRo S P (.initiateNoOPK u i bundle)).run st)) :
    z = (.noneResp, st) := by
  unfold pqxdhKeyIndImpl at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases hopk : bundle.opkB?.isSome = true
  · rw [ite_eq_left hopk] at hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz
  · rw [ite_eq_right hopk] at hz
    unfold runKeyIndInitiate at hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
    by_cases hany : (st.sessions.any (fun e => e.sid == .sendNoOPK u i)) = true
    · rw [ite_eq_left hany] at hz
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz
    · rw [ite_eq_right hany] at hz
      cases hfind : st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz
      | some up =>
        rcases up with ⟨_, uEntry⟩
        simp only [hfind] at hz
        by_cases hkosk : (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = true
        · rw [ite_eq_left hkosk] at hz
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz
        · rw [ite_eq_right hkosk] at hz
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hz
          rcases hz with ⟨_, _, kemCoins, _, hz⟩
          split_ifs at hz
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz
          · rw [hEncRej bundle.pqspkB kemCoins hbad] at hz
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz; exact hz

theorem initiateNoOPK_pad_pqspk_support (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hpk : bundle.pqspkB.length = kyberPkLen) (sig : Bytes) (st : KeyIndState S)
    (z : KeyIndResponse × KeyIndState S)
    (hz : z ∈ support ((pqxdhKeyIndImpl useRo S P
      (.initiateNoOPK u i { bundle with pqspkB := bundle.pqspkB ++ [0], pqspkSig := sig })).run st)) :
    z.1 = .noneResp ∧ z.2.sessions = st.sessions := by
  have hbad : (bundle.pqspkB ++ [0]).length ≠ kyberPkLen := by simp [hpk]
  have h := initiateNoOPK_bad_pqspk_support useRo S P hP.kemEncaps_len_reject u i
    { bundle with pqspkB := bundle.pqspkB ++ [0], pqspkSig := sig } hbad st z hz
  rw [h]
  exact ⟨rfl, rfl⟩

/-- KCI `KeyInd` adversary that corrupts principal `1` to re-sign `bundle.pqspkB ++ [0]`, submits
`.initiateNoOPK` from principal `0` on the padded bundle, and tests the responder if initiation
succeeds. -/
def paddedPqspkKciKeyIndAdv (P : Primitives) : KeyIndAdversary paddedKeyIndSetup where
  run := do
    let _ ← kiQuery (.initPrin ⟨0, by decide⟩)
    let _ ← kiQuery (.initPrin ⟨1, by decide⟩)
    let bResp ← kiQuery (.genSPK ⟨1, by decide⟩ ⟨0, by decide⟩)
    let .bundleResp bundle := bResp | return false
    let cResp ← kiQuery (.corruptIK ⟨1, by decide⟩)
    let .corrResp _ sigSkB := cResp | return false
    let sigPad := P.sigSign sigSkB (encodeKEM (bundle.pqspkB ++ [0])) (List.replicate 64 0)
    let bundlePad : PreKeyBundleInput :=
      { bundle with pqspkB := bundle.pqspkB ++ [0], pqspkSig := sigPad }
    let iResp ← kiQuery (.initiateNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩ bundlePad)
    let (dkInit, hdr) ← match iResp with
      | .initUnfreshResp dk hdr => pure (dk, hdr)
      | .hdrResp hdr =>
        let revResp ← kiQuery (.revealSessionKey (.sendNoOPK ⟨0, by decide⟩ ⟨0, by decide⟩))
        let .drKeyResp dk := revResp | return false
        pure (dk, hdr)
      | _ => return false
    let _ ← kiQuery (.acceptNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ hdr)
    let testResp ← kiQuery (.testSession (.recvNoOPK ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩))
    match testResp with
    | .drKeyResp dkTest => return (dkInit == dkTest)
    | _ => return false

private theorem paddedPqspkKciKeyIndAdv_support (useRo : Bool) (P : Primitives)
    (ki : QueryImpl (keyIndSpec paddedKeyIndSetup) (StateT (KeyIndState paddedKeyIndSetup) ProbComp))
    (hInit : ∀ (u : Fin paddedKeyIndSetup.N_id) (st : KeyIndState paddedKeyIndSetup) z,
      z ∈ support ((ki (.initPrin u)).run st) →
      z.2.sessions = st.sessions ∧ z.2.respSessions = st.respSessions)
    (hOther : ∀ q, (∀ u, q ≠ .initPrin u) → (∀ s, q ≠ .roQuery s) → q ≠ .revealDhSecrets →
      ki q = pqxdhKeyIndImpl useRo paddedKeyIndSetup P q)
    (hKg : ∀ seed, seed.length = 64 → (P.kemKeyGen seed).1.length = kyberPkLen)
    (hEncRej : ∀ pk r, pk.length ≠ kyberPkLen → P.kemEncaps pk r = none)
    (secb : Bool) (z : Bool × KeyIndState paddedKeyIndSetup)
    (hz : z ∈ support ((simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState paddedKeyIndSetup) ProbComp) + ki)
      (paddedPqspkKciKeyIndAdv P).run).run (KeyIndState.empty paddedKeyIndSetup secb))) :
    z.1 = false ∧ z.2.sessions = [] ∧ z.2.respSessions = [] ∧ allTestedCleanKeyInd P z.2 = true := by
  unfold paddedPqspkKciKeyIndAdv kiQuery at hz
  rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨_, st1⟩, h1, hz⟩
  obtain ⟨hs1, hr1⟩ := hInit ⟨0, by decide⟩ (KeyIndState.empty paddedKeyIndSetup secb) _ h1
  rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨_, st2⟩, h2, hz⟩
  obtain ⟨hs2, hr2⟩ := hInit ⟨1, by decide⟩ st1 _ h2
  have hs2_nil : st2.sessions = [] := by rw [hs2, hs1]; rfl
  have hr2_nil : st2.respSessions = [] := by rw [hr2, hr1]; rfl
  rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
    MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨⟨bResp, st3⟩, h3, hz⟩
  cases bResp with
  | bundleResp bundle =>
    have h3_props : st3.sessions = [] ∧ st3.respSessions = [] ∧ bundle.pqspkB.length = kyberPkLen := by
      unfold pqxdhKeyIndImpl at h3
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h3
      split_ifs at h3
      · simp at h3
      · cases hfind : st2.principals.find? (fun (idx, _) => idx == 1) with
        | none => simp [hfind] at h3
        | some kp =>
          rcases kp with ⟨_, uEnt⟩
          simp only [hfind, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
            pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h3
          rcases h3 with ⟨_, _, _, _, ⟨pqspkPk, pqspkSk⟩, hpq, _, _, h3⟩
          have hpq_len : pqspkPk.length = kyberPkLen := mem_support_sampleKemKeyGen_pk_len hKg hpq
          have hb_eq := congrArg Prod.fst h3
          have hst3 := congrArg Prod.snd h3
          injection hb_eq with hb_eq; subst hb_eq; subst hst3
          exact ⟨hs2_nil, hr2_nil, hpq_len⟩
    obtain ⟨hs3_nil, hr3_nil, hpq_len⟩ := h3_props
    rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
      MonadAttach.mem_support_bind] at hz
    rcases hz with ⟨⟨cResp, st4⟩, h4, hz⟩
    have h4_nil : st4.sessions = [] ∧ st4.respSessions = [] := by
      unfold pqxdhKeyIndImpl at h4
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h4
      cases hfindc : st3.principals.find? (fun (idx, _) => idx == 1) with
      | none =>
        simp only [hfindc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h4
        have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
      | some cp =>
        rcases cp with ⟨_, _⟩
        simp only [hfindc, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at h4
        have hst4 := congrArg Prod.snd h4; subst hst4; exact ⟨hs3_nil, hr3_nil⟩
    cases cResp with
    | corrResp ikSk sigSkB =>
      rw [simulateQ_run_query_inr, hOther _ (by intro u; exact nofun) (by intro s; exact nofun) (by exact nofun),
        MonadAttach.mem_support_bind] at hz
      rcases hz with ⟨⟨iResp, st5⟩, h5, hz⟩
      have hbad : (bundle.pqspkB ++ [0]).length ≠ kyberPkLen := by simp [hpq_len]
      have h5_eq := initiateNoOPK_bad_pqspk_support useRo paddedKeyIndSetup P hEncRej
        ⟨0, by decide⟩ ⟨0, by decide⟩ _ hbad st4 (iResp, st5) h5
      injection h5_eq with hiResp hst5; subst hiResp; subst hst5
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [allTestedCleanKeyInd, h4_nil.1, h4_nil.2]
    | _ =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [allTestedCleanKeyInd, h4_nil.1, h4_nil.2]
  | _ =>
    have h3_nil : st3.sessions = [] ∧ st3.respSessions = [] := by
      unfold pqxdhKeyIndImpl at h3
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at h3
      split_ifs at h3
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at h3
        have hst3 := congrArg Prod.snd h3; subst hst3; exact ⟨hs2_nil, hr2_nil⟩
      · cases hfind : st2.principals.find? (fun (idx, _) => idx == 1) with
        | none =>
          simp only [hfind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at h3
          have hst3 := congrArg Prod.snd h3; subst hst3; exact ⟨hs2_nil, hr2_nil⟩
        | some kp =>
          rcases kp with ⟨_, _⟩
          simp only [hfind, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
            pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at h3
          rcases h3 with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, h3⟩
          have hfalse := congrArg Prod.fst h3
          cases hfalse
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [allTestedCleanKeyInd, h3_nil.1, h3_nil.2]

theorem keyInd1KeyRoAdvantage_paddedPqspkKci (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) :
    KeyInd1KeyRoAdvantage paddedKeyIndSetup P (paddedPqspkKciKeyIndAdv P) = 0 := by
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedPqspkKciKeyIndAdv_support true P
    (pqxdhKeyIndImpl1KeyRo paddedKeyIndSetup P)
    (fun u st w hw =>
      let hp := initPrin_1Key_props paddedKeyIndSetup P u st w hw
      ⟨hp.1, hp.2.1⟩)
    (fun q hq _ _ => by cases q with | initPrin u => exact absurd rfl (hq u) | _ => rfl)
    (fun seed _ => (hP.kemKeyGen_valid seed).1)
    hP.kemEncaps_len_reject secb z hz
  exact ⟨h.1, h.2.2.2⟩

theorem keyInd1KeyRealAdvantage_paddedPqspkKci_of_laws (P : Primitives)
    (hKg : ∀ seed, seed.length = 64 → (P.kemKeyGen seed).1.length = kyberPkLen)
    (hEncRej : ∀ pk r, pk.length ≠ kyberPkLen → P.kemEncaps pk r = none) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup P (paddedPqspkKciKeyIndAdv P) = 0 := by
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedPqspkKciKeyIndAdv_support false P
    (pqxdhKeyIndImpl1KeyReal paddedKeyIndSetup P)
    (fun u st w hw =>
      let hp := initPrin_1Key_props paddedKeyIndSetup P u st w hw
      ⟨hp.1, hp.2.1⟩)
    (fun q h1 h2 h3 => by
      cases q with
      | initPrin u => exact absurd rfl (h1 u)
      | roQuery s => exact absurd rfl (h2 s)
      | revealDhSecrets => exact absurd rfl h3
      | _ => rfl)
    hKg hEncRej secb z hz
  exact ⟨h.1, h.2.2.2⟩

theorem keyInd1KeyRealAdvantage_paddedPqspkKci (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup P (paddedPqspkKciKeyIndAdv P) = 0 :=
  keyInd1KeyRealAdvantage_paddedPqspkKci_of_laws P
    (fun seed _ => (hP.kemKeyGen_valid seed).1) hP.kemEncaps_len_reject

theorem keyIndAdvantage_paddedPqspkKci (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) :
    KeyIndAdvantage paddedKeyIndSetup P (paddedPqspkKciKeyIndAdv P) = 0 := by
  change (𝒟[pqxdhKeyInd1KeyExpForHandshake paddedKeyIndSetup P
    (pqxdhKeyIndImpl true paddedKeyIndSetup P) (paddedPqspkKciKeyIndAdv P)].boolBias).toReal = 0
  suffices h0 : 𝒟[pqxdhKeyInd1KeyExpForHandshake paddedKeyIndSetup P
      (pqxdhKeyIndImpl true paddedKeyIndSetup P) (paddedPqspkKciKeyIndAdv P)].boolBias = 0 by
    rw [h0, ENNReal.toReal_zero]
  apply boolBias_pqxdhKeyInd1KeyExpForHandshake_eq_zero
  intro secb z hz
  have h := paddedPqspkKciKeyIndAdv_support true P
    (pqxdhKeyIndImpl true paddedKeyIndSetup P)
    (fun u st w hw =>
      let hp := initPrin_2Key_props true paddedKeyIndSetup P u st w hw
      ⟨hp.1, hp.2.1⟩)
    (fun _ _ _ _ => rfl)
    (fun seed _ => (hP.kemKeyGen_valid seed).1)
    hP.kemEncaps_len_reject secb z hz
  exact ⟨h.1, h.2.2.2⟩

theorem keyInd1KeyRealAdvantage_paddedPqspkKci_modelPrims (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (hKg : ∀ seed, seed.length = 64 → (X.kemKeyGen seed).1.length = kyberPkLen) :
    KeyInd1KeyRealAdvantage paddedKeyIndSetup (modelPrims X W)
      (paddedPqspkKciKeyIndAdv (modelPrims X W)) = 0 :=
  keyInd1KeyRealAdvantage_paddedPqspkKci_of_laws (modelPrims X W) hKg
    (fun pk r hpk => by simp [modelPrims, blockLevelPrims, hpk])

end SignalPqxdh.Guards
