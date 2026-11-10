/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.TightSize

/-!
# Tight Envelopes, Domain Bundles, and Branch Specs for `spqr::recv`

Defines tight `fineCostModel` budget constants, the CLI `recv` peer-validity bridge
(`cliRecv_peerSpqrTightValid640`), parametric codec / `<States>::recv` / domain hypothesis bundles
(`C07TightCreditSpec`, `StatesRecvTightCreditSpec`, `SpqrRecvTightDomain`), tight `spqr::recv`
envelopes, and `PhaseCreditSpec` bounds for `Ordering::Less`, `Ordering::Greater`, and
`V1ChainAndEncodeTightEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainEpoch ChainEpochDirection ChainEpochPB ChainPB Direction EpochSecret HkdfFn
   Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB chainFrom
   chainFromVersionNegotiation spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Proto (spqrDecodeState)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.KitInst (cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize
  (optRaw rawChain rawPqState rawV1State rawVN)
open CryptoVerification.SpqrV1Sync.SendTotal (RecvSmallTight)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (DecodeStateBoundedEnv DecodeStateTightEnv StatesFromPbBoundedEnv StatesFromPbTightEnv
   decodeState_fine_phaseCreditSpec_tight statesFromPb_fine_phaseCreditSpec_tight
   statesIntoPb_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds (pqRatchetStateEncodeToVec_len_le)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakSpec
  (OptChainAddEpochEnv SpqrRecvGreaterCallEnv SpqrRecvLessCallEnv SpqrRecvPartsEnv V0ChainInitEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
  (chainAddEpoch_fine_phaseCreditSpec_4 chainFrom_fine_phaseCreditSpec
   chainIntoPb_fine_phaseCreditSpec_4 chainNew_fine_phaseCreditSpec chainRecvKey_links_length_eq
   initInner_fine_phaseCreditSpec_32 pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
   statesIntoPb_fine_phaseCreditSpec_49856)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey
  (KeyHistorySmallOrReserved chainRecvKey_fine_phaseCreditSpec_tight
   chainRecvKey_fine_phaseCreditSpec_tight_smallHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidChainParamsPB ValidEncoderPts640 peerSpqrTightValid640_of_cliPqInputs_recv
   peerSpqrTightValidAt_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt ValidV1PtsAt)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (ChainRecvKeyEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (ChainFromEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (StatesIntoPbEnv)

/-! ## Tight Budget Constants -/

/-- Cumulative small-allocation ceiling for tight `spqr::recv` (`23,313,687` bytes). -/
def spqrRecvTightCumCap : Nat := 23313687

/-- Live/peak large-allocation ceiling under `KeyHistorySmallOrReserved` (`294,391` bytes). -/
def spqrRecvTightLiveCap : Nat := 294391

/-- Unconditional-`xRk.G` live large-allocation ceiling (`605,066` bytes). -/
def spqrRecvTightUncondLiveCap : Nat := 605066

/-- Unconditional-`xRk.G` peak large-allocation ceiling (`621,350` bytes). -/
def spqrRecvTightUncondPeakCap : Nat := 621350

def c07TightDecodeCum : Nat := 939633

def c07TightFromPbCum : Nat := 155757

def c07TightIntoPbCum : Nat := 164351

/-- Cumulative small-allocation budget for `DecodeStateTightEnv` (`1,307,216` bytes). -/
def c07ActualDecodeCum : Nat := 1307216

/-- Cumulative small-allocation budget for `StatesFromPbTightEnv` (`359,623` bytes). -/
def c07ActualFromPbCum : Nat := 359623

/-- Cumulative small-allocation budget for `StatesIntoPbTightEnv` (`376,193` bytes). -/
def c07ActualIntoPbCum : Nat := 376193

def c07ActualCodecSum : Nat := 2043032

/-- Cumulative small-allocation budget for `<States>::recv` when `k ≥ 2` (`1,647,247` bytes). -/
def c09aTightStatesRecvCum : Nat := 1647247

/-- Cumulative small-allocation budget for `<States>::recv` across arbitrary `k` (`5,335,951` bytes).
-/
def c09aTightStatesRecvAnyKCum : Nat := 5335951

theorem phaseCreditSpec_of_false_fine {Env : List AllocEvent → Prop} (c l p r : Nat)
    (hf : ∀ evs, ¬ Env evs) :
    PhaseCreditSpec fineCostModel Env c l p r :=
  (PhaseCreditSpec.of_eq_nil (M := fineCostModel) fun evs h => False.elim (hf evs h)).mono
    (Nat.zero_le c) (Nat.zero_le l) (Nat.zero_le p) (Nat.zero_le r)

theorem phaseCreditSpec_or_freeOnly_fine {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => FreeOnlyEvs evs ∨ E evs) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le c, Nat.le_refl c⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le l, Nat.le_refl l⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le p, Nat.le_refl p⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le r, Nat.le_refl r⟩)

theorem phaseCreditSpec_seq_freeOnly_left_fine {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (SeqEnv FreeOnlyEvs E) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).seq h).mono
    (by simp) (by simp) (by simp) (Nat.max_le.mpr ⟨Nat.zero_le r, Nat.le_refl r⟩)

theorem phaseCreditSpec_seq_freeOnly_right_fine {E : List AllocEvent → Prop} {c l p r : Nat}
    (hlp : l ≤ p) (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (SeqEnv E FreeOnlyEvs) c l p r :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by simp) (by simp) (Nat.max_le.mpr ⟨Nat.le_refl p, by simpa using hlp⟩)
    (Nat.max_le.mpr ⟨Nat.le_refl r, Nat.zero_le r⟩)

theorem phaseCreditSpec_seq_zero_left_fine {E₁ E₂ : List AllocEvent → Prop}
    {c₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 0 0 r₁)
    (h₂ : PhaseCreditSpec fineCostModel E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec fineCostModel (SeqEnv E₁ E₂) (c₁ + c₂) l₂ p₂ (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (by simp) (by simp) (Nat.le_refl _)

/-! ## CLI `recv` Validity Bridge and `chainFrom` Link-Count Helpers -/

/-- Extracts `ValidEncoderPts640 stBytes ∧ ValidChainParams stBytes` (and `stBytes.length < 2 ^ 31`) from `CliPqxdhInputs` and `cliSessionStoreSpec.ScopeAt`.
-/
theorem cliRecv_peerSpqrTightValid640
    {W : PEParams} {i : Inputs} {peer : AddrV}
    {A : RustAlloc} {b : BitVec 64} {pathOk : List (BitVec 8) → Prop} {peerG : AddrGhost}
    {s1 s2 s3 s4 : Nat} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {stBytes : Bytes}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hScAt : (cliSessionStoreSpec A b cliIo.rd (runFiles i) pathOk scopeKit peerG s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions (addrValOf peer) r)
    (hcur : r.currentSession = some sess)
    (hpqr : stBytes = sess.state.pqRatchetState) :
    ValidEncoderPts640 stBytes ∧ ValidChainParams stBytes ∧ stBytes.length < 2 ^ 31 :=
  peerSpqrTightValidAt_of_cliSessionStoreSpec hScAt hcur hpqr
    (peerSpqrTightValid640_of_cliPqInputs_recv hi hparse)

private theorem linksFromPb_length :
    ∀ (pbs : List ChainEpochPB) (ls : List ChainEpoch),
      Chain.linksFromPb pbs = .ok ls → ls.length = pbs.length
  | [], ls, h => by
    simp only [Chain.linksFromPb, Except.ok.injEq] at h
    subst h; rfl
  | link :: rest, ls, h => by
    unfold Chain.linksFromPb at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hs : link.send with
    | none => rw [hs] at h; contradiction
    | some sendPb =>
      rw [hs] at h; dsimp only at h
      cases hsd : ChainEpochDirection.fromPb sendPb with
      | error _ => rw [hsd] at h; contradiction
      | ok send =>
        rw [hsd] at h; dsimp only at h
        cases hr : link.recv with
        | none => rw [hr] at h; contradiction
        | some recvPb =>
          rw [hr] at h; dsimp only at h
          cases hrd : ChainEpochDirection.fromPb recvPb with
          | error _ => rw [hrd] at h; contradiction
          | ok recv =>
            rw [hrd] at h; dsimp only at h
            cases htl : Chain.linksFromPb rest with
            | error _ => rw [htl] at h; contradiction
            | ok tail =>
              rw [htl] at h; dsimp only at h
              have heq := Except.ok.inj h; subst heq
              simp [linksFromPb_length rest tail htl]

theorem chainFrom_links_length_le_4 {hkdf : HkdfFn} {pb? : Option ChainPB}
    {vn? : Option VersionNegotiationPB} {c : Chain}
    (hpb : ∀ pb, pb? = some pb → pb.links.length ≤ 4)
    (h : chainFrom hkdf pb? vn? = .ok c) :
    c.links.length ≤ 4 := by
  unfold chainFrom at h
  cases pb? with
  | some pb =>
    unfold Chain.fromPb at h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hd : Direction.fromI32? pb.direction with
    | none => rw [hd] at h; contradiction
    | some d =>
      rw [hd] at h; dsimp only at h
      cases hl : Chain.linksFromPb pb.links with
      | error _ => rw [hl] at h; contradiction
      | ok links =>
        rw [hl] at h; dsimp only at h
        cases hp : pb.params with
        | none => rw [hp] at h; contradiction
        | some p =>
          rw [hp] at h; dsimp only at h
          have hc := Except.ok.inj h; subst hc
          dsimp only
          rw [linksFromPb_length pb.links links hl]
          exact hpb pb rfl
  | none =>
    cases vn? with
    | none => contradiction
    | some vn =>
      unfold chainFromVersionNegotiation at h
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases hd : Direction.fromI32? vn.direction with
      | none => rw [hd] at h; contradiction
      | some d =>
        rw [hd] at h; dsimp only at h
        cases hp : vn.chainParams with
        | none => rw [hp] at h; contradiction
        | some p =>
          rw [hp] at h; dsimp only at h
          unfold Chain.new at h
          have hc := Except.ok.inj h; subst hc
          simp only [List.length]; decide

/-! ## Codec, `<States>::recv`, and Domain Hypothesis Bundles -/

/-- Small-class (`sc < 48`, `Δlive = Δpeak = 0`) `fineCostModel` `PhaseCreditSpec` bundle for `spqr::decode_state`, `<States>::from_pb`, and `<States>::into_pb`.
-/
structure C07TightCreditSpec (F : ShaCompress)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (cDec rDec cFrom rFrom cInto rInto : Nat) : Prop where
  decode_spec :
    ∀ stBytes : Bytes,
      stBytes.length ≤ spqrStateTightCapBytes →
      ValidEncoderPts640 stBytes →
      ValidChainParams stBytes →
      PhaseCreditSpec fineCostModel (DecodeStateEnv stBytes) cDec 0 0 rDec
  fromPb_spec :
    ∀ pb : V1State,
      ValidV1PtsAt 640 pb →
      rawV1State pb ≤ 46880 →
      PhaseCreditSpec fineCostModel (StatesFromPbEnv pb) cFrom 0 0 rFrom
  intoPb_spec :
    ∀ xSInto : StatesIntoPbGhost F,
      StatesPtsBoundedAt 640 xSInto.st →
      ValidV1PtsAt 640 xSInto.st.into_pb →
      rawV1State xSInto.st.into_pb ≤ 49856 →
      PhaseCreditSpec fineCostModel (StatesIntoPbEnv' xSInto) cInto 0 0 rInto

/-- Constructs `C07TightCreditSpec` using the fallback `statesIntoPb_fine_phaseCreditSpec_49856` bound.
-/
theorem C07TightCreditSpec.ofDecodeAndFromPb {F : ShaCompress}
    {DecodeStateEnv : Bytes → List AllocEvent → Prop}
    {StatesFromPbEnv : V1State → List AllocEvent → Prop}
    {cDec rDec cFrom rFrom : Nat}
    (hDec : ∀ stBytes : Bytes,
      stBytes.length ≤ spqrStateTightCapBytes →
      ValidEncoderPts640 stBytes →
      ValidChainParams stBytes →
      PhaseCreditSpec fineCostModel (DecodeStateEnv stBytes) cDec 0 0 rDec)
    (hFrom : ∀ pb : V1State,
      ValidV1PtsAt 640 pb →
      rawV1State pb ≤ 46880 →
      PhaseCreditSpec fineCostModel (StatesFromPbEnv pb) cFrom 0 0 rFrom) :
    C07TightCreditSpec F DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv
      cDec rDec cFrom rFrom 13607104 101536 :=
  ⟨hDec, hFrom, fun xSInto _ _ hv1 => statesIntoPb_fine_phaseCreditSpec_49856 xSInto hv1⟩

/-- Instantiates `C07TightCreditSpec` at `DecodeStateTightEnv`, `StatesFromPbTightEnv`, and `StatesIntoPbTightEnv`.
-/
theorem c07TightCreditSpec_inst (F : ShaCompress) :
    C07TightCreditSpec F
      (fun _ : Bytes => DecodeStateTightEnv)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      1307216 79236 359623 2560 376193 2400 :=
  ⟨fun _ _ _ _ => decodeState_fine_phaseCreditSpec_tight,
   fun _ _ _ => statesFromPb_fine_phaseCreditSpec_tight,
   fun _ _ _ _ => statesIntoPb_fine_phaseCreditSpec_tight⟩

/-- Small-class (`sc < 48`, `Δlive = Δpeak = 0`) `fineCostModel` `PhaseCreditSpec` bundle for `<States>::recv`.
-/
structure StatesRecvTightCreditSpec (F : ShaCompress)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (cRecv rRecv : Nat) : Prop where
  recv_spec :
    ∀ (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi),
      StatesDecPtsNeededBound st0 →
      StatesPtsBoundedAt 640 st0 →
      rawV1State st0.into_pb ≤ 46880 →
      PhaseCreditSpec fineCostModel (StatesRecvEnv st0 msg) cRecv 0 0 rRecv

/-- Domain size and parameter invariant bundle on `stBytes` and chain call ghosts `(xAdd, xRk)` for `spqr::recv`.
-/
structure SpqrRecvTightDomain (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes) (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost) : Prop where
  hLen : stBytes.length ≤ spqrStateTightCapBytes
  hPts : ValidEncoderPts640 stBytes
  hChainParams : ValidChainParams stBytes
  hDecoded :
    ∀ pre_pb : PqRatchetState, spqrDecodeState stBytes = .ok pre_pb →
      (∀ vn, pre_pb.versionNegotiation = some vn → vn.authKey.length ≤ 32) ∧
      (∀ c, pre_pb.chain = some c → c.links.length ≤ 4) ∧
      (∀ pb, pre_pb.inner = some (.v1 pb) → rawV1State pb ≤ 46880) ∧
      xAdd.self.links.length ≤ 4 ∧
      xRk.self.links.length ≤ 4 ∧
      RecvSmallTight xRk.self ∧
      ValidChainParamsPB xRk.self.params ∧
      (∀ (vn : VersionNegotiationPB) (pb : V1State) (c : Chain),
        pre_pb.versionNegotiation = some vn →
        pre_pb.inner = some (.v1 pb) →
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
        pqRatchetStatePBEncodedLen
          { versionNegotiation := some vn, chain := some c.intoPb, inner := some (.v1 pb) } ≤
            spqrStateTightCapBytes) ∧
      (∀ (pb : V1State) (st0 : States spqrPolyApi (spqrAuthApi F))
          (sckaMsg : Message spqrPolyApi) (v : V1Recv spqrPolyApi (spqrAuthApi F)) (c : Chain),
        pre_pb.inner = some (.v1 pb) →
        States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
        States.recv K st0 sckaMsg = .ok v →
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
        pqRatchetStatePBEncodedLen
          { versionNegotiation := none, chain := some c.intoPb, inner := some (.v1 v.state.into_pb) } ≤
            spqrStateTightCapBytes)

/-- Constructs `SpqrRecvTightDomain` from raw output component bounds (`32 + 238,532 + 46,880 + 752 = 286,196`).
-/
theorem SpqrRecvTightDomain.ofRawOutCaps {F : ShaCompress} {K : MlKem}
    {stBytes : Bytes} {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    (hLen : stBytes.length ≤ spqrStateTightCapBytes)
    (hPts : ValidEncoderPts640 stBytes)
    (hChainParams : ValidChainParams stBytes)
    (hDecRaw :
      ∀ pre_pb : PqRatchetState, spqrDecodeState stBytes = .ok pre_pb →
        (∀ vn, pre_pb.versionNegotiation = some vn → vn.authKey.length ≤ 32 ∧ rawVN vn ≤ 32) ∧
        (∀ c, pre_pb.chain = some c → c.links.length ≤ 4) ∧
        (∀ pb, pre_pb.inner = some (.v1 pb) → rawV1State pb ≤ 46880) ∧
        xAdd.self.links.length ≤ 4 ∧
        xRk.self.links.length ≤ 4 ∧
        RecvSmallTight xRk.self ∧
        ValidChainParamsPB xRk.self.params ∧
        (∀ c : Chain,
          (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
          rawChain c.intoPb ≤ 238532) ∧
        (∀ (pb : V1State) (st0 : States spqrPolyApi (spqrAuthApi F))
            (sckaMsg : Message spqrPolyApi) (v : V1Recv spqrPolyApi (spqrAuthApi F)),
          pre_pb.inner = some (.v1 pb) →
          States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
          States.recv K st0 sckaMsg = .ok v →
          rawV1State v.state.into_pb ≤ 46880)) :
    SpqrRecvTightDomain F K stBytes xAdd xRk where
  hLen := hLen
  hPts := hPts
  hChainParams := hChainParams
  hDecoded pre_pb hdec := by
    obtain ⟨hvn, hc, hpb, hadd, hrk, hprev, hcp, hrcOut, hvOut⟩ := hDecRaw pre_pb hdec
    refine ⟨fun vn hv => (hvn vn hv).1, hc, hpb, hadd, hrk, hprev, hcp, ?_, ?_⟩
    · intro vn pb c hv hi hrk_ok
      set stOut : PqRatchetState :=
        { versionNegotiation := some vn, chain := some c.intoPb, inner := some (.v1 pb) }
      have hlen := pqRatchetStateEncodeToVec_len_le stOut
      have hst_eq : rawPqState stOut = rawVN vn + rawChain c.intoPb + rawV1State pb := rfl
      have h1 := (hvn vn hv).2
      have h2 := hrcOut c hrk_ok
      have h3 := hpb pb hi
      have hsum : rawPqState stOut + 752 ≤ spqrStateTightCapBytes := by
        rw [hst_eq]
        exact Nat.le_trans
          (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add h1 h2) h3) 752)
          (by decide)
      exact Nat.le_trans hlen hsum
    · intro pb st0 sckaMsg v c hi hfrom hrecv hrk_ok
      set stOut : PqRatchetState :=
        { versionNegotiation := none, chain := some c.intoPb, inner := some (.v1 v.state.into_pb) }
      have hlen := pqRatchetStateEncodeToVec_len_le stOut
      have hst_eq : rawPqState stOut = 0 + rawChain c.intoPb + rawV1State v.state.into_pb := rfl
      have h2 := hrcOut c hrk_ok
      have h3 := hvOut pb st0 sckaMsg v hi hfrom hrecv
      have hsum : rawPqState stOut + 752 ≤ spqrStateTightCapBytes := by
        rw [hst_eq, Nat.zero_add]
        exact Nat.le_trans
          (Nat.add_le_add_right (Nat.add_le_add h2 h3) 752)
          (by decide)
      exact Nat.le_trans hlen hsum

/-! ## Parametric Tight Envelopes -/

/-- `V1ChainAndEncodeEnv` parameterized by `StatesIntoPbEnv'`. -/
def V1ChainAndEncodeTightEnv (F : ShaCompress)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (pre_pb : PqRatchetState) (esOpt : Option EpochSecret)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (ChainFromEnv pre_pb.chain pre_pb.versionNegotiation)
    (fun evs1 =>
      FreeOnlyEvs evs1 ∨
        (rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
          rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
          SeqEnv (OptChainAddEpochEnv F esOpt xAdd)
            (fun evs2 =>
              FreeOnlyEvs evs2 ∨
                SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk)
                  (fun evs3 =>
                    FreeOnlyEvs evs3 ∨
                      ((∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
                          .ok (xCInto.chain, rawKey)) ∧
                        SeqEnv (StatesIntoPbEnv' xSInto)
                          (SeqEnv (ChainIntoPbEnv xCInto)
                            (SeqEnv
                              (PqRatchetStateEncodeToVecEnv
                                { versionNegotiation := none
                                  chain := some xCInto.chain.intoPb
                                  inner := some (.v1 xSInto.st.into_pb) })
                              FreeOnlyEvs)) evs3)) evs2) evs1)) evs

/-- `SpqrRecvEqualCallEnv` parameterized by `StatesFromPbEnv` and `StatesIntoPbEnv'`. -/
def SpqrRecvEqualTightEnv (F : ShaCompress) (K : MlKem)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SeqEnv FreeOnlyEvs
    (fun evsAfterMd =>
      FreeOnlyEvs evsAfterMd ∨
        SeqEnv (StatesFromPbEnv pb)
          (fun evsAfterFrom =>
            FreeOnlyEvs evsAfterFrom ∨
              (States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 ∧
                SeqEnv (StatesRecvEnv st0 sckaMsg)
                  (fun evsAfterRecv =>
                    FreeOnlyEvs evsAfterRecv ∨
                      (States.recv K st0 sckaMsg = .ok v ∧
                        xSInto.st = v.state ∧
                        V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb v.key
                          xAdd xRk xSInto xCInto evsAfterRecv)) evsAfterFrom)) evsAfterMd) evs

/-- `spqr::recv` envelope parameterized by `DecodeStateEnv`, `StatesFromPbEnv`, `StatesIntoPbEnv'`, and `StatesRecvEnv`.
-/
def SpqrRecvTightEnv (F : ShaCompress) (K : MlKem)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (DecodeStateEnv stBytes)
      (fun evsAfterDec =>
        FreeOnlyEvs evsAfterDec ∨
          (spqrDecodeState stBytes = .ok pre_pb ∧
            ((pre_pb.versionNegotiation = some vn ∧ xInit.authKey = vn.authKey ∧
                SpqrRecvLessCallEnv F pre_pb vn xInit xCInto evsAfterDec) ∨
              (pre_pb.versionNegotiation = some vn ∧ pre_pb.inner = some (.v1 pb) ∧
                SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xCInto evsAfterDec) ∨
              (pre_pb.inner = some (.v1 pb) ∧
                SpqrRecvEqualTightEnv F K StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
                  pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evsAfterDec)))) evs

/-- Definitional equality between `SpqrRecvTightEnv` at bounded codec envelopes and `SpqrRecvPartsEnv`.
-/
theorem spqrRecvTightEnv_eq_spqrRecvPartsEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvTightEnv F K (fun s => DecodeStateBoundedEnv s.length)
      StatesFromPbBoundedEnv StatesIntoPbEnv StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto =
    SpqrRecvPartsEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto :=
  rfl

theorem spqrRecvTightEnv_nil (F : ShaCompress) (K : MlKem)
    (DecodeStateEnv : Bytes → List AllocEvent → Prop)
    (StatesFromPbEnv : V1State → List AllocEvent → Prop)
    (StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvTightEnv F K DecodeStateEnv StatesFromPbEnv StatesIntoPbEnv' StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] :=
  Or.inl fun _ h => nomatch h

/-- `V1ChainAndEncodeTightEnv` specialized to `StatesIntoPbTightEnv`. -/
def V1ChainAndEncodeC07TightEnv (F : ShaCompress)
    (pre_pb : PqRatchetState) (esOpt : Option EpochSecret)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  V1ChainAndEncodeTightEnv F (fun _ => StatesIntoPbTightEnv)
    pre_pb esOpt xAdd xRk xSInto xCInto evs

/-- `SpqrRecvEqualTightEnv` specialized to `StatesFromPbTightEnv` and `StatesIntoPbTightEnv`. -/
def SpqrRecvEqualC07TightEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (pre_pb : PqRatchetState) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvEqualTightEnv F K (fun _ => StatesFromPbTightEnv) (fun _ => StatesIntoPbTightEnv)
    StatesRecvEnv pre_pb pb st0 sckaMsg v xAdd xRk xSInto xCInto evs

/-- `SpqrRecvTightEnv` specialized to `DecodeStateTightEnv`, `StatesFromPbTightEnv`, and `StatesIntoPbTightEnv`.
-/
def SpqrRecvC07TightEnv (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvTightEnv F K
    (fun _ => DecodeStateTightEnv)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    StatesRecvEnv stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem spqrRecvC07TightEnv_nil (F : ShaCompress) (K : MlKem)
    (StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall) :
    SpqrRecvC07TightEnv F K StatesRecvEnv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto [] :=
  spqrRecvTightEnv_nil F K _ _ _ StatesRecvEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto

/-! ## Tight Branch 1–2 and `V1ChainAndEncodeTightEnv` Credit Specs -/

/-- Tight `Ordering::Less` `PhaseCreditSpec` on `fineCostModel` (`Δcum = 1,348,326`, `Δlive = Δpeak = 0`, `maxReq = 2,112`).
-/
theorem spqrRecvOrderingLess_phaseCreditSpec_tight
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB}
    {xInit : InitInnerGhost} {xInto : ChainIntoPbCall}
    (hauth_eq : xInit.authKey = vn.authKey)
    (hauth32 : vn.authKey.length ≤ 32)
    (hcLinks : ∀ c, pre_pb.chain = some c → c.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (SpqrRecvLessCallEnv F pre_pb vn xInit xInto)
      1348326 0 0 2112 := by
  have hInit := initInner_fine_phaseCreditSpec_32 F xInit (hauth_eq ▸ hauth32)
  have hCf := chainFrom_fine_phaseCreditSpec pre_pb.chain (some vn)
  have hTailOk : PhaseCreditSpec fineCostModel
      (fun evsTail =>
        chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain ∧
          SeqEnv (ChainIntoPbEnv xInto) FreeOnlyEvs evsTail)
      10435 0 0 448 := by
    by_cases hcf : chainFrom (spqrHkdfWith F) pre_pb.chain (some vn) = .ok xInto.chain
    · have hlen4 := chainFrom_links_length_le_4 hcLinks hcf
      exact (phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl 0)
        (chainIntoPb_fine_phaseCreditSpec_4 xInto hlen4)).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hcf
  have hTail := phaseCreditSpec_or_freeOnly_fine hTailOk
  have hActive :=
    phaseCreditSpec_seq_zero_left_fine hInit (phaseCreditSpec_seq_zero_left_fine hCf hTail)
  unfold SpqrRecvLessCallEnv
  exact (phaseCreditSpec_or_freeOnly_fine hActive).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem v0ChainInit_fine_phaseCreditSpec
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (xNew : ChainNewGhost) :
    PhaseCreditSpec fineCostModel (V0ChainInitEnv pre_pb vn xNew) 16643 0 0 448 := by
  unfold V0ChainInitEnv
  exact phaseCreditSpec_or_freeOnly_fine
    ((chainNew_fine_phaseCreditSpec.or
      (chainFrom_fine_phaseCreditSpec pre_pb.chain (some vn))).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide))

/-- Tight `Ordering::Greater` `PhaseCreditSpec` on `fineCostModel` independent of `xRk.G` (`Δcum = 19,352,456`, `Δlive = 605,066`, `Δpeak = 621,350`).
-/
theorem spqrRecvOrderingGreater_phaseCreditSpec_tight
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {xNew : ChainNewGhost} {xRk : ChainRecvKeyGhost} {xInto : ChainIntoPbCall}
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := some vn, chain := some c.intoPb, inner := some (.v1 pb) } ≤
          spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel (SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xInto)
      19352456 605066 621350 302480 := by
  have hInit := v0ChainInit_fine_phaseCreditSpec pre_pb vn xNew
  have hRk := chainRecvKey_fine_phaseCreditSpec_tight (spqrHkdfWith F) xRk
    hParams.1 hParams.2 hPrev
  have hTailOk : PhaseCreditSpec fineCostModel
      (fun evsTail =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xInto.chain, rawKey)) ∧
          SeqEnv (ChainIntoPbEnv xInto)
            (SeqEnv
              (PqRatchetStateEncodeToVecEnv
                { versionNegotiation := some vn
                  chain := some xInto.chain.intoPb
                  inner := some (.v1 pb) })
              FreeOnlyEvs) evsTail)
      171967 294391 294391 286196 := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hInto := chainIntoPb_fine_phaseCreditSpec_4 xInto hlen4
      have hEnc := phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := some vn, chain := some xInto.chain.intoPb, inner := some (.v1 pb) }
          (hOutCap xInto.chain ⟨rawKey, hrk⟩))
      exact ((phaseCreditSpec_seq_zero_left_fine hInto hEnc).of_imp fun _ h => h.2).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hTail := phaseCreditSpec_or_freeOnly_fine hTailOk
  have hRkTail : PhaseCreditSpec fineCostModel _ 19335813 605066 621350 302480 :=
    (hRk.seq hTail).mono (by decide) (by decide) (by decide) (by decide)
  have hSeq := (phaseCreditSpec_seq_zero_left_fine hInit hRkTail).of_imp
    (E₁ := fun evs => rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      SeqEnv (V0ChainInitEnv pre_pb vn xNew)
        (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk) _) evs)
    fun _ h => h.2
  unfold SpqrRecvGreaterCallEnv
  exact (phaseCreditSpec_or_freeOnly_fine hSeq).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- Tight `Ordering::Greater` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk` (`Δcum = 19,342,917`, `Δlive = Δpeak = 294,391`).
-/
theorem spqrRecvOrderingGreater_phaseCreditSpec_tight_smallHist
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {xNew : ChainNewGhost} {xRk : ChainRecvKeyGhost} {xInto : ChainIntoPbCall}
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := some vn, chain := some c.intoPb, inner := some (.v1 pb) } ≤
          spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel (SpqrRecvGreaterCallEnv F pre_pb vn pb xNew xRk xInto)
      19342917 294391 294391 286196 := by
  have hInit := v0ChainInit_fine_phaseCreditSpec pre_pb vn xNew
  have hRk := chainRecvKey_fine_phaseCreditSpec_tight_smallHist (spqrHkdfWith F) xRk
    hParams.1 hHist
  have hTailOk : PhaseCreditSpec fineCostModel
      (fun evsTail =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xInto.chain, rawKey)) ∧
          SeqEnv (ChainIntoPbEnv xInto)
            (SeqEnv
              (PqRatchetStateEncodeToVecEnv
                { versionNegotiation := some vn
                  chain := some xInto.chain.intoPb
                  inner := some (.v1 pb) })
              FreeOnlyEvs) evsTail)
      171967 294391 294391 286196 := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hInto := chainIntoPb_fine_phaseCreditSpec_4 xInto hlen4
      have hEnc := phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := some vn, chain := some xInto.chain.intoPb, inner := some (.v1 pb) }
          (hOutCap xInto.chain ⟨rawKey, hrk⟩))
      exact ((phaseCreditSpec_seq_zero_left_fine hInto hEnc).of_imp fun _ h => h.2).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hTail := phaseCreditSpec_or_freeOnly_fine hTailOk
  have hRkTail : PhaseCreditSpec fineCostModel _ 19326274 294391 294391 286196 :=
    (phaseCreditSpec_seq_zero_left_fine hRk hTail).mono
      (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)
  have hSeq := (phaseCreditSpec_seq_zero_left_fine hInit hRkTail).of_imp
    (E₁ := fun evs => rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
      SeqEnv (V0ChainInitEnv pre_pb vn xNew)
        (SeqEnv (ChainRecvKeyEnv (spqrHkdfWith F) xRk) _) evs)
    fun _ h => h.2
  unfold SpqrRecvGreaterCallEnv
  exact (phaseCreditSpec_or_freeOnly_fine hSeq).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem optChainAddEpoch_fine_phaseCreditSpec_4
    (F : ShaCompress) (esOpt : Option EpochSecret) (xAdd : ChainAddEpochGhost)
    (hlen : xAdd.self.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (OptChainAddEpochEnv F esOpt xAdd) 17539 0 0 896 := by
  unfold OptChainAddEpochEnv
  cases esOpt with
  | none =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | some _ =>
    exact chainAddEpoch_fine_phaseCreditSpec_4 (spqrHkdfWith F) xAdd hlen

/-- Tight `V1ChainAndEncodeTightEnv` `PhaseCreditSpec` independent of `xRk.G` (`Δcum = 19,369,995 + cInto`).
-/
theorem v1ChainAndEncode_phaseCreditSpec_tight
    (F : ShaCompress)
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {cInto rInto : Nat}
    (hSIntoSpec : PhaseCreditSpec fineCostModel (StatesIntoPbEnv' xSInto) cInto 0 0 rInto)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 xSInto.st.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb esOpt xAdd xRk xSInto xCInto)
      (19369995 + cInto) 605066 621350 (max 302480 rInto) := by
  have hCf := chainFrom_fine_phaseCreditSpec pre_pb.chain pre_pb.versionNegotiation
  have hAdd := optChainAddEpoch_fine_phaseCreditSpec_4 F esOpt xAdd hAddLinks
  have hRk := chainRecvKey_fine_phaseCreditSpec_tight (spqrHkdfWith F) xRk
    hParams.1 hParams.2 hPrev
  have hEncodeTail : PhaseCreditSpec fineCostModel
      (fun evs3 =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xCInto.chain, rawKey)) ∧
          SeqEnv (StatesIntoPbEnv' xSInto)
            (SeqEnv (ChainIntoPbEnv xCInto)
              (SeqEnv
                (PqRatchetStateEncodeToVecEnv
                  { versionNegotiation := none
                    chain := some xCInto.chain.intoPb
                    inner := some (.v1 xSInto.st.into_pb) })
                FreeOnlyEvs)) evs3)
      (cInto + 171967) 294391 294391 (max rInto 286196) := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xCInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xCInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hC := chainIntoPb_fine_phaseCreditSpec_4 xCInto hlen4
      have hE := phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := none
            chain := some xCInto.chain.intoPb
            inner := some (.v1 xSInto.st.into_pb) }
          (hOutCap xCInto.chain ⟨rawKey, hrk⟩))
      have hCE : PhaseCreditSpec fineCostModel _ 171967 294391 294391 286196 :=
        (phaseCreditSpec_seq_zero_left_fine hC hE).mono
          (by decide) (by decide) (by decide) (by decide)
      exact (phaseCreditSpec_seq_zero_left_fine hSIntoSpec hCE).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hEvs3 := phaseCreditSpec_or_freeOnly_fine hEncodeTail
  have hRkTail : PhaseCreditSpec fineCostModel _
      (19163846 + (cInto + 171967)) 605066 621350 (max 302480 rInto) :=
    (hRk.seq hEvs3).mono
      (Nat.le_refl _) (by decide) (by decide)
      (Nat.max_le.mpr ⟨Nat.le_max_left 302480 rInto,
        Nat.max_le.mpr ⟨Nat.le_max_right 302480 rInto,
          Nat.le_trans (by decide : 286196 ≤ 302480) (Nat.le_max_left 302480 rInto)⟩⟩)
  have hEvs2 := phaseCreditSpec_or_freeOnly_fine hRkTail
  have hAddEvs2 := (phaseCreditSpec_seq_zero_left_fine hAdd hEvs2).of_imp
    (E₁ := fun evs1 =>
      rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
        SeqEnv (OptChainAddEpochEnv F esOpt xAdd) _ evs1)
    fun _ h => h.2.2
  have hSeq := phaseCreditSpec_seq_zero_left_fine hCf (phaseCreditSpec_or_freeOnly_fine hAddEvs2)
  have hcum : 16643 + (17539 + (19163846 + (cInto + 171967))) ≤ 19369995 + cInto := by
    have heq : 16643 + (17539 + (19163846 + (cInto + 171967))) =
        (16643 + 17539 + 19163846 + 171967) + cInto := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.add_le_add_right
      (by decide : 16643 + 17539 + 19163846 + 171967 ≤ 19369995) cInto
  have hreq : max 448 (max 896 (max 302480 rInto)) ≤ max 302480 rInto :=
    Nat.max_le.mpr ⟨Nat.le_trans (by decide : 448 ≤ 302480) (Nat.le_max_left _ _),
      Nat.max_le.mpr ⟨Nat.le_trans (by decide : 896 ≤ 302480) (Nat.le_max_left _ _),
        Nat.le_refl _⟩⟩
  unfold V1ChainAndEncodeTightEnv
  exact hSeq.mono hcum (Nat.le_refl _) (Nat.le_refl _) hreq

/-- Tight `V1ChainAndEncodeTightEnv` `PhaseCreditSpec` under `KeyHistorySmallOrReserved xRk` (`Δcum = 19,360,456 + cInto`, `Δlive = Δpeak = 294,391`).
-/
theorem v1ChainAndEncode_phaseCreditSpec_tight_smallHist
    (F : ShaCompress)
    {StatesIntoPbEnv' : StatesIntoPbGhost F → List AllocEvent → Prop}
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {cInto rInto : Nat}
    (hSIntoSpec : PhaseCreditSpec fineCostModel (StatesIntoPbEnv' xSInto) cInto 0 0 rInto)
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 xSInto.st.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (V1ChainAndEncodeTightEnv F StatesIntoPbEnv' pre_pb esOpt xAdd xRk xSInto xCInto)
      (19360456 + cInto) 294391 294391 (max 286196 rInto) := by
  have hCf := chainFrom_fine_phaseCreditSpec pre_pb.chain pre_pb.versionNegotiation
  have hAdd := optChainAddEpoch_fine_phaseCreditSpec_4 F esOpt xAdd hAddLinks
  have hRk := chainRecvKey_fine_phaseCreditSpec_tight_smallHist (spqrHkdfWith F) xRk
    hParams.1 hHist
  have hEncodeTail : PhaseCreditSpec fineCostModel
      (fun evs3 =>
        (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
            .ok (xCInto.chain, rawKey)) ∧
          SeqEnv (StatesIntoPbEnv' xSInto)
            (SeqEnv (ChainIntoPbEnv xCInto)
              (SeqEnv
                (PqRatchetStateEncodeToVecEnv
                  { versionNegotiation := none
                    chain := some xCInto.chain.intoPb
                    inner := some (.v1 xSInto.st.into_pb) })
                FreeOnlyEvs)) evs3)
      (cInto + 171967) 294391 294391 (max rInto 286196) := by
    by_cases hrk_ok : ∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index =
        .ok (xCInto.chain, rawKey)
    · obtain ⟨rawKey, hrk⟩ := hrk_ok
      have hlen4 : xCInto.chain.links.length ≤ 4 :=
        (chainRecvKey_links_length_eq hrk) ▸ hRkLinks
      have hC := chainIntoPb_fine_phaseCreditSpec_4 xCInto hlen4
      have hE := phaseCreditSpec_seq_freeOnly_right_fine (Nat.le_refl _)
        (pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
          { versionNegotiation := none
            chain := some xCInto.chain.intoPb
            inner := some (.v1 xSInto.st.into_pb) }
          (hOutCap xCInto.chain ⟨rawKey, hrk⟩))
      have hCE : PhaseCreditSpec fineCostModel _ 171967 294391 294391 286196 :=
        (phaseCreditSpec_seq_zero_left_fine hC hE).mono
          (by decide) (by decide) (by decide) (by decide)
      exact (phaseCreditSpec_seq_zero_left_fine hSIntoSpec hCE).of_imp fun _ h => h.2
    · exact phaseCreditSpec_of_false_fine _ _ _ _ fun _ h => absurd h.1 hrk_ok
  have hEvs3 := phaseCreditSpec_or_freeOnly_fine hEncodeTail
  have hRkTail : PhaseCreditSpec fineCostModel _
      (19154307 + (cInto + 171967)) 294391 294391 (max 286196 rInto) :=
    (phaseCreditSpec_seq_zero_left_fine hRk hEvs3).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.max_le.mpr ⟨Nat.le_trans (by decide : 135166 ≤ 286196) (Nat.le_max_left 286196 rInto),
        Nat.max_le.mpr ⟨Nat.le_max_right 286196 rInto, Nat.le_max_left 286196 rInto⟩⟩)
  have hEvs2 := phaseCreditSpec_or_freeOnly_fine hRkTail
  have hAddEvs2 := (phaseCreditSpec_seq_zero_left_fine hAdd hEvs2).of_imp
    (E₁ := fun evs1 =>
      rawChain xAdd.self.intoPb ≤ optRaw rawChain pre_pb.chain + 296 ∧
        rawChain xRk.self.intoPb ≤ optRaw rawChain pre_pb.chain + 1058 ∧
        SeqEnv (OptChainAddEpochEnv F esOpt xAdd) _ evs1)
    fun _ h => h.2.2
  have hSeq := phaseCreditSpec_seq_zero_left_fine hCf (phaseCreditSpec_or_freeOnly_fine hAddEvs2)
  have hcum : 16643 + (17539 + (19154307 + (cInto + 171967))) ≤ 19360456 + cInto := by
    have heq : 16643 + (17539 + (19154307 + (cInto + 171967))) =
        (16643 + 17539 + 19154307 + 171967) + cInto := by
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    exact heq ▸ Nat.add_le_add_right
      (by decide : 16643 + 17539 + 19154307 + 171967 ≤ 19360456) cInto
  have hreq : max 448 (max 896 (max 286196 rInto)) ≤ max 286196 rInto :=
    Nat.max_le.mpr ⟨Nat.le_trans (by decide : 448 ≤ 286196) (Nat.le_max_left _ _),
      Nat.max_le.mpr ⟨Nat.le_trans (by decide : 896 ≤ 286196) (Nat.le_max_left _ _),
        Nat.le_refl _⟩⟩
  unfold V1ChainAndEncodeTightEnv
  exact hSeq.mono hcum (Nat.le_refl _) (Nat.le_refl _) hreq

theorem v1ChainAndEncode_c07_phaseCreditSpec_tight
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hPrev : RecvSmallTight xRk.self)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 xSInto.st.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (V1ChainAndEncodeC07TightEnv F pre_pb esOpt xAdd xRk xSInto xCInto)
      19746188 605066 621350 302480 := by
  unfold V1ChainAndEncodeC07TightEnv
  exact (v1ChainAndEncode_phaseCreditSpec_tight F statesIntoPb_fine_phaseCreditSpec_tight
    hAddLinks hRkLinks hParams hPrev hOutCap).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

theorem v1ChainAndEncode_c07_phaseCreditSpec_tight_smallHist
    (F : ShaCompress)
    {pre_pb : PqRatchetState} {esOpt : Option EpochSecret}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    (hAddLinks : xAdd.self.links.length ≤ 4)
    (hRkLinks : xRk.self.links.length ≤ 4)
    (hParams : ValidChainParamsPB xRk.self.params)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hOutCap : ∀ c : Chain,
      (∃ rawKey, xRk.self.recvKey (spqrHkdfWith F) xRk.epoch xRk.index = .ok (c, rawKey)) →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := none
          chain := some c.intoPb
          inner := some (.v1 xSInto.st.into_pb) } ≤ spqrStateTightCapBytes) :
    PhaseCreditSpec fineCostModel
      (V1ChainAndEncodeC07TightEnv F pre_pb esOpt xAdd xRk xSInto xCInto)
      19736649 294391 294391 286196 := by
  unfold V1ChainAndEncodeC07TightEnv
  exact (v1ChainAndEncode_phaseCreditSpec_tight_smallHist F statesIntoPb_fine_phaseCreditSpec_tight
    hAddLinks hRkLinks hParams hHist hOutCap).mono
    (by decide) (Nat.le_refl _) (Nat.le_refl _) (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
