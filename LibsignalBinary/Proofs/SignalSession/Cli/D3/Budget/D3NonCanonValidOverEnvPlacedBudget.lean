/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3StageP3Prev1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Slot Envelopes, `SingleSlotFineSpec`, and `W4RecvPrekeyRealEnv` Inclusion for `validOver`

Defines the `DecPkOkOverV4` (`validOver`) slot allocation envelopes (`DecPkD3ValidOverEnv`,
`DecPkD3ValidOverCliEnv`, `ValidOverRealSlotEnv`), proves `SingleSlotFineSpec`, closed `1 MiB` and
`1 GiB` cap inequalities, and `W4RecvPrekeyRealDomOf`, and establishes inclusion into
`W4RecvPrekeyRealEnv` along with whole-`main` `FitsEnv` at `cliBudgetLimits`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1 (spqrV1)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs PqParty PqxdhPartyInSpecDomain pqRecvInputs)
open CryptoVerification.SignalSession.Cli (CliInputsOk StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudget (TryDecryptCliEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (phaseGroupSpec_exists_guarded)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (CliPqOrD3RecvDom d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq
   d3RecvW4ExtPeak mainSt0Dom mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB
   mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_mem_w4 mkD3RecvCalleeEnvs
   realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB
   realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftWf (peerSpqrStateTight640_of_pqRecv_wf)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4RecvPrekeyRealEnv W4RecvPrekeyRealParams mkW4RecvPrekeySlotParams
   w4RecvPrekeyRealEnv_nonvacuous_alloc w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf
   W4TryDecryptPathACDomOf w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
   w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak w4RecvPrekeyReal1MiB_i_eq
   w4RecvPrekeyReal1MiB_i_singleSlotFineSpec)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
  (DecPkD3ValidOverPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
  (CliStageP4Prev1Envs cliPollStageP4Prev1Envs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## 1. Parametric & Concrete CLI `validOver` Slot Allocation Envelopes -/

/-- Parametric D3 `validOver` (`DecPkOkOverV4`) `decrypt_prekey` slot allocation envelope
(`cliDecryptPrekey` Block `520` prologue/epilogue is stack-only, so the slot envelope equals
`DecPkD3ValidOverPollEnv`). -/
def DecPkD3ValidOverEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop)
    (p4Envs : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
      (pid kpkId spkId : BitVec 32) (kbk : PublicKey),
      CliStageP4Prev1Envs (A := A) B F0 peer pid kpkId spkId kbk)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3ValidOverPollEnv (A := A) W X B ReadEnv DeserEnv
    P2OverErrEnv P2OverOkEnv tdEnv p4Envs g evs

/-- Concrete CLI specialization of `DecPkD3ValidOverEnv` wired to `ReadFileRuleEnv cliIo.rd`,
`SessDeserializeCancelEnv`, `TryDecryptCliEnv W.C (spqrV1 W.C.F W.Q.K)`, and
`cliPollStageP4Prev1Envs`. -/
def DecPkD3ValidOverCliEnv [LibsignalPlacement] (A : RustAlloc)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    (P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (g : DecPkGhost) (evs : List AllocEvent) : Prop :=
  DecPkD3ValidOverEnv A W X B
    (ReadFileRuleEnv cliIo.rd)
    SessDeserializeCancelEnv
    P2OverErrEnv P2OverOkEnv
    (fun W' => TryDecryptCliEnv W'.C (spqrV1 W'.C.F W'.Q.K))
    (fun B' F0 peer pid kpkId spkId kbk =>
      cliPollStageP4Prev1Envs A B' F0 peer pid kpkId spkId kbk (ReadFileRuleEnv cliIo.rd))
    g evs

/-! ## 2. `SingleSlotFineSpec`, Slot-Cap Bounds, & `W4RecvPrekeyRealDomOf` -/

theorem phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

/-- Existential Variant (i) W4 real-slot envelope (`(sessionCapBytes, msgCapBytes)`). -/
def ValidOverRealSlotEnv (evs : List AllocEvent) : Prop :=
  ∃ w4R : W4RecvPrekeyRealParams,
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs

def decPkD3ValidOverCum : Nat := w4RecvPrekeyReal1MiB_i_Cum
def decPkD3ValidOverLive : Nat := w4RecvPrekeyReal1MiB_i_Live
def decPkD3ValidOverPeak : Nat := w4RecvPrekeyReal1MiB_i_Peak
def decPkD3ValidOverMaxReq : Nat := w4RecvPrekeyReal1MiB_i_MaxReq
def decPkD3ValidOverGrpS : Nat := w4RecvPrekeyRealGrpS

/-- `SingleSlotFineSpec` for `ValidOverRealSlotEnv`. -/
def decPkD3ValidOverReal_singleSlotFineSpec :
    SingleSlotFineSpec ValidOverRealSlotEnv where
  cum := decPkD3ValidOverCum
  live := decPkD3ValidOverLive
  peak := decPkD3ValidOverPeak
  maxReq := decPkD3ValidOverMaxReq
  grpS := decPkD3ValidOverGrpS
  credit := phaseCredit_exists_guarded_u fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).credit
  live_le_peak := w4RecvPrekeyReal1MiB_i_eq.2.2.2.2
  groups := phaseGroupSpec_exists_guarded fineCostModel fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_singleSlotFineSpec w4R hw4).groups

/-- Closed inequalities bounding `ValidOverRealSlotEnv` within Variant (i) of the `1 MiB`
`recv` pre-key slot caps (`w4RecvPrekeyReal1MiB_i_*`, `w4RecvPrekeyRealGrpS`). -/
theorem decPkD3ValidOver_caps_le :
    decPkD3ValidOverLive ≤ decPkD3ValidOverPeak ∧
    decPkD3ValidOverCum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
    decPkD3ValidOverLive ≤ w4RecvPrekeyReal1MiB_i_Live ∧
    decPkD3ValidOverPeak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
    decPkD3ValidOverMaxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
    decPkD3ValidOverGrpS ≤ w4RecvPrekeyRealGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Extended-ceiling (`d3RecvW4Ext*`) cap inequalities accommodating `1 GiB` Stage-P3
`SegCloneEnv` headroom. -/
theorem decPkD3ValidOver_ext_caps_le :
    decPkD3ValidOverCum ≤ d3RecvW4ExtCum ∧
    decPkD3ValidOverLive ≤ d3RecvW4ExtLive ∧
    decPkD3ValidOverPeak ≤ d3RecvW4ExtPeak ∧
    decPkD3ValidOverMaxReq ≤ d3RecvW4ExtMaxReq ∧
    decPkD3ValidOverGrpS ≤ d3RecvW4ExtGrpS :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
   Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- `PeerSpqrStateTight640` on `CliPqOrD3RecvDom P i` (`CliPqxdhInputs` or `pqRecvInputs` of a
spec-domain party). -/
theorem peerSpqrStateTight640_of_cliPqOrD3Recv {P : PEParams} {i : Inputs} {peer : AddrV}
    (hi : CliPqOrD3RecvDom P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer)) :
    PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peer) := by
  rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
  · exact peerSpqrStateTight640_of_cliPqInputs_recv hPq hparse
  · exact peerSpqrStateTight640_of_pqRecv_wf hwf hparse

/-- Establishes `W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes` for Path-C overwrite runs
(`hasCurSession = true`, `archivedTrials.length ≤ 4`, `isPathAC = true`) from
`parseArgs = some (.recv peerAddr)` and `cliIo_rd_ok_length_le_sessionCapBytes`. -/
theorem w4RecvPrekeyRealDomOf_validOver {i : Inputs} {peerAddr : AddrV}
    (R : W4RecvPrekeyRealParams)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hrd : R.rd = cliIo.rd)
    (hfiles : R.files = runFiles i)
    (hkpk : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort)
    (hpeer : R.peer.val = addrValOf peerAddr)
    (hownKey : R.ownKeyName.length ≤ 64)
    (hownReg : R.ownRegName.length ≤ 64)
    (hkpkMark : R.kpkMarkName.length ≤ 64)
    (hresOld : R.x_res.cap.toNat ≤ 4096)
    (hresNew : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096)
    (hspqrKey : R.x_spqr.p.authKey.length ≤ 32)
    (hcurDom : R.hasCurSession = true →
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
          SessionCloneDom 286196 ses_cur)
    (hcurFail : R.hasCurSession = true → W4FailedTdDomOf R.F R.K msgCapBytes R.fc_cur)
    (htrialsLen : R.archivedTrials.length ≤ 4)
    (htrialsDom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K msgCapBytes x)
    (harchValid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (harchEnc : (encodeRecord R.r_arch).length ≤ 2097152)
    (hout0Valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hout0Enc : (encodeRecord R.r_out0).length ≤ 2097152)
    (hout1 : FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1)
    (htdB : R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B)
    (htdAC : R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K msgCapBytes R.td_AC) :
    W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R where
  kpk_dir := hkpk
  outer_dom :=
    { peer_len := by
        have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
        change (mkW4RecvPrekeySlotParams R).peer.val.name.length ≤ 40
        simp only [mkW4RecvPrekeySlotParams, hpeer]
        exact hp40
      ownKey_len := hownKey
      ownReg_len := hownReg
      kpkMark_len := hkpkMark
      res_old := hresOld
      res_new := hresNew
      ikm_small := by decide
      spqr_key := hspqrKey
      sess_cap := fun bs hbs => by
        rw [mkW4RecvPrekeySlotParams, hrd, hfiles] at hbs
        exact cliIo_rd_ok_length_le_sessionCapBytes (runFiles i) _ bs hbs
      small_cap := fun d _ n bs hbs => by
        rw [mkW4RecvPrekeySlotParams, hrd, hfiles] at hbs
        exact cliIo_rd_ok_length_le_sessionCapBytes (runFiles i) _ bs hbs
      cur_dom := by
        cases hcs : R.hasCurSession with
        | false =>
          exact Or.inl (fun evs hevs => by
            change (if R.hasCurSession then _ else fun _ => False) evs at hevs
            rw [hcs] at hevs
            exact hevs)
        | true =>
          exact Or.inr (hcurDom hcs)
      arch_valid := harchValid
      arch_enc := harchEnc
      out0_valid := hout0Valid
      out0_enc := hout0Enc
      out1_freshBob := hout1
      trials_len4 := htrialsLen }
  cur_fail_dom := hcurFail
  trials_dom := htrialsDom
  tdB_dom := htdB
  tdAC_dom := htdAC

/-- Non-empty allocation trace witness (`rustAllocEvents 24 8 ≠ []`) for `ValidOverRealSlotEnv`. -/
theorem validOverRealSlotEnv_nonvacuous_alloc
    {R : W4RecvPrekeyRealParams} (hDom : W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes R) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ ValidOverRealSlotEnv evs := by
  obtain ⟨evs, hne, hevs⟩ := w4RecvPrekeyRealEnv_nonvacuous_alloc R
  exact ⟨evs, hne, R, hDom, hevs⟩

/-! ## 3. `W4RecvPrekeyRealEnv` Inclusion & Whole-`main` `FitsEnv` -/

/-- Witness-fact bundle for the Stage-P3/P2 `W4RecvPrekeyRealEnv` structural bridge. -/
def ValidOverStageP3WitnessFacts (i : Inputs) (peerAddr : AddrV)
    (R : W4RecvPrekeyRealParams) (evs : List AllocEvent) : Prop :=
  R.rd = cliIo.rd ∧
  R.files = runFiles i ∧
  (R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
    R.kpkDir = StoresGhost.opened.kyber.lastResort) ∧
  R.peer.val = addrValOf peerAddr ∧
  R.ownKeyName.length ≤ 64 ∧
  R.ownRegName.length ≤ 64 ∧
  R.kpkMarkName.length ≤ 64 ∧
  R.x_res.cap.toNat ≤ 4096 ∧
  reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096 ∧
  R.x_spqr.p.authKey.length ≤ 32 ∧
  (R.hasCurSession = true →
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur) ∧
  (R.hasCurSession = true → W4FailedTdDomOf R.F R.K msgCapBytes R.fc_cur) ∧
  R.archivedTrials.length ≤ 4 ∧
  (∀ x ∈ R.archivedTrials, W4ArchivedTrialDomOf R.F R.K msgCapBytes x) ∧
  (∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
  (encodeRecord R.r_arch).length ≤ 2097152 ∧
  (∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses) ∧
  (encodeRecord R.r_out0).length ≤ 2097152 ∧
  FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1 ∧
  (R.isPathB = true → W4TryDecryptCallDomOf R.F R.K msgCapBytes R.td_B) ∧
  (R.isPathAC = true → W4TryDecryptPathACDomOf R.F R.K msgCapBytes R.td_AC) ∧
  W4RecvPrekeyRealEnv R evs

/-- Embeds `DecPkD3ValidOverCliEnv` into `ValidOverRealSlotEnv`
(`∃ w4R, W4RecvPrekeyRealDomOf sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs`). -/
theorem decPkD3ValidOverEnv_mem_validOverRealSlotEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (_hfiles : x.F = runFiles g.i)
    (_hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidOverStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
      ValidOverRealSlotEnv evs := by
  intro evs hevs
  have hTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) :=
    peerSpqrStateTight640_of_cliPqOrD3Recv hi hparse
  obtain ⟨R, hrd, hRfiles, hkpk, hRpeer, hownK, hownR, hkpkM, hresO, hresN, hspqrK,
    hcurDom, hcurFail, htrialsLen, htrialsDom, harchV, harchE, hout0V, hout0E,
    hout1, htdB, htdAC, hRenv⟩ := hStageP3Bridge hTight hstdin evs hevs
  exact ⟨R, w4RecvPrekeyRealDomOf_validOver R hparse hrd hRfiles hkpk hRpeer
    hownK hownR hkpkM hresO hresN hspqrK hcurDom hcurFail htrialsLen htrialsDom
    harchV harchE hout0V hout0E hout1 htdB htdAC, hRenv⟩

/-- Embeds `DecPkD3ValidOverCliEnv` into the mode-dispatched `.decPkEnv` of
`mkExistentialRealCalleeEnvs img S ⟨W.C, W.Q⟩ g`. -/
theorem decPkD3ValidOverEnv_mem_w4RecvPrekeyRealEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost}
    (hc : g.c = .recv peerAddr)
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidOverStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
      (match g.c with | .recv _ => ValidOverRealSlotEnv | _ => fun _ => False) evs := by
  intro evs hevs
  have hmem := decPkD3ValidOverEnv_mem_validOverRealSlotEnv A W X B hi hstdin hparse
    hfiles hpeer hStageP3Bridge evs hevs
  rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
  dsimp only at hc
  subst hc
  exact hmem

/-- Explicit `(mkExistentialRealCalleeEnvs img S ⟨W.C, W.Q⟩ g).decPkEnv` spelling of
`decPkD3ValidOverEnv_mem_w4RecvPrekeyRealEnv`. -/
theorem decPkD3ValidOverEnv_mem_existentialRealCalleeEnvs [LibsignalPlacement]
    (img : Image) (S : RunSem)
    (A : RustAlloc) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
    {P2OverErrEnv P2OverOkEnv :
      DecPkGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {g : RunCall} {peerAddr : AddrV} {x : DecPkGhost}
    (hc : g.c = .recv peerAddr)
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i)
    (hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerAddr))
    (hfiles : x.F = runFiles g.i)
    (hpeer : x.peer.val = addrValOf peerAddr)
    (hStageP3Bridge :
      PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerAddr) →
      g.i.stdin.length ≤ msgCapBytes →
      ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
        ∃ R : W4RecvPrekeyRealParams, ValidOverStageP3WitnessFacts g.i peerAddr R evs) :
    ∀ evs, DecPkD3ValidOverCliEnv A W X B P2OverErrEnv P2OverOkEnv x evs →
      (mkExistentialRealCalleeEnvs img S ⟨W.C, W.Q⟩ g).decPkEnv evs :=
  decPkD3ValidOverEnv_mem_w4RecvPrekeyRealEnv A W X B hc hi hstdin hparse hfiles hpeer
    hStageP3Bridge

/-- Whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` at `cliBudgetLimits` (`1 GiB`) for any
call-level `DecPkEnv` included in `(mkExistentialRealCalleeEnvs img S P g).decPkEnv`. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_validOver_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs) :
    ∀ i : Inputs, CliPqOrD3RecvDom P i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_mem_w4 img S P hMem

/-- Initial `mainSt0Dom` invariant at `cliBudgetLimits` (`1 GiB`) for `validOver`. -/
theorem mainSt0Dom_init_cliBudgetLimits_validOver_d3 [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (hMem : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      ∀ evs, DecPkEnv g evs → (mkExistentialRealCalleeEnvs img S P g).decPkEnv evs)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_mem_w4 img S P hMem i hok

/-- Extended-ceiling (`d3RecvW4Ext*`) whole-`main` `RealCliMainBinaryEnvOf` `FitsEnv` at
`cliBudgetLimits` (`1 GiB`) accommodating Stage-P3 `SegCloneEnv` headroom. -/
theorem realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_validOver_d3_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS) :
    ∀ i : Inputs, CliPqOrD3RecvDom P i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3RecvCalleeEnvs img S P DecPkEnv) i) :=
  realCliMainBinaryEnvOf_fitsEnv_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P S_pk hCaps

/-- Extended-ceiling (`d3RecvW4Ext*`) initial `mainSt0Dom` invariant at `cliBudgetLimits` (`1 GiB`). -/
theorem mainSt0Dom_init_cliBudgetLimits_validOver_d3_1GiB [LibsignalPlacement]
    (img : Image) (S : RunSem) (P : PEParams)
    {DecPkEnv : RunCall → List AllocEvent → Prop}
    (S_pk : ∀ (g : RunCall), CliPqOrD3RecvDom P g.i → g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (DecPkEnv g))
    (hCaps : ∀ (g : RunCall) (hi_g : CliPqOrD3RecvDom P g.i) (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS)
    (i : Inputs) (hok : CliInputsOk i) :
    mainSt0Dom (CliPqOrD3RecvDom P) (mkD3RecvCalleeEnvs img S P DecPkEnv) cliBudgetLimits i
      fineCostModel.init :=
  mainSt0Dom_init_cliBudgetLimits_pqRecv_d3_of_callSpecs_1GiB img S P S_pk hCaps i hok

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
