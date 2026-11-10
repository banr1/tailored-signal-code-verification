/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs

/-!
# Parametric Exact-Slot Binary-Kit Callee Envelopes and Whole-`run` Bridge

**Checked by Lean.**

Provides slot-parametric binary-kit callee bundles (`mkBinaryKitRealCalleeEnvsSlotOf`,
`realCliRunBinaryKitEnvOfSlot`, `realCliMainBinaryKitEnvOfSlot`) parameterized by `W1`/`W2` slot
families `EncSlot` and `DecSigSlot`, together with the whole-`run` inclusion theorem
`hmx_runEnvExact_sub_runBinaryKitEnvOfSlot` under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i` and the
whole-`main` `FitsEnv` statement `realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams PreKeyMessageFields UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall cliIo cliRunBudgets inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost Init1Data Init2Data InitGhost MeAtDispatch PksmGhost RunSem
   addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (pksmParse_lengths_le signalMessage_tryFrom_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams
   mkBinaryKitRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs
   init1Env_sub_r1bFileStepEnv init2Env_sub_r1bBinaryEnv preEnv_sub_r0BinaryEnv
   r1cInit3Env_sub_r1cEnv r2SendEnv_sub_r2Env r3aRecvWEnv_sub_r3aBinaryEnv r3bRecvPEnv_sub_r3bEnv
   runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (bundleReadEnv_fixed_eq_of_not_overCap dirGetEnv_fixed_eq_of_not_overCap
   mkBinaryKitRealCalleeEnvsFixed not_overCapFile_runFiles_bundle_idKey
   not_overCapFile_runFiles_bundle_kpk not_overCapFile_runFiles_bundle_opk
   not_overCapFile_runFiles_bundle_regId not_overCapFile_runFiles_bundle_spk
   not_overCapFile_runFiles_own_address readFileRuleEnvFixed_eq_of_not_overCap
   realCliInitBinarySlotEnvFixed w3InitBinaryKitSlotEnvFixed_eq_plain)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (CanonicalOrFallbackPksmEnv pksmCanonicalGuard_sub_binaryKit pksmCanonicalOrFallback_sub_binaryKit
   recv_rest_length_le_msgCapBytes w1_send_outPk_serialized_le_sessionCapBytes
   w1_send_out_serialized_le_sessionCapBytes w3_realCliInitBinarySlotEnv_sub_binaryKit)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (PksmCanonSliceEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget (Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env R1bStepKpkErrEnv R1bStepKpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

/-! ## 1. Slot-Parametric Binary-Kit `RunSlotEnvs` & `CliRunCalleeEnvs` Bundles -/

/-- Slot-parametric `RunSlotEnvs` bundle; definitionally equal (`rfl`) to
`ElfSlicesPqOomHole3Cut.binaryKitRunSlotEnvsExact W A B InitEnv DecPkEnv` when instantiated at
`EncSlot := fun {_M} A B => cliEncryptBinaryKitSlotEnvExact W A B` and
`DecSigSlot := fun {_M} A B => cliDecryptSignalBinaryKitSlotEnvExact W A B`. -/
noncomputable def hmx_binaryKitRunSlotEnvsSlotOf {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := EncSlot A B
  decryptSignal := DecSigSlot A B
  initiate := InitEnv
  decryptPrekey := DecPkEnv

/-- Mode-dispatched `CliRunCalleeEnvs` bundle parametric in the `W1`/`W2` slot families `EncSlot`
and `DecSigSlot`, keeping `initEnv` at `(mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv`,
`pksmEnv` at `PksmCanonSliceEnv`, and wrapping the named `cliDecPkCanonSlotEnvExact X W` directly on
`.recv` (`3#8 :: rest` prekey arm). -/
noncomputable def mkBinaryKitRealCalleeEnvsSlotOf [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : CliRunCalleeEnvs where
  initEnv := (mkBinaryKitRealCalleeEnvsFixed img S X W g).initEnv
  encEnv := match g.c with
    | .send _ => fun evs =>
      ∃ (M : AllocCostModel) (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
        w1R.repAlloc = A.repAlloc ∧
        W1BinarySendDom g.c g.i w1R ∧
        EncSlot A w1R.B w1R.x evs
    | _ => fun _ => False
  decSigEnv := match g.c with
    | .recv _ => fun evs =>
      ∃ (M : AllocCostModel) (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
        w2R.repAlloc = A.repAlloc ∧
        W2BinaryWhisperDom g.c g.i w2R ∧
        DecSigSlot A w2R.B w2R.x evs
    | _ => fun _ => False
  pksmEnv := PksmCanonSliceEnv
  decPkEnv := match g.c with
    | .recv peerV => fun evs =>
      ∃ (meV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
        g.i.stdin = 3#8 :: rest ∧
        pksmParse rest = some pm ∧
        pm.message.ciphertext.length ≤ msgCapBytes ∧
        cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm) evs
    | _ => fun _ => False

/-- Whole-`signal_session::run` binary-kit allocator trace predicate at
`mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot`. -/
noncomputable abbrev realCliRunBinaryKitEnvOfSlot [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) : List AllocEvent → Prop :=
  CliRunBinaryEnv cliIo.rd (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g)
    sessionCapBytes g

/-- Whole-`main` binary-kit allocator trace predicate at
`mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot`. -/
noncomputable abbrev realCliMainBinaryKitEnvOfSlot [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) : List AllocEvent → Prop :=
  RealCliMainBinaryEnvOf (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W) i

/-! ## 2. Private Non-`OverCapFile` & Input-Length Helpers -/

private theorem hmx_send_stdin_length_le_msgCapBytes {g : RunCall} {peerV : AddrV}
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV) :
    g.i.stdin.length ≤ msgCapBytes := by
  have hin_stdin : g.i.stdin.length ≤ stdinCapBytes := by
    simpa [hc, inputOf, CallV.tag] using hin
  have hcap_le : stdinCapBytes ≤ msgCapBytes := by
    unfold stdinCapBytes msgCapBytes
    decide
  exact Nat.le_trans hin_stdin hcap_le

private theorem hmx_preEnv_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i) :
    PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
      PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
  funext evs
  unfold PreEnv cliRunCalleesEnvs
  dsimp only
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi)]

private theorem hmx_init1Env_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i)
    (me : MeAtDispatch) (peerV : AddrV) (dir : List (BitVec 8)) :
    Init1Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g me peerV dir =
      Init1Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g me peerV dir := by
  funext evs
  cases me with
  | none => rfl
  | some _ _ =>
    unfold Init1Env cliRunCalleesEnvs
    dsimp only
    rw [readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_idKey hi dir)]

private theorem hmx_init2Env_fixed_eq_plain {P : PEParams} {g : RunCall}
    (hi : CliPqxdhInputs P g.i) (d1 : Init1Data) :
    Init2Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g d1 =
      Init2Env (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g d1 := by
  let cF := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  let cP := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)
  have hreg : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "registration-id") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_regId hi d1.dir)
  have hspk : cF.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") =
      cP.readFile (runFiles g.i) (d1.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") :=
    readFileRuleEnvFixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_spk hi d1.dir)
  have hkpk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "kyber-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_kpk hi d1.dir)
  have hopk : cF.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") =
      cP.bundleRead (runFiles g.i) d1.dir (utf8 "one-time-pre-key") :=
    bundleReadEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_bundle_opk hi d1.dir)
  have hsid : cF.splitId = cP.splitId := rfl
  have hssg : cF.splitSigned = cP.splitSigned := rfl
  have hopkOk : ∀ bs, R1bStepOpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepOpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepOpkOkEnv; rw [hopk, hsid]
  have hopkErr : R1bStepOpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepOpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepOpkErrEnv; rw [hopk, hsid]
  have hst3 : ∀ spkKey kpkKey, Init2Stage3Env cF (runFiles g.i) d1.dir spkKey kpkKey =
      Init2Stage3Env cP (runFiles g.i) d1.dir spkKey kpkKey := by
    intro spkKey kpkKey; funext evs; unfold Init2Stage3Env
    rw [hopk, hopkErr, hsid]; simp only [hopkOk]
  have hkpkOk : ∀ bs, R1bStepKpkOkEnv cF (runFiles g.i) d1.dir bs =
      R1bStepKpkOkEnv cP (runFiles g.i) d1.dir bs := by
    intro bs; funext evs; unfold R1bStepKpkOkEnv; rw [hkpk, hssg]
  have hkpkErr : R1bStepKpkErrEnv cF (runFiles g.i) d1.dir =
      R1bStepKpkErrEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold R1bStepKpkErrEnv; rw [hkpk]; simp only [hkpkOk]
  have hst2 : ∀ spkKey, Init2Stage2Env cF (runFiles g.i) d1.dir spkKey =
      Init2Stage2Env cP (runFiles g.i) d1.dir spkKey := by
    intro spkKey; funext evs; unfold Init2Stage2Env
    rw [hkpk, hkpkErr]; simp only [hkpkOk, hst3]
  have hafter : Init2AfterRegOkEnv cF (runFiles g.i) d1.dir =
      Init2AfterRegOkEnv cP (runFiles g.i) d1.dir := by
    funext evs; unfold Init2AfterRegOkEnv
    dsimp only
    rw [hspk, hssg]; simp only [hst2]
  funext evs
  change Init2Env cF g d1 evs = Init2Env cP g d1 evs
  unfold Init2Env
  dsimp only
  rw [hreg, hafter]

/-! ## 3. Per-Slot Containment Helpers and Whole-`run` Exact Inclusion -/

private theorem hmx_w1_encSlot_sub_slotOf [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (g : RunCall) (meG : AddrGhost) (peerV : AddrV)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .send peerV)
    {evs : List AllocEvent}
    (hevs : EncSlot A B (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64) evs) :
    (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv evs := by
  let w1R : W1BinarySendParams :=
    ⟨A.repAlloc, B, r2PeerGhost0 peerV, r2EncGhost g (r2PeerGhost0 peerV) meG 0#64⟩
  have hptext : g.i.stdin.length ≤ msgCapBytes := hmx_send_stdin_length_le_msgCapBytes hin hc
  have hdom : W1BinarySendDom g.c g.i w1R := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨rfl, rfl, rfl, hptext, rfl⟩
  dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
  rw [hc]
  exact ⟨M, A, w1R, rfl, hc ▸ hdom, hevs⟩

private theorem hmx_w2_decSigSlot_sub_slotOf [LibsignalPlacement] {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (g : RunCall) (meG : AddrGhost) (peerV : AddrV) (rest : List (BitVec 8)) (m : SignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 2#8 :: rest)
    (htr : SignalMessage.tryFrom protoSignalCodec rest = .ok m)
    {evs : List AllocEvent}
    (hevs : DecSigSlot A B (r3aDecSigGhost0 g peerV meG m) evs) :
    (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv evs := by
  let x := r3aDecSigGhost0 g peerV meG m
  let w2R : W2BinaryWhisperParams := ⟨A.repAlloc, B, x.peer, x⟩
  have hct_rest : m.ciphertext.length ≤ rest.length :=
    (signalMessage_tryFrom_lengths_le htr).2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : m.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  have hdom : W2BinaryWhisperDom g.c g.i w2R := by
    intro pAddr hpAddr
    rw [hc] at hpAddr
    injection hpAddr with hpEq
    subst hpEq
    exact ⟨rfl, rfl, rfl, hct_cap, rfl⟩
  dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
  rw [hc]
  exact ⟨M, A, w2R, rfl, hc ▸ hdom, hevs⟩

private theorem hmx_w4_decPkCanonSlot_sub_slotOf [LibsignalPlacement]
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : S.pksmParse rest = some pm)
    (hS_pksm : S.pksmParse = pksmParse)
    {evs : List AllocEvent}
    (hevs : cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm) evs) :
    (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv evs := by
  have hpk' : pksmParse rest = some pm := hS_pksm ▸ hpk
  have hct_rest : pm.message.ciphertext.length ≤ rest.length :=
    (pksmParse_lengths_le hpk').2.2.1
  have hrest_cap : rest.length ≤ msgCapBytes :=
    recv_rest_length_le_msgCapBytes hin hc hst
  have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
    Nat.le_trans hct_rest hrest_cap
  dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
  rw [hc]
  exact ⟨meV, rest, pm, hst, hpk', hct_cap, hevs⟩

/-- Parametric whole-`run` `RunEnv` to `realCliRunBinaryKitEnvOfSlot` inclusion over arbitrary
`EncSlot`, `DecSigSlot`, `InitEnv`, `DecPkEnv`, and `PksmTryFromEnv`. -/
theorem hmx_runEnvSlotOf_sub_runBinaryKitEnvOfSlot_of_slots [LibsignalPlacement]
    {M : AllocCostModel}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hinit3 : ∀ peerV dir d2 evs, g.c = .init peerV dir → d2.dir = dir →
      d2.peerV = peerV → d2.peerG.val = addrValOf peerV →
      d2.spkSigPtr ≠ 0 → d2.kpkSigPtr ≠ 0 → d2.kpkPtr ≠ 0 →
      InitEnv (r1cInitGhost g d2 0#64) evs →
      (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv evs)
    (hrecvP_pksm : ∀ peerV rest evs, g.c = .recv peerV → g.i.stdin = 3#8 :: rest →
      PksmTryFromEnv (r3bPksmGhost rest) evs →
      (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).pksmEnv rest evs)
    (hrecvP_slot : ∀ (meV : AddrV) (_meG : AddrGhost) peerV rest pm evs, g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      DecPkEnv (r3bDecPkGhost g meV peerV pm) evs →
      (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B InitEnv DecPkEnv)
          PksmTryFromEnv S)
        g evs →
      realCliRunBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W g evs :=
  runEnv_to_cliRunBinaryEnv_of_slots
    (fun _ hp =>
      preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
        (Eq.mp (congrFun (hmx_preEnv_fixed_eq_plain hi) _) hp))
    (fun me peerV dir _ _ h1 =>
      init1Env_sub_r1bFileStepEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl g me peerV dir (Eq.mp (congrFun (hmx_init1Env_fixed_eq_plain hi me peerV dir) _) h1))
    (fun _ _ d1 _ _ hd1 h2 =>
      hd1 ▸ init2Env_sub_r1bBinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd))
        rfl rfl rfl rfl g d1 (Eq.mp (congrFun (hmx_init2Env_fixed_eq_plain hi d1) _) h2))
    (fun peerV dir d2 _ hc hd2 hpv hpval hspk hkpkS hkpkP h3 =>
      r1cInit3Env_sub_r1cEnv (hinit3 peerV dir d2 · hc hd2 hpv hpval hspk hkpkS hkpkP) h3)
    (fun _me peerV _ hc hs =>
      r2SendEnv_sub_r2Env
        (fun _ meG _evs _hme he =>
          hmx_w1_encSlot_sub_slotOf EncSlot DecSigSlot img S X W A B g meG peerV hin hc he)
        (fun meV f m heq =>
          w1_send_out_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc)
        (fun meV f m heq =>
          w1_send_outPk_serialized_le_sessionCapBytes X W g peerV meV f m hin hc heq hS_enc) hs)
    (fun _me peerV rest _ hc hst hrw =>
      r3aRecvWEnv_sub_r3aBinaryEnv
        (fun _ meG m _evs _hme htr hd =>
          hmx_w2_decSigSlot_sub_slotOf EncSlot DecSigSlot img S X W A B g meG peerV rest m hin hc
            hst htr hd) hrw)
    (fun _me peerV rest _ hc hst hrp =>
      r3bRecvPEnv_sub_r3bEnv
        (hrecvP_pksm peerV rest · hc hst)
        (fun meV meG pm evs _hme hp hd => hrecvP_slot meV meG peerV rest pm evs hc hst hp hd) hrp)

/-- Whole-`run` `RunEnv` inclusion at `hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
(realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W)` and
`CanonicalOrFallbackPksmEnv FallbackEnv` under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`.

Instantiating `EncSlot` at `cliEncryptBinaryKitSlotEnvExact W` and `DecSigSlot` at
`cliDecryptSignalBinaryKitSlotEnvExact W` makes the `RunSlotEnvs` argument definitionally equal to
`ElfSlicesPqOomHole3Cut.binaryKitRunSlotEnvsExact`. -/
theorem hmx_runEnvExact_sub_runBinaryKitEnvOfSlot [LibsignalPlacement]
    {M : AllocCostModel}
    {FallbackEnv : PksmGhost → List AllocEvent → Prop}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
          (CanonicalOrFallbackPksmEnv FallbackEnv)
          S)
        g evs →
      realCliRunBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W g evs :=
  hmx_runEnvSlotOf_sub_runBinaryKitEnvOfSlot_of_slots EncSlot DecSigSlot img S X W A B hi hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
        ⟨w, hx, hF, hspqr, hgv, halice,
          Eq.mp
            (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx)) _)
            hslotF⟩)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalOrFallback_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      hmx_w4_decPkCanonSlot_sub_slotOf EncSlot DecSigSlot img S X W g meV peerV rest pm
        hin hc hst hpk hS_pksm hd)
    hS_enc

/-- Variant of `hmx_runEnvExact_sub_runBinaryKitEnvOfSlot` for any `PksmTryFromEnv` reducing to
`PksmCanonSliceEnv x.bytes` on canonical outer `PreKeyMessageFields`. -/
theorem hmx_runEnvExact_sub_runBinaryKitEnvOfSlot_of_pksmCanon [LibsignalPlacement]
    {M : AllocCostModel}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    (EncSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M' : AllocCostModel},
      RustCliAllocBudget M' → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    {g : RunCall}
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hpksm_canon : ∀ (x : PksmGhost) (evs : List AllocEvent),
      (∃ m : PreKeyMessageFields, x.bytes = m.bytes) →
      PksmTryFromEnv x evs → PksmCanonSliceEnv x.bytes evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : S.pksmParse = pksmParse := by rfl) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (hmx_binaryKitRunSlotEnvsSlotOf EncSlot DecSigSlot A B
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
          PksmTryFromEnv
          S)
        g evs →
      realCliRunBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W g evs :=
  hmx_runEnvSlotOf_sub_runBinaryKitEnvOfSlot_of_slots EncSlot DecSigSlot img S X W A B hi hin
    (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
      w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2 hparse hc hpv hpval
        ⟨w, hx, hF, hspqr, hgv, halice,
          Eq.mp
            (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi (congrArg (·.F) hx)) _)
            hslotF⟩)
    (fun peerV rest _ hc hst hpk =>
      pksmCanonicalGuard_sub_binaryKit img S X W g peerV rest hi hparse hc hst rfl
        (hpksm_canon (r3bPksmGhost rest) _) hpk)
    (fun meV _ peerV rest pm _ hc hst hpk hd =>
      hmx_w4_decPkCanonSlot_sub_slotOf EncSlot DecSigSlot img S X W g meV peerV rest pm
        hin hc hst hpk hS_pksm hd)
    hS_enc

/-! ## 4. Whole-`main` `FitsEnv` Statement Proposition -/

/-- Whole-`main` `FitsEnv fineCostModel cliBudgetLimits fineCostModel.init` proposition on
`realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i` for all `CliPqxdhInputs ⟨W.C, W.Q⟩ i`
(discharged parametrically in `CliKitEnvFitsExact`). -/
def realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
      (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i)

end LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
