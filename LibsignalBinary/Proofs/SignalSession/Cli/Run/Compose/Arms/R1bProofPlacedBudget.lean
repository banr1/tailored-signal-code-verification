/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Relocatable Arm `R1b` Proof (`run_hop_init2_placed_ok`)

Defines the prefix-closed stage envelopes (`Init2Stage4Env`, `Init2Stage3Env`, `Init2Stage2Env`,
`Init2AfterRegOkEnv`, `Init2Env`) and proves `r1b_step_init2_27bc_placed`,
`run_hop_init2_placed_ok`, and `run_hop_init2_of_slots_placed_ok` on Block `579` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Wire (pkBytesOf)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitId splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall blockingAncestorF cliIo cliRd ownedBytes readViewF sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtInit1Placed AtInit2Placed AtRunEntryPlaced Init1Data Init2Data PanicK RejectKind RunNeeds
   RunSem r1b_CodeOk r1b_OkCtxPlaced r1b_StackBounds r1b_invCoreBase_placed r1b_none_kpk_deser
   r1b_none_spk_deser r1b_opkStage3At r1b_spkBytesOf r1b_stackBounds_of_placed readBundleV runFiles
   runFsp runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkDeserialize)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv pathEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
  (R1bDeserCloneErrEnv R1bDeserCloneOkEnv r1b_step_deser_clone_placed_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudget
  (r1b_step_tail_25f4_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
  (r1b_step_kpk_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv r1b_step_opk_placed_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudget
  (r1b_step_reg_spk_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget (RunHopInit2Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetAux
  (r1b_step_init2_27bc_placed_aux)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget (init2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget
  (kemDeserializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)

/-! ## Prefix-Closed Stage Envelopes and `Init2Env` -/

/-- Success-path allocation-event envelope of `r1b_step_kpk_placed`: `bundleRead` for `"kyber-pre-key"` followed by `split_signed` on `kpkBs`. -/
def R1bStepKpkOkEnv (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir kpkBs : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (cEnvs.bundleRead files dir (utf8 "kyber-pre-key")) (cEnvs.splitSigned kpkBs)

example (files : FsFiles) :
    R1bStepKpkOkEnv
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      files [] [] [] :=
  Or.inl rfl

/-- Error-path allocation-event envelope of `r1b_step_kpk_placed`: `bundleRead` failure or `splitSigned kpkBs = none`, followed by `FreeOnlyEvs`. -/
def R1bStepKpkErrEnv (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
  | .error () => SeqEnv (cEnvs.bundleRead files dir (utf8 "kyber-pre-key")) FreeOnlyEvs evs
  | .ok kpkBs =>
      splitSigned kpkBs = none ∧
      SeqEnv (R1bStepKpkOkEnv cEnvs files dir kpkBs) FreeOnlyEvs evs

example :
    R1bStepKpkErrEnv
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      (fun _ => some .dir) [] [] := by
  unfold R1bStepKpkErrEnv
  have hrd :
      cliIo.rd ((fun _ => some .dir) : FsFiles) ([] ++ [0x2f#8] ++ utf8 "kyber-pre-key") =
        .error () := by
    unfold cliIo cliRd readViewF blockingAncestorF
    dsimp only
    generalize List.find? _ _ = o
    cases o <;> rfl
  rw [hrd]
  exact Or.inl rfl

/-- Allocation-event envelope from `0x24ec` through `0x28f0` (Stages 4a, 4b, and `0x27bc → 0x28f0`). -/
def Init2Stage4Env (spkKey kpkKey : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match PublicKey.deserialize spkKey with
  | .error _ => FreeOnlyEvs evs
  | .ok _ =>
      evs = rustAllocEvents 64 1 ∨
      evs = rustAllocEvents 64 1 ++
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.KemDeserialize.SpecBudget.kemDeserializeEvents kpkKey ∨
      match kemPkDeserialize kpkKey with
      | .ok _ => SeqEnv (R1bDeserCloneOkEnv kpkKey) FreeOnlyEvs evs
      | _ => R1bDeserCloneErrEnv spkKey kpkKey evs

example (spkKey kpkKey : List (BitVec 8)) : ∃ evs, Init2Stage4Env spkKey kpkKey evs := by
  unfold Init2Stage4Env
  split
  · exact ⟨[], fun _ h => nomatch h⟩
  · exact ⟨rustAllocEvents 64 1, Or.inl rfl⟩

/-- Allocation-event envelope from `0x12dc` through `0x28f0` (Stage 3 `one-time-pre-key` and Stage 4). -/
def Init2Stage3Env (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir spkKey kpkKey : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  cEnvs.bundleRead files dir (utf8 "one-time-pre-key") evs ∨
  R1bStepOpkErrEnv cEnvs files dir evs ∨
  match cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
  | .error () => False
  | .ok [] =>
      SeqEnv (R1bStepOpkOkEnv cEnvs files dir []) (Init2Stage4Env spkKey kpkKey) evs
  | .ok (b :: bs) =>
      SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key"))
        (cEnvs.splitId (b :: bs)) evs ∨
      match splitId (b :: bs) with
      | none => False
      | some (_, opkKey) =>
          match PublicKey.deserialize opkKey with
          | .error _ => False
          | .ok _ =>
              SeqEnv (R1bStepOpkOkEnv cEnvs files dir (b :: bs))
                (Init2Stage4Env spkKey kpkKey) evs

example (files : FsFiles) :
    Init2Stage3Env
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      files [] [] [] [] :=
  Or.inl rfl

/-- Allocation-event envelope from `0x1260` through `0x28f0` (Stage 2 `kyber-pre-key` and Stages 3–4). -/
def Init2Stage2Env (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir spkKey : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  cEnvs.bundleRead files dir (utf8 "kyber-pre-key") evs ∨
  R1bStepKpkErrEnv cEnvs files dir evs ∨
  match cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
  | .error () => False
  | .ok kpkBs =>
      R1bStepKpkOkEnv cEnvs files dir kpkBs evs ∨
      match splitSigned kpkBs with
      | none => False
      | some (_, kpkKey, _) =>
          SeqEnv (R1bStepKpkOkEnv cEnvs files dir kpkBs)
            (Init2Stage3Env cEnvs files dir spkKey kpkKey) evs

example (files : FsFiles) :
    Init2Stage2Env
      ⟨fun _ _ e => e = [], fun _ _ _ e => e = [], fun _ _ _ e => e = [],
       fun _ e => e = [], fun _ e => e = []⟩
      files [] [] [] :=
  Or.inl rfl

/-- Allocation-event envelope from `0x0c6c` (`signed-pre-key` read after valid 4-byte `registration-id`) through `0x28f0`. -/
def Init2AfterRegOkEnv (cEnvs : RunCalleesEnvs) (files : FsFiles)
    (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  let spkPath := dir ++ [0x2f#8] ++ utf8 "signed-pre-key"
  PathEnv dir (utf8 "signed-pre-key") evs ∨
  SeqEnv (PathEnv dir (utf8 "signed-pre-key")) (cEnvs.readFile files spkPath) evs ∨
  match cliIo.rd files spkPath with
  | .error () =>
      SeqEnv (SeqEnv (PathEnv dir (utf8 "signed-pre-key")) (cEnvs.readFile files spkPath))
        (SeqEnv (fun e => e = [AllocEvent.alloc 22]) FreeOnlyEvs) evs
  | .ok spkBs =>
      let spkRd :=
        SeqEnv (SeqEnv (PathEnv dir (utf8 "signed-pre-key")) (cEnvs.readFile files spkPath))
          FreeOnlyEvs
      SeqEnv spkRd (cEnvs.splitSigned spkBs) evs ∨
      match splitSigned spkBs with
      | none => SeqEnv (SeqEnv spkRd (cEnvs.splitSigned spkBs)) FreeOnlyEvs evs
      | some (_, spkKey, _) =>
          SeqEnv (SeqEnv spkRd (cEnvs.splitSigned spkBs))
            (Init2Stage2Env cEnvs files dir spkKey) evs

example (c0 : RunCalleesEnvs) (files : FsFiles) :
    Init2AfterRegOkEnv c0 files [] (pathEvents [] (utf8 "signed-pre-key")) :=
  Or.inl rfl

/-- Full prefix-closed allocation-event envelope for Arm `R1b` (`R+0x074c → R+0x28f0` or `RejectKPlacedEnv`). -/
def Init2Env (cEnvs : RunCalleesEnvs) (g : RunCall) (d : Init1Data)
    (evs : List AllocEvent) : Prop :=
  let files := runFiles g.i
  let dir := d.dir
  let regPath := dir ++ [0x2f#8] ++ utf8 "registration-id"
  PathEnv dir (utf8 "registration-id") evs ∨
  SeqEnv (PathEnv dir (utf8 "registration-id")) (cEnvs.readFile files regPath) evs ∨
  match cliIo.rd files regPath with
  | .error () =>
      SeqEnv (SeqEnv (PathEnv dir (utf8 "registration-id")) (cEnvs.readFile files regPath))
        (SeqEnv (fun e => e = [AllocEvent.alloc 22]) FreeOnlyEvs) evs
  | .ok regBs =>
      let regRd :=
        SeqEnv (SeqEnv (PathEnv dir (utf8 "registration-id")) (cEnvs.readFile files regPath))
          FreeOnlyEvs
      if regBs.length = 4 then
        SeqEnv regRd (Init2AfterRegOkEnv cEnvs files dir) evs
      else
        SeqEnv regRd (SeqEnv (fun e => e = [AllocEvent.alloc 14]) FreeOnlyEvs) evs

example (c0 : RunCalleesEnvs) (g : RunCall) (d : Init1Data) :
    Init2Env c0 g d (pathEvents d.dir (utf8 "registration-id")) :=
  Or.inl rfl

/-! ## Final Bundle Assembly (`0x27bc → 0x28f0`) and `run_hop_init2_placed_ok` -/

/-- Final straight-line block (`0x27bc → 0x28f0`) assembling `cliBundleAt` (`[0x4d0..0x590)`), `protocolAddressAt A.repAlloc d.meG` (`[0x320..0x340)`), and the `AtInit2Placed` ABI registers. -/
theorem r1b_step_init2_27bc_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {spk : PublicKey} {kpk : List (BitVec 8)}
    {spkSig kpkSig : List (BitVec 8)}
    {spkSigPtr kpkSigPtr kpkBuf : BitVec 64}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {spkId kpkId v11c : BitVec 32}
    {opk : Option (BitVec 32 × PublicKey)}
    {c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    {w0e0 w0e4 c9 : BitVec 32} {c13 : BitVec 16} {w15 c23 : BitVec 64} {c31 : BitVec 8}
    {kpkPtr v130 kpkCap spkPtr spkCap regCap regPtr : BitVec 64}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x27bc)
    (hbundle : readBundleV (runFiles g.i) d.dir d.peerV.device = some {
      idKey := d.idKey, regId := ofLe32 r0 r1 r2 r3, device := d.peerV.device,
      spkId := spkId, spk := spk, spkSig := spkSig,
      kpkId := kpkId, kpk := kpk, kpkSig := kpkSig, opk := opk
    })
    (hspk_bytes : spk.bytes.toList = r1b_spkBytesOf spkW0 spkW8 spkW12 spkW16 spkW24)
    (hptrs : spkSigPtr ≠ 0 ∧ kpkSigPtr ≠ 0 ∧ kpkBuf ≠ 0)
    (hlens : spkSig.length = 64 ∧ kpkSig.length = 64 ∧ kpk.length = 1568)
    (hopk_pk : ∀ p, opk = some p → v11c = p.1 ∧
      p.2.bytes.toList = pkBytesOf c0 c1 c2 c3 c4 c5 c6
        (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32)
    (hx25 : s.readReg64 (.gpr 25#5) = (if opk.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = (if opk.isSome then 1#32 else 0#32).zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hnext : ∀ (s2 : State) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
        A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
        A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
          c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 ∗
        ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ 64#64) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ v130) ∗
        ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
        ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  exact r1b_step_init2_27bc_placed_aux hok hbundle hspk_bytes hptrs hlens hopk_pk
    hx23 hx24 hx25 hx26 hx28 hnext

private theorem seqEnv_append_eq {E₁ E₂ : List AllocEvent → Prop} {e₁ e₂ evs : List AllocEvent}
    (heq : evs = e₁ ++ e₂) (h₁ : E₁ e₁) (h₂ : E₂ e₂) :
    SeqEnv E₁ E₂ evs :=
  Or.inr ⟨e₁, e₂, heq, h₁, h₂⟩

private theorem fitsEnv_after {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E E' : List AllocEvent → Prop} (p : List AllocEvent)
    (h : FitsEnv M lim st E) (hsub : ∀ sfx, E' sfx → E (p ++ sfx)) :
    FitsEnv M lim (M.stepEvents p st) E' :=
  fun sfx hs => ((fitsEvents_append M lim p sfx st).mp (h (p ++ sfx) (hsub sfx hs))).2

private theorem fitsEvents_after {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (p sfx : List AllocEvent)
    (h : FitsEnv M lim st E) (hmem : E (p ++ sfx)) :
    FitsEvents M lim (M.stepEvents p st) sfx :=
  ((fitsEvents_append M lim p sfx st).mp (h (p ++ sfx) hmem)).2

private def mkEnvAt {M : AllocCostModel} (E : List AllocEvent → Prop) (st : M.σ) :
    StoresGhost → RejectKind → M.σ → Prop :=
  fun _ _ st' => ∃ evs, E evs ∧ st' = M.stepEvents evs st

private theorem envAt_of_mem {M : AllocCostModel} {E : List AllocEvent → Prop} {st : M.σ}
    {evs : List AllocEvent} (h : E evs) :
    mkEnvAt E st StoresGhost.opened .postDispatch (M.stepEvents evs st) :=
  ⟨evs, h, rfl⟩

private theorem rej_lift [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {E E' : List AllocEvent → Prop} {st : M.σ} (p : List AllocEvent)
    {g : RunCall} {s0 : State} {resStack : Nat} {Q Qp : State → SepProp → Prop}
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt E st) g s0 resStack Q Qp)
    (hsub : ∀ sfx, E' sfx → E (p ++ sfx)) :
    RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt E' (M.stepEvents p st)) g s0 resStack Q Qp :=
  fun sf st' g' rk hAt ⟨sfx, hsfx, hst'⟩ =>
    hrej sf st' g' rk hAt ⟨p ++ sfx, hsub sfx hsfx, by rw [hst', M.stepEvents_append]⟩

private theorem init2Env_of_afterRegOk {cEnvs : RunCalleesEnvs} {g : RunCall} {d : Init1Data}
    {evsRegP evsRegRd evsFreeR regBs sfx : List _}
    (hp : PathEnv d.dir (utf8 "registration-id") evsRegP)
    (hok_r : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hrd : cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") evsRegRd)
    (hfoR : FreeOnlyEvs evsFreeR)
    (heq4 : regBs.length = 4)
    (hafter : Init2AfterRegOkEnv cEnvs (runFiles g.i) d.dir sfx) :
    Init2Env cEnvs g d ((evsRegP ++ evsRegRd ++ evsFreeR) ++ sfx) := by
  unfold Init2Env
  simp only [hok_r, heq4, ↓reduceIte]
  exact Or.inr (Or.inr
    (SeqEnv.append
      (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hp hrd) hfoR)
      hafter))

private theorem init2Stage4Env_of_deserCloneErr {spkKey kpkKey : List (BitVec 8)}
    {evs : List AllocEvent} (herr : R1bDeserCloneErrEnv spkKey kpkKey evs) :
    Init2Stage4Env spkKey kpkKey evs := by
  unfold Init2Stage4Env
  cases hsd : PublicKey.deserialize spkKey with
  | error e =>
      unfold R1bDeserCloneErrEnv at herr
      rw [hsd] at herr
      exact herr
  | ok spk =>
      refine Or.inr (Or.inr ?_)
      split
      · rename_i kpk hk
        unfold R1bDeserCloneErrEnv at herr
        rw [hsd, hk] at herr
        exact False.elim herr
      · exact herr

/-- Budget-threaded relocatable Arm `R1b` proof from `AtInit1Placed` (`R+0x074c`) to `AtInit2Placed` (`R+0x28f0`) under `FitsEnv M lim st (Init2Env cEnvs g d1)`. -/
theorem run_hop_init2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat} :
    RunHopInit2Placed (LibsignalCodeRoLoaded lsmpl)
      A lim cEnvs sEnvs (Init2Env cEnvs) H B S needs resStack := by
  intro g st d1 s0 s1 Q Qp hh hc hdrop hres hres64 he hi1 hfit hpanic hrej hnext
  have hres' :
      runNeed B (CryptoVerification.SignalSession.Cli.RunCompose.slotsOfPlaced A.repAlloc S needs) ≤
        resStack := hres
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres' hres64
  have hok0 : r1b_OkCtxPlaced r1b_CodeOk S g d1 s0 s1 0x074c := r1b_OkCtxPlaced.of_init1 he hi1
  have hrej0 : RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt (Init2Env cEnvs g d1) st)
      g s0 resStack Q Qp := hrej
  refine r1b_step_reg_spk_placed hh hc hdrop hbnd he hok0 hi1.x28
    (hfit.mono fun _ hp => Or.inl hp)
    (fun evsRegP hp => fitsEnv_after evsRegP hfit fun _ hrd =>
      Or.inr (Or.inl (SeqEnv.append hp hrd)))
    (fun evsRegP evsRegRd hp herr hrd =>
      fitsEvents_after (evsRegP ++ evsRegRd) [AllocEvent.alloc 22] hfit (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hp hrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFree hp herr hrd hfo =>
      envAt_of_mem (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hp hrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR hne =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR) [AllocEvent.alloc 14] hfit (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (SeqEnv.append
            (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsFree hp hok_r hrd hfoR hne hfo =>
      envAt_of_mem (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR heq4 =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR) hfit fun _ hsp =>
        init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 (Or.inl hsp))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP hp hok_r hrd hfoR heq4 hsp =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) hfit fun sfx hsrd => by
        rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) ++ sfx =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++ (evsSpkP ++ sfx) by simp only [List.append_assoc]]
        exact init2Env_of_afterRegOk hp hok_r hrd hfoR heq4
          (Or.inr (Or.inl (SeqEnv.append hsp hsrd))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd hp hok_r hrd hfoR heq4 hsp hserr hsrd =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd)
        [AllocEvent.alloc 22] hfit (by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd) ++
              [AllocEvent.alloc 22] =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++
                ((evsSpkP ++ evsSpkRd) ++ [AllocEvent.alloc 22]) by simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
          exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hsp hsrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree
        hp hok_r hrd hfoR heq4 hsp hserr hsrd hfo =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            [AllocEvent.alloc 22] ++ evsFree =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ [AllocEvent.alloc 22] ++ evsFree) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hsp hsrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) hfit
        fun sfx hssp => by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx) by
            simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hsok]
          exact Or.inr (Or.inr (Or.inl
            (SeqEnv.append
              (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hsp hsrd) hfoS)
              hssp))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS hsnone hssp hfo2 =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            evsFreeS ++ evsSp ++ evsFree2 =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp ++ evsFree2) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; simp only [hsok, hsnone]
        exact Or.inr (Or.inr (Or.inr
          (SeqEnv.append
            (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
            hfo2)))))
    hpanic hrej0
    fun sf1 evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp
        r0 r1 r2 r3 regCap regPtr spkCap spkPtr spkBs spkKey spkSig spkId
        hp hrd hfoR hsp hsrd hfoS hssp hok1 hreg_rd hspk_rd hspk_sp
        hx10_1 hx27_1 hx2_1 hx26_1 hx28_1 => ?_
  let pfx1 := evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp
  have hlift1 : ∀ sfx, Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey sfx →
      Init2Env cEnvs g d1 (pfx1 ++ sfx) := fun sfx hs2 => by
    dsimp only [pfx1]
    rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx =
        (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx) by
      simp only [List.append_assoc]]
    refine init2Env_of_afterRegOk hp hreg_rd hrd hfoR rfl ?_
    unfold Init2AfterRegOkEnv; simp only [hspk_rd, hspk_sp]
    exact Or.inr (Or.inr (Or.inr
      (SeqEnv.append
        (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
        hs2)))
  have hfit1 := fitsEnv_after pfx1 hfit hlift1
  have hrej1 := rej_lift pfx1 hrej0 hlift1
  have hnext1 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx1 st)) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx1 evs st]
    exact hnext s2 (pfx1 ++ evs) d2 hi2 (hlift1 evs hevs)
  refine r1b_step_kpk_placed hh hc hdrop hbnd he hok1 hreg_rd hspk_rd hspk_sp
    hx10_1 hx27_1 hx2_1 hx26_1 hx28_1
    (hfit1.mono fun _ h => Or.inl h)
    (fun evsKpkBr evsFree herr hbr hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [herr]; exact SeqEnv.append hbr hfo))))
    (fun evsKpkBr kpkBs hok_k hbr =>
      fitsEnv_after evsKpkBr hfit1 fun _ hksp => by
        unfold Init2Stage2Env; rw [hok_k]
        exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr hksp))))
    (fun evsKpkBr kpkBs evsKpkSp evsFree hok_k hbr hnone hksp hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [hok_k]
        exact ⟨hnone, seqEnv_append_eq (by simp only [List.append_assoc])
          (SeqEnv.append hbr hksp) hfo⟩))))
    hpanic hrej1
    fun sf2 evsKpkBr evsKpkSp kpkCap kpkPtr kpkBs kpkKey kpkSig kpkId
        hbr hksp hok2 hkpk_rd hkpk_sp
        hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2 => ?_
  let pfx2 := evsKpkBr ++ evsKpkSp
  have hlift2 : ∀ sfx, Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey sfx →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey (pfx2 ++ sfx) := fun sfx hs3 => by
    unfold Init2Stage2Env; simp only [hkpk_rd, hkpk_sp]
    exact Or.inr (Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hbr hksp) hs3)))
  have hfit2 := fitsEnv_after pfx2 hfit1 hlift2
  have hrej2 := rej_lift pfx2 hrej1 hlift2
  have hnext2 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx2 evs]
    exact hnext1 s2 (pfx2 ++ evs) d2 hi2 (hlift2 evs hevs)
  refine r1b_step_opk_placed_env hh hc hdrop hbnd he hok2
    hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2
    (hfit2.mono fun _ h => Or.inl h)
    (fun evs_br opkBs hne hbr_o hok_o => by
      cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          exact fitsEnv_after evs_br hfit2 fun _ hsp_o => by
            unfold Init2Stage3Env; rw [hok_o]
            exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr_o hsp_o))))
    hpanic hrej2
    (fun evs herr => envAt_of_mem (Or.inr (Or.inl herr)))
    fun sf3 evs_opk opkBs opk v11c b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31
        hopk_ok hok3 hopk_rd hopk_sem hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 => ?_
  have hlift3 : ∀ sfx, Init2Stage4Env spkKey kpkKey sfx →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey (evs_opk ++ sfx) := fun sfx hs4 => by
    rcases hopk_sem with ⟨rfl, _⟩ | ⟨opkId, opkKey, opkPk, hne, _, hsp_o, hdes_o, _⟩
    · unfold Init2Stage3Env; rw [hopk_rd]
      exact Or.inr (Or.inr (SeqEnv.append hopk_ok hs4))
    · cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          unfold Init2Stage3Env; simp only [hopk_rd, hsp_o, hdes_o]
          exact Or.inr (Or.inr (Or.inr (SeqEnv.append hopk_ok hs4)))
  have hfit3 := fitsEnv_after evs_opk hfit2 hlift3
  have hrej3 := rej_lift evs_opk hrej2 hlift3
  have hnext3 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage4Env spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim
          (M.stepEvents evs (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st))))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append evs_opk evs]
    exact hnext2 s2 (evs_opk ++ evs) d2 hi2 (hlift3 evs hevs)
  refine r1b_step_deser_clone_placed_env (sEnvs := sEnvs) (needs := needs)
    hh hc hdrop hbnd hok3 hreg_rd hspk_rd hspk_sp hkpk_rd hkpk_sp hopk_rd hopk_sem
    hx23_3 hx24_3 hx25_3 hx27_3 hx28_3
    (fun spk hspk_d => hfit3 (rustAllocEvents 64 1) (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inl rfl))
    (fun spk hspk_d => fitsEvents_after (rustAllocEvents 64 1) (kemDeserializeEvents kpkKey) hfit3 (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inr (Or.inl rfl)))
    (fun spk kpk hspk_d hkpk_d =>
      fitsEvents_after (rustAllocEvents 64 1 ++ kemDeserializeEvents kpkKey) (rustAllocEvents 64 1)
        hfit3 (by
          unfold Init2Stage4Env; rw [hspk_d, hkpk_d]
          exact Or.inr (Or.inr (SeqEnv.inl (by
            unfold R1bDeserCloneOkEnv; simp only [List.append_assoc])))))
    hpanic hrej3
    (fun evs herr => envAt_of_mem (init2Stage4Env_of_deserCloneErr herr))
    fun sf4 evs_dc spk kpk spkSigPtr kpkSigPtr kpkBuf spkW0 spkW8 spkW12 spkW16 spkW24
        hDcOk hok4 hbundle hspk_bytes hptrs hlens hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 => ?_
  have ⟨spk', hsd⟩ : ∃ spk', PublicKey.deserialize spkKey = .ok spk' := by
    cases h : PublicKey.deserialize spkKey with
    | error e =>
        have hnone := r1b_none_spk_deser (dev := d1.peerV.device) hspk_rd hspk_sp h
        rw [hbundle] at hnone; cases hnone
    | ok v => exact ⟨v, rfl⟩
  have ⟨kpk', hkd⟩ : ∃ kpk', kemPkDeserialize kpkKey = .ok kpk' := by
    cases h : kemPkDeserialize kpkKey with
    | ok v => exact ⟨v, rfl⟩
    | _ =>
        have hnone := r1b_none_kpk_deser (dev := d1.peerV.device) hkpk_rd hkpk_sp
          (fun _ hk => by rw [h] at hk; cases hk)
        rw [hbundle] at hnone; cases hnone
  let fsp := runFsp s0
  let tailFrame : SepProp :=
    memRegion (fsp + 0x4d0#64) 48 ∗
      A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
      A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
      A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
      r1b_invCoreBase_placed A.repAlloc g d1 s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d1.dirCap d1.dirPtr (BitVec.ofNat 64 d1.dir.length) d1.dir ∗
      ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
      ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
      ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
      ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
      ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
      ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d1.ikW3) ∗
      ((fsp + 0x1a8#64) ↦₆₄ d1.ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ d1.peerV.device.zeroExtend 32) ∗
      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24
  let st4 := M.stepEvents evs_dc (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
  have htail := r1b_step_tail_25f4_placed
    (A := A) (lim := lim) (st := st4) (H := H) (resStack := resStack)
    (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
    (spkW0 := spkW0) (spkW8 := spkW8) (spkW16 := spkW16) (spkW24 := spkW24)
    (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
    (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
    (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
    (F := tailFrame)
    hh hbnd hok4 hopk_sem hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hpanic
    fun sf5 evs_tail c0 c1 c2 c3 c4 c5 c6 c9 c13 c23 c31
        hfo_tail hok5 hopk_pk hx23_5 hx24_5 hx25_5 hx26_5 hx28_5 => by
      have hStage4 : Init2Stage4Env spkKey kpkKey (evs_dc ++ evs_tail) := by
        unfold Init2Stage4Env; rw [hsd, hkd]
        exact Or.inr (Or.inr (SeqEnv.append hDcOk hfo_tail))
      have hstep := r1b_step_init2_27bc_placed
        (A := A) (lim := lim) (st := M.stepEvents evs_tail st4) (H := H) (resStack := resStack)
        (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
        (kpkPtr := kpkPtr) (v130 := kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
        (kpkCap := kpkCap) (spkPtr := spkPtr) (spkCap := spkCap)
        (regCap := regCap) (regPtr := regPtr)
        hok5 hbundle hspk_bytes hptrs hlens hopk_pk
        hx23_5 hx24_5 hx25_5 hx26_5 hx28_5
        (fun s2 d2 hi2 => by
          dsimp only [st4]
          rw [← M.stepEvents_append evs_dc evs_tail]
          exact hnext3 s2 (evs_dc ++ evs_tail) d2 hi2 hStage4)
      dsimp only [tailFrame, fsp, st4] at hstep ⊢
      exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep
  dsimp only [tailFrame, fsp, st4] at htail ⊢
  exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) htail


theorem run_hop_init2_of_slots_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds}
    {slots : CryptoVerification.SignalSession.Cli.RunSkeleton.RunSlots} {resStack : Nat}
    (hneed_eq : CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B slots =
      CryptoVerification.SignalSession.Cli.RunSkeleton.runNeed B
        (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfPlaced
          A lim sEnvs S needs))
    (hkem_eq : slots.kemDeserialize =
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfPlaced
        A lim sEnvs S needs).kemDeserialize) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget.RunHopInit2PlacedOf
      (LibsignalCodeRoLoaded lsmpl) A lim cEnvs (Init2Env cEnvs) H B S slots resStack := by
  intro g st d1 s0 s1 Q Qp hh hc hdrop hres_slots hres64 he hi1 hfit hpanic hrej hnext
  have hres : runNeed B (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfPlaced A lim sEnvs S needs) ≤ resStack :=
    hneed_eq ▸ hres_slots
  have hres' :
      runNeed B (CryptoVerification.SignalSession.Cli.RunCompose.slotsOfPlaced A.repAlloc S needs) ≤
        resStack := hres
  have hbnd : r1b_StackBounds B resStack := r1b_stackBounds_of_placed hres' hres64
  have hok0 : r1b_OkCtxPlaced r1b_CodeOk S g d1 s0 s1 0x074c := r1b_OkCtxPlaced.of_init1 he hi1
  have hrej0 : RejectKPlacedEnv r1b_CodeOk H A lim (mkEnvAt (Init2Env cEnvs g d1) st)
      g s0 resStack Q Qp := hrej
  refine r1b_step_reg_spk_placed hh hc hdrop hbnd he hok0 hi1.x28
    (hfit.mono fun _ hp => Or.inl hp)
    (fun evsRegP hp => fitsEnv_after evsRegP hfit fun _ hrd =>
      Or.inr (Or.inl (SeqEnv.append hp hrd)))
    (fun evsRegP evsRegRd hp herr hrd =>
      fitsEvents_after (evsRegP ++ evsRegRd) [AllocEvent.alloc 22] hfit (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hp hrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFree hp herr hrd hfo =>
      envAt_of_mem (by
        unfold Init2Env; dsimp only; rw [herr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hp hrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR hne =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR) [AllocEvent.alloc 14] hfit (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (SeqEnv.append
            (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsFree hp hok_r hrd hfoR hne hfo =>
      envAt_of_mem (by
        unfold Init2Env; simp only [hok_r, hne, ↓reduceIte]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append (SeqEnv.append hp hrd) hfoR)
            (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs hp hok_r hrd hfoR heq4 =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR) hfit fun _ hsp =>
        init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 (Or.inl hsp))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP hp hok_r hrd hfoR heq4 hsp =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) hfit fun sfx hsrd => by
        rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP) ++ sfx =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++ (evsSpkP ++ sfx) by simp only [List.append_assoc]]
        exact init2Env_of_afterRegOk hp hok_r hrd hfoR heq4
          (Or.inr (Or.inl (SeqEnv.append hsp hsrd))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd hp hok_r hrd hfoR heq4 hsp hserr hsrd =>
      fitsEvents_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd)
        [AllocEvent.alloc 22] hfit (by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd) ++
              [AllocEvent.alloc 22] =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++
                ((evsSpkP ++ evsSpkRd) ++ [AllocEvent.alloc 22]) by simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
          exact Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hsp hsrd) (SeqEnv.inl rfl)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFree
        hp hok_r hrd hfoR heq4 hsp hserr hsrd hfo =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            [AllocEvent.alloc 22] ++ evsFree =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ [AllocEvent.alloc 22] ++ evsFree) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; dsimp only; rw [hserr]
        exact Or.inr (Or.inr
          (seqEnv_append_eq (by simp only [List.append_assoc])
            (SeqEnv.append hsp hsrd) (SeqEnv.append rfl hfo)))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS =>
      fitsEnv_after (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) hfit
        fun sfx hssp => by
          rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx =
              (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS) ++ sfx) by
            simp only [List.append_assoc]]
          refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
          unfold Init2AfterRegOkEnv; dsimp only; rw [hsok]
          exact Or.inr (Or.inr (Or.inl
            (SeqEnv.append
              (seqEnv_append_eq (by simp only [List.append_assoc]) (SeqEnv.append hsp hsrd) hfoS)
              hssp))))
    (fun evsRegP evsRegRd evsFreeR regBs evsSpkP evsSpkRd evsFreeS spkBs evsSp evsFree2
        hp hok_r hrd hfoR heq4 hsp hsok hsrd hfoS hsnone hssp hfo2 =>
      envAt_of_mem (by
        rw [show evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++
            evsFreeS ++ evsSp ++ evsFree2 =
            (evsRegP ++ evsRegRd ++ evsFreeR) ++
              (evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp ++ evsFree2) by
          simp only [List.append_assoc]]
        refine init2Env_of_afterRegOk hp hok_r hrd hfoR heq4 ?_
        unfold Init2AfterRegOkEnv; simp only [hsok, hsnone]
        exact Or.inr (Or.inr (Or.inr
          (SeqEnv.append
            (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
            hfo2)))))
    hpanic hrej0
    fun sf1 evsRegP evsRegRd evsFreeR evsSpkP evsSpkRd evsFreeS evsSp
        r0 r1 r2 r3 regCap regPtr spkCap spkPtr spkBs spkKey spkSig spkId
        hp hrd hfoR hsp hsrd hfoS hssp hok1 hreg_rd hspk_rd hspk_sp
        hx10_1 hx27_1 hx2_1 hx26_1 hx28_1 => ?_
  let pfx1 := evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp
  have hlift1 : ∀ sfx, Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey sfx →
      Init2Env cEnvs g d1 (pfx1 ++ sfx) := fun sfx hs2 => by
    dsimp only [pfx1]
    rw [show (evsRegP ++ evsRegRd ++ evsFreeR ++ evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx =
        (evsRegP ++ evsRegRd ++ evsFreeR) ++ ((evsSpkP ++ evsSpkRd ++ evsFreeS ++ evsSp) ++ sfx) by
      simp only [List.append_assoc]]
    refine init2Env_of_afterRegOk hp hreg_rd hrd hfoR rfl ?_
    unfold Init2AfterRegOkEnv; simp only [hspk_rd, hspk_sp]
    exact Or.inr (Or.inr (Or.inr
      (SeqEnv.append
        (SeqEnv.append (SeqEnv.append (SeqEnv.append hsp hsrd) hfoS) hssp)
        hs2)))
  have hfit1 := fitsEnv_after pfx1 hfit hlift1
  have hrej1 := rej_lift pfx1 hrej0 hlift1
  have hnext1 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx1 st)) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx1 evs st]
    exact hnext s2 (pfx1 ++ evs) d2 hi2 (hlift1 evs hevs)
  refine r1b_step_kpk_placed hh hc hdrop hbnd he hok1 hreg_rd hspk_rd hspk_sp
    hx10_1 hx27_1 hx2_1 hx26_1 hx28_1
    (hfit1.mono fun _ h => Or.inl h)
    (fun evsKpkBr evsFree herr hbr hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [herr]; exact SeqEnv.append hbr hfo))))
    (fun evsKpkBr kpkBs hok_k hbr =>
      fitsEnv_after evsKpkBr hfit1 fun _ hksp => by
        unfold Init2Stage2Env; rw [hok_k]
        exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr hksp))))
    (fun evsKpkBr kpkBs evsKpkSp evsFree hok_k hbr hnone hksp hfo =>
      envAt_of_mem (Or.inr (Or.inl (by
        unfold R1bStepKpkErrEnv; rw [hok_k]
        exact ⟨hnone, seqEnv_append_eq (by simp only [List.append_assoc])
          (SeqEnv.append hbr hksp) hfo⟩))))
    hpanic hrej1
    fun sf2 evsKpkBr evsKpkSp kpkCap kpkPtr kpkBs kpkKey kpkSig kpkId
        hbr hksp hok2 hkpk_rd hkpk_sp
        hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2 => ?_
  let pfx2 := evsKpkBr ++ evsKpkSp
  have hlift2 : ∀ sfx, Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey sfx →
      Init2Stage2Env cEnvs (runFiles g.i) d1.dir spkKey (pfx2 ++ sfx) := fun sfx hs3 => by
    unfold Init2Stage2Env; simp only [hkpk_rd, hkpk_sp]
    exact Or.inr (Or.inr (Or.inr (SeqEnv.append (SeqEnv.append hbr hksp) hs3)))
  have hfit2 := fitsEnv_after pfx2 hfit1 hlift2
  have hrej2 := rej_lift pfx2 hrej1 hlift2
  have hnext2 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append pfx2 evs]
    exact hnext1 s2 (pfx2 ++ evs) d2 hi2 (hlift2 evs hevs)
  refine r1b_step_opk_placed_env hh hc hdrop hbnd he hok2
    hx25_2 hx28_2 hx26_2 hx27_2 hx9_2 hx10_2 hx8_2 hx23_2 hx24_2
    (hfit2.mono fun _ h => Or.inl h)
    (fun evs_br opkBs hne hbr_o hok_o => by
      cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          exact fitsEnv_after evs_br hfit2 fun _ hsp_o => by
            unfold Init2Stage3Env; rw [hok_o]
            exact Or.inr (Or.inr (Or.inl (SeqEnv.append hbr_o hsp_o))))
    hpanic hrej2
    (fun evs herr => envAt_of_mem (Or.inr (Or.inl herr)))
    fun sf3 evs_opk opkBs opk v11c b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31
        hopk_ok hok3 hopk_rd hopk_sem hx23_3 hx24_3 hx25_3 hx27_3 hx28_3 => ?_
  have hlift3 : ∀ sfx, Init2Stage4Env spkKey kpkKey sfx →
      Init2Stage3Env cEnvs (runFiles g.i) d1.dir spkKey kpkKey (evs_opk ++ sfx) := fun sfx hs4 => by
    rcases hopk_sem with ⟨rfl, _⟩ | ⟨opkId, opkKey, opkPk, hne, _, hsp_o, hdes_o, _⟩
    · unfold Init2Stage3Env; rw [hopk_rd]
      exact Or.inr (Or.inr (SeqEnv.append hopk_ok hs4))
    · cases opkBs with
      | nil => exact False.elim (hne rfl)
      | cons b bs =>
          unfold Init2Stage3Env; simp only [hopk_rd, hsp_o, hdes_o]
          exact Or.inr (Or.inr (Or.inr (SeqEnv.append hopk_ok hs4)))
  have hfit3 := fitsEnv_after evs_opk hfit2 hlift3
  have hrej3 := rej_lift evs_opk hrej2 hlift3
  have hnext3 : ∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2Placed r1b_CodeOk g d2 s0 s2 →
      Init2Stage4Env spkKey kpkKey evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim
          (M.stepEvents evs (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st))))
          g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝) := fun s2 evs d2 hi2 hevs => by
    rw [← M.stepEvents_append evs_opk evs]
    exact hnext2 s2 (evs_opk ++ evs) d2 hi2 (hlift3 evs hevs)
  refine LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget.r1b_step_deser_clone_of_kem_placed_env
    (sEnvs := sEnvs) (needs := needs)
    hh (hkem_eq ▸ hc.kemDeserialize) hdrop hbnd hok3 hreg_rd hspk_rd hspk_sp hkpk_rd hkpk_sp hopk_rd hopk_sem
    hx23_3 hx24_3 hx25_3 hx27_3 hx28_3
    (fun spk hspk_d => hfit3 (rustAllocEvents 64 1) (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inl rfl))
    (fun spk hspk_d => fitsEvents_after (rustAllocEvents 64 1) (kemDeserializeEvents kpkKey) hfit3 (by
      unfold Init2Stage4Env; rw [hspk_d]; exact Or.inr (Or.inl rfl)))
    (fun spk kpk hspk_d hkpk_d =>
      fitsEvents_after (rustAllocEvents 64 1 ++ kemDeserializeEvents kpkKey) (rustAllocEvents 64 1)
        hfit3 (by
          unfold Init2Stage4Env; rw [hspk_d, hkpk_d]
          exact Or.inr (Or.inr (SeqEnv.inl (by
            unfold R1bDeserCloneOkEnv; simp only [List.append_assoc])))))
    hpanic hrej3
    (fun evs herr => envAt_of_mem (init2Stage4Env_of_deserCloneErr herr))
    fun sf4 evs_dc spk kpk spkSigPtr kpkSigPtr kpkBuf spkW0 spkW8 spkW12 spkW16 spkW24
        hDcOk hok4 hbundle hspk_bytes hptrs hlens hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 => ?_
  have ⟨spk', hsd⟩ : ∃ spk', PublicKey.deserialize spkKey = .ok spk' := by
    cases h : PublicKey.deserialize spkKey with
    | error e =>
        have hnone := r1b_none_spk_deser (dev := d1.peerV.device) hspk_rd hspk_sp h
        rw [hbundle] at hnone; cases hnone
    | ok v => exact ⟨v, rfl⟩
  have ⟨kpk', hkd⟩ : ∃ kpk', kemPkDeserialize kpkKey = .ok kpk' := by
    cases h : kemPkDeserialize kpkKey with
    | ok v => exact ⟨v, rfl⟩
    | _ =>
        have hnone := r1b_none_kpk_deser (dev := d1.peerV.device) hkpk_rd hkpk_sp
          (fun _ hk => by rw [h] at hk; cases hk)
        rw [hbundle] at hnone; cases hnone
  let fsp := runFsp s0
  let tailFrame : SepProp :=
    memRegion (fsp + 0x4d0#64) 48 ∗
      A.live spkSigPtr 64 1 ∗ (spkSigPtr ↦ₛ spkSig) ∗
      A.live kpkSigPtr 64 1 ∗ (kpkSigPtr ↦ₛ kpkSig) ∗
      A.live kpkBuf 1568 1 ∗ (kpkBuf ↦ₛ kpk) ∗
      r1b_invCoreBase_placed A.repAlloc g d1 s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ownedBytes A.repAlloc d1.dirCap d1.dirPtr (BitVec.ofNat 64 d1.dir.length) d1.dir ∗
      ((fsp + 0x110#64) ↦₆₄ spkSigPtr) ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
      ((fsp + 0x120#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
      ((fsp + 0x138#64) ↦₆₄ kpkSigPtr) ∗
      ((fsp + 0x140#64) ↦₆₄ 1568#64) ∗
      ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x158#64) ↦₆₄ 64#64) ∗
      ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
      ((fsp + 0x178#64) ↦₆₄ kpkBuf) ∗
      ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d1.ikW3) ∗
      ((fsp + 0x1a8#64) ↦₆₄ d1.ikW1) ∗
      ((fsp + 0x1b0#64) ↦₃₂ d1.peerV.device.zeroExtend 32) ∗
      memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24
  let st4 := M.stepEvents evs_dc (M.stepEvents evs_opk (M.stepEvents pfx2 (M.stepEvents pfx1 st)))
  have htail := r1b_step_tail_25f4_placed
    (A := A) (lim := lim) (st := st4) (H := H) (resStack := resStack)
    (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
    (spkW0 := spkW0) (spkW8 := spkW8) (spkW16 := spkW16) (spkW24 := spkW24)
    (kpkCap := kpkCap) (kpkPtr := kpkPtr) (kpkBs := kpkBs)
    (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
    (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
    (F := tailFrame)
    hh hbnd hok4 hopk_sem hx23_4 hx24_4 hx25_4 hx27_4 hx28_4 hpanic
    fun sf5 evs_tail c0 c1 c2 c3 c4 c5 c6 c9 c13 c23 c31
        hfo_tail hok5 hopk_pk hx23_5 hx24_5 hx25_5 hx26_5 hx28_5 => by
      have hStage4 : Init2Stage4Env spkKey kpkKey (evs_dc ++ evs_tail) := by
        unfold Init2Stage4Env; rw [hsd, hkd]
        exact Or.inr (Or.inr (SeqEnv.append hDcOk hfo_tail))
      have hstep := r1b_step_init2_27bc_placed
        (A := A) (lim := lim) (st := M.stepEvents evs_tail st4) (H := H) (resStack := resStack)
        (Q := Q) (Qp := Qp) (oom := fun _ => ⌜False⌝)
        (kpkPtr := kpkPtr) (v130 := kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)
        (kpkCap := kpkCap) (spkPtr := spkPtr) (spkCap := spkCap)
        (regCap := regCap) (regPtr := regPtr)
        hok5 hbundle hspk_bytes hptrs hlens hopk_pk
        hx23_5 hx24_5 hx25_5 hx26_5 hx28_5
        (fun s2 d2 hi2 => by
          dsimp only [st4]
          rw [← M.stepEvents_append evs_dc evs_tail]
          exact hnext3 s2 (evs_dc ++ evs_tail) d2 hi2 hStage4)
      dsimp only [tailFrame, fsp, st4] at hstep ⊢
      exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep
  dsimp only [tailFrame, fsp, st4] at htail ⊢
  exact sepWPp_weaken_pre (Entails.of_eq (by sep_ac_rfl)) htail

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
