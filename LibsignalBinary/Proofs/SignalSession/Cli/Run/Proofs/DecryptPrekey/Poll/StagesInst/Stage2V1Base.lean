/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Bridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StoresAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Pure
import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwned
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityFutDropExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtables
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize

/-!
# CLI Poll Stage P2 V1 Base Callees and Stack Bounds

Proves stack bounds (`stageP2V1CallStack_le_subStack`, `stageP2CallStack4K_le_subStack`), `FsAt`
lifts (`cliPollStageP2_fsAt`), error payload entailments, and pure internal callee bundles
(`cliInitBobErrOwned_ok`, `cliStageP2PureCallees_ok`) for Stage P2 V1.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX InitialStateOkXExt initialStateValue)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Stack Arithmetic & Error Payload Helpers -/

/-- Non-null guarantee for stack pointer `sp - 576#64` when `dpClosSubStack B ≤ sp.toNat`. -/
theorem sp_sub_576_ne_zero (B : RunBudgets) {sp : BitVec 64}
    (hle : dpClosSubStack B ≤ sp.toNat) :
    sp - 576#64 ≠ 0#64 := by
  have h524 : 524288 ≤ dpClosSubStack B := by
    dsimp only [dpClosSubStack]; omega
  intro heq
  have h1 : (sp - 576#64).toNat = 0 := congrArg BitVec.toNat heq
  have hlt : (576#64 : BitVec 64).toNat ≤ sp.toNat := by
    change 576 ≤ sp.toNat; omega
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hlt)] at h1
  change sp.toNat - 576 = 0 at h1
  omega

/-- Lift `P ⊢ decResAt A outPtr r` to `P ⊢ decResAt A outPtr r ∗ anyHeap`. -/
theorem entails_decResAt_anyHeap_of_err_ext {A : RustAlloc}
    {P : SepProp} (outPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (h : P ⊢ decResAt A outPtr (.error err)) :
    P ⊢ decResAt A outPtr (.error err) ∗ anyHeap :=
  Entails.trans h (entails_sepConj_anyHeap _)

/-- Lift `P ⊢ decResAt A0 outPtr r` to `P ⊢ decResAt A0 outPtr r ∗ anyHeap`. -/
theorem entails_decResAt_anyHeap_of_err
    {P : SepProp} (outPtr : BitVec 64) (err : ApiError AddrVal Unit)
    (h : P ⊢ decResAt E2E.HooksE.A0 outPtr (.error err)) :
    P ⊢ decResAt E2E.HooksE.A0 outPtr (.error err) ∗ anyHeap :=
  entails_decResAt_anyHeap_of_err_ext outPtr err h

/-! ## 2. Stack Budget, Pure Callees Bridge, & `FsAt` -/

/-- `stageP2V1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits. -/
theorem stageP2V1CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, _, _, _, _, _, _, hkpS, hkpP, hregS, hregP,
    hpkS, hpkP, _, _, hspkS, hspkP, hkpkS, hkpkP, _, _⟩
  have hPure := stageP2PureAndErrStack_le_subStack B
  have hb700 : stageP2bStack + 0x700 ≤ dpClosSubStack B := by
    have h0 : stageP2bStack + 0x700 ≤ 1048576 - 3280 := by decide
    exact Nat.le_trans h0 (Nat.le_add_right _ _)
  let spkK := cliPollSpkKit A b F0 spkId (cliKitStk B)
  let kpkK := cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B)
  let pkK := cliPollPkKit A b F0 opkIdWord (cliKitStk B)
  let selfK := cliPollSelfKit A b F0 peer (cliKitStk B)
  change stageP2V1CallStack spkK kpkK pkK selfK ≤ dpClosSubStack B
  have hs1 : spkK.getShimStack = (cliKitStk B).spkGetShim := rfl
  have hs2 : spkK.getPollStack = (cliKitStk B).spkGetPoll := rfl
  have hk1 : kpkK.getShimStack = (cliKitStk B).kpkGetShim := rfl
  have hk2 : kpkK.getPollStack = (cliKitStk B).kpkGetPoll := rfl
  have hp1 : pkK.getShimStack = (cliKitStk B).pkGetShim := rfl
  have hp2 : pkK.getPollStack = (cliKitStk B).pkGetPoll := rfl
  have hi1 : selfK.kpShimStack = (cliKitStk B).kpShim := rfl
  have hi2 : selfK.kpPollStack = (cliKitStk B).kpPoll := rfl
  have hi3 : selfK.regIdShimStack = (cliKitStk B).regIdShim := rfl
  have hi4 : selfK.regIdPollStack = (cliKitStk B).regIdPoll := rfl
  have hpure_eq : Kits.stageP2PureAndErrStack = Poll.stageP2PureAndErrStack := rfl
  dsimp only [stageP2V1CallStack, Kits.stageP2CallStack, stageP2Sub1To4Stack, stageP2Sub56Stack,
    spkGetCallStack, kpkGetCallStack, pkGetCallStack, selfKpCallStack, selfRegIdCallStack]
  rw [hs1, hs2, hk1, hk2, hp1, hp2, hi1, hi2, hi3, hi4, hpure_eq]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hspkS, Nat.max_le.mpr ⟨hspkP, hPure⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hkpkS, Nat.max_le.mpr ⟨hkpkP, hPure⟩⟩,
         Nat.max_le.mpr ⟨hpkS, Nat.max_le.mpr ⟨hpkP, hPure⟩⟩⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkpS, Nat.max_le.mpr ⟨hkpP, hPure⟩⟩,
       Nat.max_le.mpr ⟨hregS, Nat.max_le.mpr ⟨hregP, hPure⟩⟩⟩⟩, hb700⟩

/-- `Kits.stageP2PureAndErrStack4K` (`33536` B) fits within `dpClosSubStack B`. -/
theorem stageP2PureAndErrStack4K_le_subStack (B : RunBudgets) :
    Kits.stageP2PureAndErrStack4K ≤ dpClosSubStack B :=
  Nat.le_trans (by decide : Kits.stageP2PureAndErrStack4K ≤ 1048576 - 3280) (Nat.le_add_right _ _)

/-- `Kits.stageP2CallStack4K` (and `stageP2bStack + 0x700`) fits within `dpClosSubStack B` for the
CLI Poll store kits. -/
theorem stageP2CallStack4K_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    max
      (Kits.stageP2CallStack4K
        (cliPollSpkKit A b F0 spkId (cliKitStk B))
        (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
        (cliPollSelfKit A b F0 peer (cliKitStk B)))
      (stageP2bStack + 0x700) ≤ dpClosSubStack B := by
  have hAll := cliKitStk_le_subStack B
  dsimp only [DpKitStk.All] at hAll
  rcases hAll with ⟨_, _, _, _, _, _, _, _, hkpS, hkpP, hregS, hregP,
    hpkS, hpkP, _, _, hspkS, hspkP, hkpkS, hkpkP, _, _⟩
  have hPure4K := stageP2PureAndErrStack4K_le_subStack B
  have hb700 : stageP2bStack + 0x700 ≤ dpClosSubStack B :=
    Nat.le_trans (by decide : stageP2bStack + 0x700 ≤ 1048576 - 3280) (Nat.le_add_right _ _)
  let spkK := cliPollSpkKit A b F0 spkId (cliKitStk B)
  let kpkK := cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B)
  let pkK := cliPollPkKit A b F0 opkIdWord (cliKitStk B)
  let selfK := cliPollSelfKit A b F0 peer (cliKitStk B)
  change max (Kits.stageP2CallStack4K spkK kpkK pkK selfK) (stageP2bStack + 0x700) ≤ dpClosSubStack B
  have hs1 : spkK.getShimStack = (cliKitStk B).spkGetShim := rfl
  have hs2 : spkK.getPollStack = (cliKitStk B).spkGetPoll := rfl
  have hk1 : kpkK.getShimStack = (cliKitStk B).kpkGetShim := rfl
  have hk2 : kpkK.getPollStack = (cliKitStk B).kpkGetPoll := rfl
  have hp1 : pkK.getShimStack = (cliKitStk B).pkGetShim := rfl
  have hp2 : pkK.getPollStack = (cliKitStk B).pkGetPoll := rfl
  have hi1 : selfK.kpShimStack = (cliKitStk B).kpShim := rfl
  have hi2 : selfK.kpPollStack = (cliKitStk B).kpPoll := rfl
  have hi3 : selfK.regIdShimStack = (cliKitStk B).regIdShim := rfl
  have hi4 : selfK.regIdPollStack = (cliKitStk B).regIdPoll := rfl
  dsimp only [Kits.stageP2CallStack4K, Kits.stageP2Sub1To4Stack4K, Kits.stageP2Sub56Stack4K,
    Kits.spkGetCallStack4K, Kits.kpkGetCallStack4K, Kits.pkGetCallStack4K,
    Kits.selfKpCallStack4K, Kits.selfRegIdCallStack4K]
  rw [hs1, hs2, hk1, hk2, hp1, hp2, hi1, hi2, hi3, hi4]
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr
    ⟨Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hspkS, Nat.max_le.mpr ⟨hspkP, hPure4K⟩⟩,
       Nat.max_le.mpr
        ⟨Nat.max_le.mpr ⟨hkpkS, Nat.max_le.mpr ⟨hkpkP, hPure4K⟩⟩,
         Nat.max_le.mpr ⟨hpkS, Nat.max_le.mpr ⟨hpkP, hPure4K⟩⟩⟩⟩,
     Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨hkpS, Nat.max_le.mpr ⟨hkpP, hPure4K⟩⟩,
       Nat.max_le.mpr ⟨hregS, Nat.max_le.mpr ⟨hregP, hPure4K⟩⟩⟩⟩, hb700⟩

/-- Lift `FsAt (fun f => f = F0) True` + `TraceFsSound` to `FsAt (stageP2EnvOk...) (stageP2Quiet...)`. -/
theorem cliPollStageP2_fsAt_of_sound {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hfsSound : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True (tripleRatchetProgAtExt img.base ext) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKit A img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit A img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A img.base F0 opkIdWord (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKit A img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit A img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A img.base F0 opkIdWord (cliKitStk B))
        (cliPollSelfKit A img.base F0 peer (cliKitStk B)))
      (tripleRatchetProgAtExt img.base ext) s := by
  rcases hfs with hall | ⟨_, _, hf⟩
  · exact .inl fun f => ⟨hall f, hall f, hall f, hall f⟩
  · exact .inr
      ⟨⟨cliPollSpk_quiet img.base F0 spkId (cliKitStk B),
        cliPollKpk_quiet img.base F0 kpkId spkId kbk (cliKitStk B),
        cliPollPk_quiet img.base F0 opkIdWord (cliKitStk B),
        cliPollSelf_quiet (img := img) F0 peer (cliKitStk B)⟩,
       hfsSound, ⟨hf, hf, hf, hf⟩⟩

/-- Lift `FsAt (fun f => f = F0) True` + `CliExternsOk` to `FsAt (stageP2EnvOk...) (stageP2Quiet...)`. -/
theorem cliPollStageP2_fsAt_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKit A img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit A img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A img.base F0 opkIdWord (cliKitStk B))
        (cliPollIdKit A img.base F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKit A img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit A img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit A img.base F0 opkIdWord (cliKitStk B))
        (cliPollSelfKit A img.base F0 peer (cliKitStk B)))
      (tripleRatchetProgAtExt img.base (cliExternsWith ext)) s :=
  cliPollStageP2_fsAt_of_sound (Slots.ext_traceFsSound hOk img.base) F0 peer
    spkId kpkId opkIdWord kbk B hfs

/-- Lift `FsAt (fun f => f = F0) True` + `hh.fs` to `FsAt (stageP2EnvOk...) (stageP2Quiet...)`. -/
theorem cliPollStageP2_fsAt {img : Obj.Image} {W : CliHooks}
    (hh : RunSkeleton.RunHooks img E2E.HooksE.A0 (cliExterns W))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True (tripleRatchetProgAtExt img.base (cliExterns W)) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKit E2E.HooksE.A0 img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit E2E.HooksE.A0 img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit E2E.HooksE.A0 img.base F0 opkIdWord (cliKitStk B))
        (cliPollIdKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKit E2E.HooksE.A0 img.base F0 spkId (cliKitStk B))
        (cliPollKpkKit E2E.HooksE.A0 img.base F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKit E2E.HooksE.A0 img.base F0 opkIdWord (cliKitStk B))
        (cliPollSelfKit E2E.HooksE.A0 img.base F0 peer (cliKitStk B)))
      (tripleRatchetProgAtExt img.base (cliExterns W)) s :=
  cliPollStageP2_fsAt_of_sound hh.fs F0 peer spkId kpkId opkIdWord kbk B hfs

/-- `StructuralPrims` for `modelPrims X P`. -/
theorem cliModelPrims_structural_ext (X : UnreachedPqxdhPrimitives) (P : PEParams) :
    StructuralPrims (modelPrims X P) :=
  Pqxdh.Initiator.structuralPrims_initiatorModelPrims X P

/-- `StructuralPrims` for `modelPrims X ⟨W.C, W.Q⟩`. -/
theorem cliModelPrims_structural (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    StructuralPrims (modelPrims X ⟨W.C, W.Q⟩) :=
  cliModelPrims_structural_ext X ⟨W.C, W.Q⟩

/-- `PrimitivesMatchCrypto` for `modelPrims X P`. -/
theorem cliModelPrims_matchCrypto_ext (X : UnreachedPqxdhPrimitives) (P : PEParams) :
    PrimitivesMatchCrypto (modelPrims X P) P.C :=
  Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X P

/-- `PrimitivesMatchCrypto` for `modelPrims X ⟨W.C, W.Q⟩`. -/
theorem cliModelPrims_matchCrypto (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    PrimitivesMatchCrypto (modelPrims X ⟨W.C, W.Q⟩) W.C :=
  cliModelPrims_matchCrypto_ext X ⟨W.C, W.Q⟩

private theorem ofU8_toU8_base : ∀ bs : List (BitVec 8), ofU8 (toU8 bs) = bs
  | [] => rfl
  | _ :: rest => congrArg₂ List.cons rfl (ofU8_toU8_base rest)

private theorem shared_bytesToBv8_eq_ofU8_base :
    ∀ bs : List UInt8, Shared.bytesToBv8 bs = ofU8 bs
  | [] => rfl
  | b :: rest => congrArg₂ List.cons
      ((BitVec.ofNat_toNat 8 b.toBitVec).trans b.toBitVec.setWidth_eq)
      (shared_bytesToBv8_eq_ofU8_base rest)

private theorem u8Vec_toList_eq_bytesToBv8_base {n : Nat} {bs : List UInt8} (h : bs.length = n) :
    (u8Vec n bs).toList = Shared.bytesToBv8 bs := by
  have hof : (ofU8 bs).length = n := by simp [ofU8, h]
  change ((ofU8 bs ++ List.replicate n 0#8).take n) = Shared.bytesToBv8 bs
  rw [shared_bytesToBv8_eq_ofU8_base, List.take_append_of_le_length (Nat.le_of_eq hof.symm),
    List.take_of_length_le (Nat.le_of_eq hof)]

private theorem fitBv8_vecU8_eq_base {n : Nat} (v : List.Vector (BitVec 8) n) :
    Initiator.fitBv8 n (E2E.vecU8 v) = v.toList := by
  have hlen : (E2E.vecU8 v).length = n := by simp [E2E.vecU8, toU8, v.toList_length]
  change Shared.fitBv8 n (E2E.vecU8 v) = v.toList
  rw [Shared.fitBv8_eq_bytesToBv8 hlen, shared_bytesToBv8_eq_ofU8_base, E2E.vecU8, ofU8_toU8_base]

private theorem optEdAt_entails_dalekMontToEdOutAt_base
    (X : UnreachedPqxdhPrimitives) (P : PEParams) (outPtr : BitVec 64)
    (inBytes : List UInt8) (signBit : UInt8) :
    CliExt.optionEdwardsPointAt outPtr (P.Q.montToEd (u8Vec 32 inBytes) (BitVec.ofNat 8 signBit.toNat &&& 1#8)) ⊢
      ResponderCore.dalekMontToEdOutAt
        (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P))
        outPtr inBytes (signBit &&& 1) := by
  have hsign : BitVec.ofNat 8 signBit.toNat &&& 1#8 = (signBit &&& 1).toBitVec := by
    rcases signBit with ⟨v⟩
    simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, UInt8.toBitVec_and]
    rfl
  have hmte :
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)).montToEd inBytes (signBit &&& 1) =
        (P.Q.montToEd (u8Vec 32 inBytes) (signBit &&& 1).toBitVec).map E2E.vecU8 := rfl
  unfold ResponderCore.dalekMontToEdOutAt
  rw [hsign, hmte]
  cases hres : P.Q.montToEd (u8Vec 32 inBytes) (signBit &&& 1).toBitVec with
  | none =>
    exact Entails.of_eq rfl
  | some ed =>
    dsimp only [CliExt.optionEdwardsPointAt, Option.map]
    have hu64 : Initiator.u64le 1#64 = unpack64 1#64 := by decide
    rw [fitBv8_vecU8_eq_base ed, hu64, pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes]
    exact Entails.of_eq rfl

/-- `ResponderCore.PqxdhHookContractsExt` at `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliResponderPqxdhHookContractsExt
    (X : UnreachedPqxdhPrimitives) {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ResponderCore.PqxdhHookContractsExt
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P))
      A img (cliExternsWith ext) where
  alloc := Slots.ext_allocHooks hOk
  shim := Slots.ext_shim hOk
  memcpy := Slots.ext_memcpy hOk
  kyberDecaps := by
    have hsat : HookSat (cliExternsWith ext) ResponderCore.kyberDecapsStub
        (CliExt.kemDecapsSpec P.Q) := Slots.ext_kemDecaps hOk
    refine Slots.hookSat_map hsat fun _ hok =>
      ResponderCore.hookOk_map_ext
        (fun (g : Initiator.KyberDecapsCall) =>
          (g.skPtr, u8Vec 3168 g.sk3168, g.ctPtr, u8Vec 1568 g.ct1568, g.outPtr))
        hok ?_ ?_
    · intro g R s0 hpre
      simp only [ResponderCore.kyberDecapsStubSpecExt, CliExt.kemDecapsSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx8, hsk, hct, _⟩, hmem⟩
      have hbv_sk : (u8Vec 3168 g.sk3168).toList = Initiator.bytesToBv8 g.sk3168 :=
        u8Vec_toList_eq_bytesToBv8_base hsk
      have hbv_ct : (u8Vec 1568 g.ct1568).toList = Initiator.bytesToBv8 g.ct1568 :=
        u8Vec_toList_eq_bytesToBv8_base hct
      refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
      rw [hbv_sk, hbv_ct]
      ac_nf at hmem ⊢
    · intro g R s0 sf hpre hpost
      simp only [ResponderCore.kyberDecapsStubSpecExt, sepConj_assoc,
        satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, _, _, hsk, hct, _⟩, _⟩
      simp only [ResponderCore.kyberDecapsStubSpecExt, CliExt.kemDecapsSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hmem⟩
      have hbv_sk : (u8Vec 3168 g.sk3168).toList = Initiator.bytesToBv8 g.sk3168 :=
        u8Vec_toList_eq_bytesToBv8_base hsk
      have hbv_ct : (u8Vec 1568 g.ct1568).toList = Initiator.bytesToBv8 g.ct1568 :=
        u8Vec_toList_eq_bytesToBv8_base hct
      have hout : Initiator.fitBv8 32 (Initiator.kyberDecapsOutBytes
          (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)) g.sk3168 g.ct1568) =
          (P.Q.decaps (u8Vec 3168 g.sk3168) (u8Vec 1568 g.ct1568)).toList := by
        have hdec : (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)).kemDecaps
            g.sk3168 g.ct1568 =
            some (E2E.vecU8 (P.Q.decaps (u8Vec 3168 g.sk3168) (u8Vec 1568 g.ct1568))) := by
          simp only [ResponderCore.ofSignalPqxdhPrimitives, modelPrims, blockLevelPrims,
            SignalPqxdh.kyberCtLen, hct, beq_self_eq_true, ↓reduceIte]
        unfold Initiator.kyberDecapsOutBytes
        rw [hdec, Option.getD_some]
        exact fitBv8_vecU8_eq_base _
      refine ⟨htr, ?_⟩
      rw [hbv_sk, hbv_ct] at hmem
      rw [hout]
      ac_nf at hmem ⊢
  dalekMontToEd := by
    have hsat : HookSat (cliExternsWith ext) Shared.dalekMontToEdStub
        (CliExt.toEdwardsSpec P.Q) := Slots.ext_toEdwards hOk
    refine Slots.hookSat_map hsat fun _ hok =>
      ResponderCore.hookOk_map_ext
        (fun (g : Initiator.DalekMontToEdGhost) =>
          (g.inPtr, u8Vec 32 g.inBytes, BitVec.ofNat 8 g.signBit.toNat, g.outPtr))
        hok ?_ ?_
    · intro g R s0 hpre
      simp only [ResponderCore.dalekMontToEdStubSpecExt, CliExt.toEdwardsSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
      have hbv : (u8Vec 32 g.inBytes).toList = Initiator.bytesToBv8 g.inBytes :=
        u8Vec_toList_eq_bytesToBv8_base hlen
      refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
      rw [hbv]
      ac_nf at hmem ⊢
    · intro g R s0 sf hpre hpost
      simp only [ResponderCore.dalekMontToEdStubSpecExt, sepConj_assoc,
        satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, _, _, hlen⟩, _⟩
      simp only [ResponderCore.dalekMontToEdStubSpecExt, CliExt.toEdwardsSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hmem⟩
      have hbv : (u8Vec 32 g.inBytes).toList = Initiator.bytesToBv8 g.inBytes :=
        u8Vec_toList_eq_bytesToBv8_base hlen
      rw [hbv] at hmem
      refine ⟨htr, ?_⟩
      have hmem' : sf.mem ⊨
          CliExt.optionEdwardsPointAt g.outPtr
            (P.Q.montToEd (u8Vec 32 g.inBytes) (BitVec.ofNat 8 g.signBit.toNat &&& 1#8)) ∗
          ((g.inPtr ↦ₛ Initiator.bytesToBv8 g.inBytes) ∗ stackAt s0.sp extHookStack ∗ R) := by
        ac_nf at hmem ⊢
      have hmem'' := Satisfies.mono
        (sepConj_mono_left (optEdAt_entails_dalekMontToEdOutAt_base X P g.outPtr g.inBytes g.signBit))
        hmem'
      ac_nf at hmem'' ⊢
  dalekTorsionFree := by
    have hsat : HookSat (cliExternsWith ext) Shared.dalekTorsionFreeStub
        (CliExt.torsionFreeSpec P.Q) := Slots.ext_torsionFree hOk
    refine Slots.hookSat_map hsat fun _ hok =>
      ResponderCore.hookOk_map_ext
        (fun (g : Initiator.CryptoUnaryGhost) => (g.inPtr, u8Vec 160 g.inBytes))
        hok ?_ ?_
    · intro g R s0 hpre
      simp only [ResponderCore.cryptoBoolRegStubSpecExt, CliExt.torsionFreeSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hlen⟩, hmem⟩
      have hbv : (u8Vec 160 g.inBytes).toList = Shared.bytesToBv8 g.inBytes :=
        u8Vec_toList_eq_bytesToBv8_base hlen
      refine ⟨hx0, ?_⟩
      rw [hbv]
      ac_nf at hmem ⊢
    · intro g R s0 sf hpre hpost
      simp only [ResponderCore.cryptoBoolRegStubSpecExt, sepConj_assoc,
        satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, hlen⟩, _⟩
      simp only [ResponderCore.cryptoBoolRegStubSpecExt, CliExt.torsionFreeSpec, CliExt.withStack,
        Initiator.pqxdhHookStackExt, extHookStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, hx0⟩, hmem⟩
      have hbv : (u8Vec 160 g.inBytes).toList = Shared.bytesToBv8 g.inBytes :=
        u8Vec_toList_eq_bytesToBv8_base hlen
      have htf : (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)).isTorsionFree g.inBytes =
          P.Q.isTorsionFree (u8Vec 160 g.inBytes) := rfl
      rw [htf]
      rw [hbv] at hmem
      refine ⟨⟨htr, hx0⟩, ?_⟩
      ac_nf at hmem ⊢

/-- `ResponderCore.PqxdhHookContractsExt` at `Slots.trapUnlisted ext` from `CliExternsOk P A ext`. -/
theorem cliResponderPqxdhHookContractsExt_trapUnlisted
    (X : UnreachedPqxdhPrimitives) {P : PEParams} {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    ResponderCore.PqxdhHookContractsExt
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P))
      A img (Slots.trapUnlisted ext) := by
  simpa only [Slots.cliExternsWith_trapUnlisted] using
    cliResponderPqxdhHookContractsExt X (Slots.cliExternsOk_trapUnlisted hOk) img

/-- `ResponderCore.PqxdhHookContracts` at `cliExterns W` and `E2E.HooksE.A0`. -/
theorem cliResponderPqxdhHookContracts (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image) :
    ResponderCore.PqxdhHookContracts
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      E2E.HooksE.A0 img (cliExterns W) where
  alloc := Slots.cliExterns_allocHooks W
  kyberDecaps := Slots.cliExterns_kemDecaps W X
  dalekMontToEd := by
    rcases (Slots.cliExterns_pqxdhHookContracts W X (A := E2E.HooksE.A0) img).dalekMontToEd with
      ⟨f, hrow, hok⟩
    exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
      hok ⟨g.inBytes, g.signBit, g.inPtr, g.outPtr⟩ R s0 hrun hpre hsp⟩
  dalekTorsionFree := by
    rcases (Slots.cliExterns_pqxdhHookContracts W X (A := E2E.HooksE.A0) img).dalekTorsionFree with
      ⟨f, hrow, hok⟩
    exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
      hok ⟨g.inPtr, g.inBytes⟩ R s0 hrun hpre hsp⟩

/-- `pqxdhAccept = none` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem pqxdhAcceptErr_entails_decResAt_anyHeap_ext (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64) (err : ApiError AddrVal Unit) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
    Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ⊢
      decResAt A outPtr (.error err) ∗ anyHeap := by
  unfold Kits.pqxdhAcceptErrPayloadAt
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun isStr => ?_
  cases isStr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sepConj_comm]
    refine Entails.pure_left fun htag => ?_
    subst htag
    exact entails_decResAt_anyHeap_of_err_ext outPtr err
      (plainSpeWords_entails_decResAt_err A outPtr 10 (by decide) w2 w3 w4 w5 w6 err)
  · simp only [↓reduceIte]
    rw [← sepConj_assoc, sepConj_comm (speWordsAt outPtr errTag w2 w3 w4 w5 w6), sepConj_assoc]
    refine Entails.pure_left fun htag => ?_
    subst htag
    have hstr := strSpeWords_entails_decResAt_anyHeap A outPtr 24 (by decide)
      w2 w3 w4 w5 w6 emp err
    rw [sepConj_emp] at hstr
    exact hstr

/-- `pqxdhAccept = none` error payload entails `decResAt A0 outPtr (.error err) ∗ anyHeap`. -/
theorem pqxdhAcceptErr_entails_decResAt_anyHeap
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64) (err : ApiError AddrVal Unit) :
    speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
    Kits.pqxdhAcceptErrPayloadAt E2E.HooksE.A0 errTag w2 w3 w4 ⊢
      decResAt E2E.HooksE.A0 outPtr (.error err) ∗ anyHeap :=
  pqxdhAcceptErr_entails_decResAt_anyHeap_ext E2E.HooksE.A0 outPtr errTag w2 w3 w4 w5 w6 err

/-! ### Contract-Backed `CliExternsOk` Stage P2 Callee Projections -/

/-- `drop_spe2` (`Getters.dropSpeSpec A`) on `cliExternsWith ext` from `CliExternsOk` (`AllocHooks` alone). -/
theorem cliDropSpe2_ok_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr CryptoVerification.Cli.dropSpe2Name)
      ((Getters.dropSpeSpec A).inImage img) :=
  GenP3.drop_spe2_of_allocHooks_ext himg (Slots.ext_allocHooks hOk)

/-- `drop_session_structure3` (`dropSessionStructureLocal2Spec A`) on `cliExternsWith ext` from
`CliExternsOk` (`AllocHooks` alone). -/
theorem cliDropSessionStructure3_ok_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A) :=
  GenP3.drop_session_structure3_of_allocHooks_ext (Slots.ext_allocHooks hOk)

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec A`) on `cliExternsWith ext` from `CliExternsOk`. -/
theorem cliPublicKeySerialize_ok_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr publicKeySerializeName)
      (publicKeySerializeSpec A) :=
  Kits.p2_publicKeySerialize_of_hooks (Slots.ext_allocHooks hOk) (Slots.ext_shim hOk)

/-- `StageP2ClosureHooks` on `cliExternsWith ext` from `CliExternsOk`. -/
theorem cliStageP2ClosureHooks_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    Kits.StageP2ClosureHooks A b (cliExternsWith ext) :=
  Kits.StageP2ClosureHooks.of_hooks
    (Slots.ext_allocHooks hOk) (Slots.ext_shim hOk) (Slots.ext_memcpy hOk)

/-- `<PublicKey>::serialize` (`publicKeySerializeSpecX A`) on `cliExternsWith ext` from
`AllocContractsX`. -/
theorem cliPublicKeySerialize_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr publicKeySerializeName)
      ((publicKeySerializeSpecX A).inImage img) :=
  CryptoVerification.LibsignalTripleRatchet.public_key_serialize_ok_ext_x hA

/-- `is_same_account` (`IsSameAccountDistinctOkExt32`) on `cliExternsWith ext` from `CliExternsOk`. -/
theorem cliIsSameAccount_ok_ext32 {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32
      b A (cliExternsWith ext) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountEqDistinct_ok_ext32
    b A (cliExternsWith ext) (Slots.ext_blackBox hOk)

/-- `PqxdhCalculateAgreementOkExt` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliPqxdhCalculateAgreement_ok_ext (X : UnreachedPqxdhPrimitives)
    {P : PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    ResponderCore.PqxdhCalculateAgreementOkExt
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X P)) A img (cliExternsWith ext) :=
  ResponderCore.pqxdhCalculateAgreement_ok_of_cliExternsOk X himg hOk

/-- `AllocContractsMem4K` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliAllocContractsMem4K_ext {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (b : BitVec 64)
    (hOk : CliExternsOk P A ext) :
    AllocContractsMem4K b A (cliExternsWith ext) :=
  AllocContractsMem4K.of_hooks b A (cliExternsWith ext)
    (Slots.ext_allocHooks hOk) (Slots.ext_shim hOk)
    (Slots.ext_memcpy hOk) (Slots.ext_memmove hOk) (Slots.ext_memset hOk)

/-- `PreKeyStoreKitOkImgE` for `cliPollPkKit` on `ext` from `RunHooksExt` and `hRead`. -/
theorem cliPollPk_kitOkImgE_of_hooksExt (C : Crypto) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (B : RunBudgets)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (pid : BitVec 32) :
    PreKeyStoreKitOkImgE img
      (cliPollPkKit A img.base F0 pid (cliKitStk B)) ext :=
  cliPreKeyKitOk_of_hooksExt C (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `SignedPreKeyStoreKitOkImgE` for `cliPollSpkKit` on `ext` from `RunHooksExt` and `hRead`. -/
theorem cliPollSpk_kitOkImgE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (B : RunBudgets)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (sid : BitVec 32) :
    SignedPreKeyStoreKitOkImgE img
      (cliPollSpkKit A img.base F0 sid (cliKitStk B)) ext :=
  cliSignedPreKeyKitOk_of_hooksExt (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _)

/-- `KyberPreKeyStoreKitOkImgE` for `cliPollKpkKit` on `ext` from `RunHooksExt` and `hRead`. -/
theorem cliPollKpk_kitOkImgE_of_hooksExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (B : RunBudgets)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (kid sid : BitVec 32) (kbk : PublicKey) :
    KyberPreKeyStoreKitOkImgE img
      (cliPollKpkKit A img.base F0 kid sid kbk (cliKitStk B)) ext :=
  cliKyberKitOk_of_hooksExt (readStk := B.readFile) himg hh hRead
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `IdentitySelfStoreKitOkI` for `cliPollIdKit` + `cliPollSelfKit` on `ext` from `RunHooksExt`
and `hRead`. -/
theorem cliPollSelf_kitOkI_of_hooksExt (C : Crypto) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A ext)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentitySelfStoreKitOkI img
      (cliPollIdKit A img.base F0 peer (cliKitStk B))
      (cliPollSelfKit A img.base F0 peer (cliKitStk B)) ext := by
  have hBase := RunSkeleton.base_aligned himg
  have hGet := Initiate.dirGet_ext_ok B himg hh hRead
  exact cliSelfKitOkI_of_hops
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idKeyPairShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (subroutine_ok_map_panic
      (Initiate.IdKeyPairPoll.idKeyPairPoll_ok_of_deps (stk := (cliKitStk B).kpPoll)
        himg hh.alloc hGet
        (Initiate.identityKeyPairTryFrom_cli_ok C himg hh.alloc)
        (by dsimp [cliKitStk, Initiate.IdKeyPairPoll.kpCalleeStk]; omega) hBase)
      fun x R _ hpre => ⟨⟨x.fut, x.out, x.self, x.own⟩, R, hpre, fun _ hp => hp, fun _ hp => hp⟩)
    (Initiate.StoreCalleesProofs.idOwnShim_lift_stk
      (Initiate.StoreCalleesProofs.idRegIdShim_fixed_ok hh.alloc hBase) (Nat.le_refl _))
    (subroutine_ok_map_panic
      (Initiate.IdRegIdPoll.idRegIdPoll_ok_of_deps (stk := (cliKitStk B).regIdPoll)
        himg hh.alloc hGet
        (by dsimp [cliKitStk, Initiate.IdRegIdPoll.regCalleeStk]; omega) hBase)
      fun x R _ hpre => ⟨⟨x.fut, x.out, x.self, x.own⟩, R, hpre, fun _ hp => hp, fun _ hp => hp⟩)
    cliIdFutDrop_ok_ext

/-- Owned 4K/`Ext` `initialize_bob_session` error-exit spec on `cliExternsWith ext` from
`CliExternsOk P A ext` (`Kits.initializeBobSession_err_owned_4k_ok_ext`). -/
theorem cliInitBobErrOwned4K_ok_ext
    (X : UnreachedPqxdhPrimitives) {P : PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr initializeBobSessionSym)
      (Kits.initializeBobSessionErrOwned4KSpec (modelPrims X P) A img) :=
  Kits.initializeBobSession_err_owned_4k_ok_ext himg
    (cliModelPrims_structural_ext X P)
    (cliResponderPqxdhHookContractsExt X hOk img)
    (cliPqxdhCalculateAgreement_ok_ext X himg hOk)

/-- 4K/`Ext` pure internal callees (`StageP2PureCallees4K`) on `cliExternsWith ext` from
`CliExternsOk P A ext`, HKDF extract/expand contracts, and `InitialStateOkXExt`. -/
theorem cliStageP2PureCallees4K_of_hkdf_init
    (X : UnreachedPqxdhPrimitives) {P : PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hext : Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hexp : Initiator.PqxdhHkdfExpandMultiInfoOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hinit : InitialStateOkXExt img A P.C.F (cliExternsWith ext)) :
    StageP2PureCallees4K (modelPrims X P) A P.C.F img (cliExternsWith ext) :=
  Kits.StageP2PureCallees4K.of_hooks himg
    (Slots.ext_allocHooks hOk)
    (Slots.ext_shim hOk)
    (Slots.ext_memcpy hOk)
    (cliIsSameAccount_ok_ext32 img.base hOk)
    (cliModelPrims_structural_ext X P)
    (cliResponderPqxdhHookContractsExt X hOk img)
    hext hexp
    (cliPqxdhCalculateAgreement_ok_ext X himg hOk)
    hinit

/-- Owned `initialize_bob_session` error-exit spec on `cliExterns W`. -/
theorem cliInitBobErrOwned_ok
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr initializeBobSessionSym)
      (Kits.initializeBobSessionErrOwnedSpec (modelPrims X ⟨W.C, W.Q⟩) E2E.HooksE.A0 img) := by
  exact initializeBobSession_err_owned_ok_ext himg
    (cliModelPrims_structural X W)
    (cliResponderPqxdhHookContracts X W img)
    (cliModelPrims_matchCrypto X W)
    (Slots.trapsOnly_trTrap_cli img.base W)

/-- Pure internal callees (`StageP2PureCallees`) at `cliExterns W`. -/
theorem cliStageP2PureCallees_ok
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img E2E.HooksE.A0 (cliExterns W)) :
    StageP2PureCallees (modelPrims X ⟨W.C, W.Q⟩) E2E.HooksE.A0 W.C.F img (cliExterns W) where
  publicKeySerialize := CryptoVerification.LibsignalTripleRatchet.public_key_serialize_ok_ext hh.allocContracts
  promoteMatchingSessionEmpty := Slots.subroutine_ok_cli_of_trTrap promote_matching_session_empty_ok_trap
  curveKeyPairSerde := Slots.subroutine_ok_cli_of_trTrap curveKeyPairSerde_ok_trap
  kemKeyPairSerde := Slots.subroutine_ok_cli_of_trTrap (kemKeyPairSerde_ok_trap (Slots.cliExterns_allocHooks W))
  preKeyRecordKeyPair := Slots.subroutine_ok_cli_of_trTrap preKeyRecordKeyPair_ok_trap
  dropSpe2 := GenP3.drop_spe2_ok_ext himg hh.allocContracts
  isSameAccount := isSameAccount_cli_ok W himg hh
  initializeBobErr :=
    Slots.subroutine_ok_cli_of_trTrap
      (initializeBobSession_err_ok_trap himg
        (cliModelPrims_structural X W)
        (cliResponderPqxdhHookContracts X W img)
        (cliModelPrims_matchCrypto X W))
  initializeBobV1 :=
    CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext_trap himg
      (cliModelPrims_structural X W)
      (cliResponderPqxdhHookContracts X W img)
      (cliModelPrims_matchCrypto X W)
      (Slots.trapsOnly_trTrap_cli img.base W)
      (CryptoVerification.SpqrV1.Top.InitialState.initial_state_ok_x himg hh.allocContracts
        (Slots.authNewOkX_cli_of_hooks W himg hh.allocContracts hh.allocZeroed))
  promoteStateEmpty := Slots.subroutine_ok_cli_of_trTrap promote_state_empty_ok_trap
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_ok
  dropSessionStructure3 := GenP3.drop_session_structure3_ok_ext hh.allocContracts

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
