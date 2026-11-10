/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize

/-!
# Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Base Callees and Bounds

Proves `[LibsignalPlacement]` Stage P2 stack bounds, `FsAt` lifts, error payload entailments,
`PqxdhPlacedHookContracts`, and Stage P2 callee projections at `cliGhostExterns gh (cliExternsPlaced mmpl W)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
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
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX initialStateValue)
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
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)

/-- Placed `stageP2V1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits. -/
theorem stageP2V1CallStack_le_subStack_placed {A : RustAlloc} [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  stageP2V1CallStack_le_subStack (A := A) 0#64 F0 peer spkId kpkId opkIdWord kbk B

/-- Lift `FsAt (fun f => f = F0) True` + `hh.fs` to placed `FsAt (stageP2EnvOk...) (stageP2Quiet...)`. -/
theorem cliPollStageP2_fsAt_placed {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} [LibsignalPlacement]
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s := by
  rcases hfs with hall | ⟨_, _, hf⟩
  · exact .inl fun f => ⟨hall f, hall f, hall f, hall f⟩
  · exact .inr
      ⟨⟨cliPollSpkPlaced_quiet F0 spkId (cliKitStk B),
        cliPollKpkPlaced_quiet F0 kpkId spkId kbk (cliKitStk B),
        cliPollPkPlaced_quiet F0 opkIdWord (cliKitStk B),
        cliPollSelfPlaced_quiet F0 peer (cliKitStk B)⟩,
       hh.fs (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) 518,
       ⟨hf, hf, hf, hf⟩⟩

/-! ## 2. Placed Error-Payload Entailments (`b := 0#64`) -/

/-- Placed `get_signed_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollSpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (spkId : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSpkKitPlaced A F0 spkId σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSpkKitPlaced A F0 spkId σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  cliPollSpk_getErr_entails_decResAt_anyHeap A 0#64 F0 spkId σ outPtr e err

/-- Placed `get_kyber_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollKpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  cliPollKpk_getErr_entails_decResAt_anyHeap A 0#64 F0 kpkId spkId kbk σ outPtr e err

/-- Placed `get_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollPk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (opkIdWord : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollPkKitPlaced A F0 opkIdWord σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollPkKitPlaced A F0 opkIdWord σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  cliPollPk_getErr_entails_decResAt_anyHeap A 0#64 F0 opkIdWord σ outPtr e err

/-- Placed `get_identity_key_pair` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_kpErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).KpErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).kpErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  cliPollSelf_kpErr_entails_decResAt_err A 0#64 F0 peer σ outPtr e err

/-- Placed `get_local_registration_id` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_regIdErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).RegIdErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).regIdErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  cliPollSelf_regIdErr_entails_decResAt_err A 0#64 F0 peer σ outPtr e err

/-! ## 3. Placed `PqxdhPlacedHookContracts` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` -/

/-- `HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W))` from
`gh.memset = some memsetHook`, `gh.memcpy = some memcpyHook`, and `cliHookTablePlaced mmpl W`. -/
theorem instHkdfPlacedHooks_cli_poll (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks)
    (hMs : gh.memset = some memsetHook) (hMc : gh.memcpy = some memcpyHook) :
    HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  memset := cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hMs
  memcpy := cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hMc
  compress256 := (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (Slots.cliExternsPlaced_compress256 mmpl W)

/-- `PqxdhPlacedHookContractsExactSat` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`
and `E2E.HooksE.A0` from `CliGhostA0Hooks E2E.HooksE.A0 gh` and `RunHooksPlaced`. -/
theorem cliResponderPqxdhHookContractsPlaced [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  refine
    { hkdf :=
        { memset := Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG
          memcpy := Slots.cliGhostExterns_a0_exactMemcpy_sat (cliExternsPlaced mmpl W) hG
          compress256 :=
            (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (Slots.cliExternsPlaced_compress256 mmpl W) }
      dh := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_diffieHellman_sat mmpl W)
      sharedDrop := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_sharedSecretDrop_sat mmpl W)
      staticDrop := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W)
      blackBox :=
        (cliGhostExterns_other gh (cliExternsPlaced mmpl W)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (cliExternsPlaced_row mmpl W (Slots.blackBox_row_placed mmpl W))
      noAllocShim := hh.codecHooks.shim
      alloc := hh.codecHooks.alloc
      dealloc := hh.codecHooks.dealloc
      handleAllocError := Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W
      handleError := Slots.cliGhostExterns_panic_handle_error mmpl gh W
      kyberDecaps := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_kemDecaps_sat mmpl W X)
      dalekMontToEd := by
        rcases Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
          (Slots.cliExternsPlaced_toEdwards_sat mmpl W X (img := default)) with ⟨f, hrow, hok⟩
        exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
          hok ⟨g.inBytes, g.signBit, g.inPtr, g.outPtr⟩ R s0 hrun hpre hsp⟩
      dalekTorsionFree := by
        rcases Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
          (Slots.cliExternsPlaced_torsionFree_sat mmpl W X (img := default)) with ⟨f, hrow, hok⟩
        exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
          hok ⟨g.inPtr, g.inBytes⟩ R s0 hrun hpre hsp⟩ }

/-! ### Placed Stage P2 Callee Projections at `cliGhostExterns gh (cliExternsPlaced mmpl W)` -/

/-- `drop_spe2` (`Getters.dropSpeSpec E2E.HooksE.A0`) on any caller block `i < 619` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliDropSpe2_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (Getters.withLsRoLoaded lsmpl (Getters.dropSpeSpec E2E.HooksE.A0))) :=
  Getters.drop_spe2_placed_ok_at hh.codecHooks.dealloc hi

/-- `drop_session_structure` (`dropSessionStructureLocal2Spec E2E.HooksE.A0`) on any caller block
`i < 619` at `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliDropSessionStructure_placed_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec E2E.HooksE.A0)) :=
  cliDropSessionStructure4_placed_ok_at mmpl gh W hh hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec E2E.HooksE.A0`) on any caller block `i < 619`
at `cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPublicKeySerialize_placed_ok_at [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec E2E.HooksE.A0)) :=
  ls_subroutine_ok_of_block (i := i) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        hh.codecHooks.shim
        hh.codecHooks.alloc
        (Slots.cliGhostExterns_panic_handle_error mmpl gh W)))
    hi

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliPqxdhCalculateAgreement_placed_ok [LibsignalPlacement] (X : UnreachedPqxdhPrimitives)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    ResponderCore.PqxdhCalculateAgreementPlacedOk
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      E2E.HooksE.A0 callerProg :=
  ResponderCore.pqxdhCalculateAgreement_placed_ok_of_block
    (cliModelPrims_matchCrypto X W)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_diffieHellman_sat mmpl W))
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_sharedSecretDrop_sat mmpl W))
    ((cliGhostExterns_other gh (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (Slots.blackBox_row_placed mmpl W)))
    hh.codecHooks.shim
    hh.codecHooks.alloc
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W))
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    hi

/-- `PqxdhHkdfExtractPlacedOk` on any caller block `i < 619` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` from `CliGhostA0Hooks E2E.HooksE.A0 gh`. -/
theorem cliPqxdhHkdfExtract_placed_ok [LibsignalPlacement] (X : UnreachedPqxdhPrimitives)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    Initiator.PqxdhHkdfExtractPlacedOk
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  exact (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh).hkdfExtract_ok
    (cliModelPrims_matchCrypto X W) hi

/-- `PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block `i < 619` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` from `CliGhostA0Hooks E2E.HooksE.A0 gh`. -/
theorem cliPqxdhHkdfExpandMultiInfo_placed_ok [LibsignalPlacement] (X : UnreachedPqxdhPrimitives)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    Initiator.PqxdhHkdfExpandMultiInfoPlacedOk
      (ResponderCore.ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  exact (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh).hkdfExpandMultiInfo_ok
    (cliModelPrims_matchCrypto X W) hi

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
