/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.Closure
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage1Inst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Inst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1Inst
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightP
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecodeStateExt
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.SpqrHooksExt
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfPqxdhExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePanic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowExt
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.TopExt
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopExt
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ContractsAxExt
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.TripleRatchet.Glue

/-!
# Poll Stage Instantiation Bundle

Assembles `stages2_inst : ClosureStages2Stmt` and `Ext`-generalized `stages2_ext_inst :
ClosureStages2ExtStmt` from the stage instantiation modules under `Poll/StagesInst/`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
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
open CryptoVerification.SignalSession.Cli.KitInst

/-- `SessionOnlyKitOkSE` witness on `cliExternsWith ext` for `ClosureStages2ExtStmt.sessKitOk`. -/
theorem pollSessKitOk_ext_inst : PollSessKitOkExtStmt := by
  intro img P A ext B hOk himg hh hRead _ F0 peer
  exact CryptoVerification.SignalSession.Cli.KitInst.SessKit.cliSessKitOkSE_ext_of_hooks
    (readStk := B.readFile) himg hh hRead
    (CryptoVerification.SignalSession.Cli.Slots.sessDeserialize_scopeKit_ext hOk himg)
    (CryptoVerification.SignalSession.Cli.Store.SerGlueX.serializeCanonX_ext hOk img)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Direct `SessionOnlyKitOkSE` witness on `cliPollSessKit` from `CliExternsOk` and `hRead`
(discharging `RunHooksExt` via `RunHooksExt.of_externsOk` and `sessDeserializeExtSpec` via
`Slots.sessDeserialize_scopeKit_ext`, avoiding any `A0`-only `sessDeserializeSpec` hypothesis). -/
theorem pollSessKitOk_of_readFile {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)} {B : RunSkeleton.RunBudgets}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile))
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyKitOkSE
      (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
      Slots.scopeKit E2E.Record.encodeRecord (cliExternsWith ext) :=
  CryptoVerification.SignalSession.Cli.KitInst.SessKit.cliSessKitOkSE_ext_of_hooks
    (readStk := B.readFile) himg (RunSkeleton.RunHooksExt.of_externsOk hOk img) hRead
    (CryptoVerification.SignalSession.Cli.Slots.sessDeserialize_scopeKit_ext hOk himg)
    (CryptoVerification.SignalSession.Cli.Store.SerGlueX.serializeCanonX_ext hOk img)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Direct `SessionOnlyKitOkSE` witness on `cliPollSessKit` from `CliExternsOk` and
`extHookStack ≤ B.readFile`. -/
theorem pollSessKitOk_of_externsOk {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)} {B : RunSkeleton.RunBudgets}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyKitOkSE
      (cliPollSessKit A img.base F0 Slots.scopeKit peer (cliKitStk B))
      Slots.scopeKit E2E.Record.encodeRecord (cliExternsWith ext) :=
  pollSessKitOk_of_readFile hOk himg
    (cliReadFile_ok_cliExternsWith hOk img hread) F0 peer

/-- `IdentityStoreKitOkIE` witness on `cliPollIdKit` for `ClosureStages2ExtStmt.idKitOk`. -/
theorem pollIdKitOk_ext_inst : PollIdKitOkExtStmt := by
  intro img P A ext B hOk himg hh hRead F0 peer
  exact cliIdKitOkIE_full
    (CryptoVerification.SignalSession.Cli.KitInst.IdKit.cliIdKitOkIE_ext32
      (readStk := B.readFile) himg hh hRead
      (CryptoVerification.LibsignalTripleRatchet.Glue.publicKeyEq_ok_ext32 img.base
        (CryptoVerification.SignalSession.Cli.Slots.ext_blackBox hOk))
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))

/-- Direct `IdentityStoreKitOkIE` witness on `cliPollIdKit` from `CliExternsOk` and
`extHookStack ≤ B.readFile` (via `cliIdKitOkIE_ext_of_externsOk_full`). -/
theorem pollIdKitOk_of_externsOk {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)} {B : RunSkeleton.RunBudgets}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile)
    (F0 : FsFiles) (peer : AddrGhost) :
    CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE img
      (cliPollIdKit A img.base F0 peer (cliKitStk B)) (cliExternsWith ext) :=
  cliIdKitOkIE_ext_of_externsOk_full (readStk := B.readFile) hOk himg
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hread

/-- `PollPathBXCallees` witness on `cliExternsWith ext` from `CliExternsOk` and `RunHooksExt`
(without any `A0`-only `sessDeserializeSpec` hypothesis). -/
theorem pollPathBXCallees_ext_inst {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)} {B : RunSkeleton.RunBudgets}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile)) :
    PollPathBXCallees img A B (cliExternsWith ext) :=
  { alloc := CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk
    dropSs3 := cliDropSessionStructure3_ok_ext img.base hOk
    sessKitOk := pollSessKitOk_of_readFile hOk himg hRead
    idKitOk := pollIdKitOk_ext_inst P A ext B hOk himg hh hRead }

/-- `StageP4MatchedExtAt` instantiated from `StageP4MatchedXExtStmt`, `CliExternsOk`, and `RunHooksExt`. -/
theorem stageP4MatchedExtAt_of_ext {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)} {B : RunSkeleton.RunBudgets}
    (hP4X : StageP4MatchedXExtStmt)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile)) :
    StageP4MatchedExtAt img A B (cliExternsWith ext) :=
  stageP4MatchedExtAt_of_xCallees hP4X (pollPathBXCallees_ext_inst hOk himg hh hRead)

/-- Budgeted `StageP4MatchedExtAt` on `cliExternsWith ext` from `StageP4MatchedXExtStmt`,
`CliExternsOk`, and `extHookStack ≤ B.readFile`. -/
theorem stageP4MatchedExtAt_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {ext : String → Option (Arm64.State → Arm64.State)}
    {B : RunSkeleton.RunBudgets}
    (hP4X : StageP4MatchedXExtStmt)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile) :
    StageP4MatchedExtAt img A B (cliExternsWith ext) :=
  stageP4MatchedExtAt_of_ext hP4X hOk himg
    (RunSkeleton.RunHooksExt.of_externsOk hOk img)
    (cliReadFile_ok_cliExternsWith hOk img hread)

/-- Budgeted `StageP4MatchedExtAt` on `cliExternsWith ext` directly from `CliExternsOk` and
`extHookStack ≤ B.readFile` (using `stageP4Matched_x_inst`, for `D2cStagesExtStmt.stageP4PathB`). -/
theorem stageP4Matched_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {ext : String → Option (Arm64.State → Arm64.State)}
    {B : RunSkeleton.RunBudgets}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile) :
    StageP4MatchedExtAt img A B (cliExternsWith ext) :=
  stageP4MatchedExtAt_of_externsOk stageP4Matched_x_inst hOk himg hread

/-- `StageP2MatchedFramedExtAt` on `cliExternsWith ext` directly from `CliExternsOk`
(discharging `RunHooksExt` via `RunHooksExt.of_externsOk`, for `D2cStagesExtStmt.stageP2PathB`). -/
theorem stageP2MatchedFramedExtAt_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    StageP2MatchedFramedExtAt img A (cliExternsWith ext) :=
  @stageP2MatchedFramedExtAt_of_extStmt stageP2Matched_framed_ext_ok P A ext hOk img himg
    (RunSkeleton.RunHooksExt.of_externsOk hOk img)

/-- Instantiates `StageP4PathAV1ExtAt` directly from `Kits.stageP4_v1_vregs_kits_ok_p4`
(`StageP4Alloc.of_allocHooks`). -/
theorem stageP4PathAV1_ext_ok {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {B : RunSkeleton.RunBudgets} {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A (cliExternsWith ext))
    (hRead : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile)) :
    StageP4PathAV1ExtAt img A B (cliExternsWith ext) := by
  intro F0 peer pid kyberPreKeyId signedPreKeyId baseKey remoteIk
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? b_2c0 pt G ss
  dsimp only
  intro hsub64 hprev_nz hExtra hrec_ok hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hfiles hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  let σ := cliKitStk B
  have hp4_64 : stageP4CallStack
      (cliPollSessKit A img.base F0 Slots.scopeKit peer σ)
      (cliPollIdKit A img.base F0 peer σ)
      (cliPollPkKit A img.base F0 pid σ)
      (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ) ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4CallStack_le_subStack img.base F0 Slots.scopeKit peer pid signedPreKeyId
        kyberPreKeyId baseKey B)
      hsub64
  exact Kits.stageP4_v1_vregs_kits_ok_p4 img (cliExternsWith ext) Slots.scopeKit E2E.Record.encodeRecord
    (cliPollSessKit A img.base F0 Slots.scopeKit peer σ)
    (cliPollIdKit A img.base F0 peer σ)
    (cliPollPkKit A img.base F0 pid σ)
    (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ)
    (Kits.StageP4Alloc.of_allocHooks img.base
      (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk))
    (cliDropSessionStructure3_ok_ext img.base hOk)
    (pollSessKitOk_of_readFile hOk himg hRead F0 peer)
    (cliPollSess_vtablesOk himg F0 Slots.scopeKit peer σ)
    (pollIdKitOk_ext_inst P A ext B hOk himg hh hRead F0 peer)
    (cliPollId_vtablesOk himg F0 peer σ)
    (cliPollPk_kitOkImgE_of_hooksExt P.C himg hh B hRead F0 pid)
    (cliPollPk_vtablesOk himg F0 pid σ)
    (cliPollKpk_kitOkImgE_of_hooksExt himg hh B hRead F0 kyberPreKeyId signedPreKeyId baseKey)
    (cliPollKpk_vtablesOk himg F0 kyberPreKeyId signedPreKeyId baseKey σ)
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss
    (cliBase_aligned himg) hprev_nz hExtra hrec_ok rfl rfl
    hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hp4_64
    (cliPollStageP4_fsAt_ext hh F0 Slots.scopeKit peer pid signedPreKeyId kyberPreKeyId
      baseKey B hfiles)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Budgeted `StageP4PathAV1ExtAt` on `cliExternsWith ext` directly from `CliExternsOk` and
`extHookStack ≤ B.readFile`. -/
theorem stageP4PathAV1ExtAt_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {B : RunSkeleton.RunBudgets}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile) :
    StageP4PathAV1ExtAt img A B (cliExternsWith ext) :=
  stageP4PathAV1_ext_ok hOk himg
    (RunSkeleton.RunHooksExt.of_externsOk hOk img)
    (cliReadFile_ok_cliExternsWith hOk img hread)

section PathABudgeted

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem pathAB_fsAt_of_files_eq {img : Obj.Image} {ext : String → Option (State → State)}
    {envOk : FsFiles → Prop} {Q : Prop} {F0 : FsFiles} {s : State}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hQ : Q) (henv : envOk F0) (hf : s.fs.files = F0) :
    FsAt envOk Q (tripleRatchetProgAtExt img.base ext) s :=
  .inr ⟨hQ, hFs, hf ▸ henv⟩

private theorem pathAB_storesAt_opened_entails_cliPollStoresKitsAt
    {A : RustAlloc} (b : BitVec 64) {P : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {me : AddrVal} {pm : PreKeySignalMessage}
    {pid sid kid : BitVec 32} {kbk : PublicKey} (σ : DpKitStk) (a : BitVec 64)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r') (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ P Scope F peer.val me pm) :
    storesAt A a StoresGhost.opened ⊢
      cliPollStoresKitsAt A b F Slots.scopeKit peer pid sid kid kbk σ a StoresGhost.opened :=
  storesAt_entails_cliPollStoresKitsAt b σ a StoresGhost.opened
    (cliSessInv_opened_scopeKit hsub hf) (cliIdOwnInv_opened hd) (cliIdInv_opened_peer hf)
    (cliPkInv_opened hd pid) (cliSpkInv_opened hd sid) (cliKpkInvFull_opened hd kid sid kbk)

private theorem pathAB_sepWPp_pollGoal_frame {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S)) {s0 s1 : State} {P1 Fr_tail R : SepProp}
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 P1
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s1 (P1 ∗ Fr_tail)
      (fun sf P_f =>
        (Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps1f, ⟨hpcm, hrunm, P_f, hmf, hpost, hspf, hcs⟩ | ⟨hpanf, P_f, hmf, hpan⟩ | ⟨_, hoom⟩⟩ :=
    hwp (Fr_tail ∗ R') hm hL
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inl ⟨hpcm, hrunm, P_f ∗ Fr_tail, hmf, ?_, hspf, hcs⟩⟩
    intro hsteps0f hmR
    rw [sepConj_assoc] at hmR
    exact hpost hsteps0f hmR
  · rw [← sepConj_assoc] at hmf
    refine ⟨sf, hsteps1f, Or.inr (Or.inl ⟨hpanf, P_f ∗ Fr_tail, hmf, ?_⟩)⟩
    intro hsteps0f hmR
    rw [sepConj_assoc] at hmR
    exact hpan hsteps0f hmR
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem pathAB_sepWPp_genP3_to_tailQpan {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {P : PEParams}
    (B : RunBudgets) (S : RunSem) (stk' : Nat)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    {rem loc : AddrGhost} {st : SessionState (List (BitVec 8))}
    {msg : SignalMessage} {msgVer : BitVec 32} {rest : List (BitVec 8)}
    {s0 s2 : State} {Pre Fr_tail R : SepProp} {Q : State → SepProp → Prop}
    (hpan : st.version = msgVer →
      (genP3S5Model P.C P.Q.K rem loc msg rest st).1 = .error .panic →
      (dpSlotPollKState A img B S).panics y.g)
    (hwp : SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2 Pre Q
      (genP3S5PanicProp P.C P.Q.K rem loc st msg msgVer rest s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s2 Pre Q
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s0 sf → (sf.mem ⊨ P_f ∗ (Fr_tail ∗ R)) →
          (sf.mem ⊨ ((dpPollSpecState (dpSlotPollKState A img B S) stk').inImage img).onPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hnorm | ⟨hpanf, P_f, hmf, hgp⟩ | ⟨_, hoom⟩⟩ := hwp R' hm hL
  · exact ⟨sf, hsteps, Or.inl hnorm⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpanf, P_f, hmf, ?_⟩)⟩
    intro _ hmR
    rw [← sepConj_assoc] at hmR
    exact dpPollOnPanic_of_genP3 stk' y hgp hpan hmR
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1000000 in
/-- Budget-indexed variant of `closure_pathA_ok_of_stages` accepting `StageP2PathAQpanExtAtB` at
fixed `(B : RunBudgets)` (avoiding `StageP2PathAQpanExtAt`'s universal `∀ B` quantifier). -/
theorem closure_pathA_ok_of_stages_b
    {img : Obj.Image} (P : PEParams) (A : RustAlloc) (ext : String → Option (State → State))
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (himg : Obj.Loads libsignalSessionImage img)
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hP2A : StageP2PathAQpanExtAtB img P A B ext)
    (hP3A : StageP3GenPathAExtAt img P A ext)
    (hP4A : StageP4PathAV1ExtAt img A B ext)
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hS : S.decryptPrekey = decPkDef X P Scope)
    (stk' : Nat) (hneed : dpPollNeed B ≤ stk') (hstk63 : stk' ≤ 2 ^ 63)
    (y : DpPollGhostState (dpSlotPollKState A img B S))
    (s0 s1 : State) (rngPtr v_a8 v_b8 v_d0 : BitVec 64) (R : SepProp)
    (hf0 : s0.fs.files = y.g.F)
    (hfPeer : Slots.FilesOkPeer Scope y.g.F y.g.peer.val)
    (hdecOk : DecPkOk₀ P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg)
    (hcoins : y.g.coins.length < 2 ^ 63)
    (htrusted : StoresGhost.opened.identity.trusted cliIo.rd y.g.F y.g.peer.val
      y.g.msg.identityKey = .ok true)
    (hload_rel : (cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer
      (cliKitStk B)).loadRel StoresGhost.opened.sessions y.g.peer.val (.ok none))
    (hsteps01 : Steps (tripleRatchetProgAtExt img.base ext) s0 s1)
    (htr1 : s1.trace = s0.trace)
    (hinv1 : ImgCallInv img s1)
    (hs1_sp : s1.sp = s0.sp - 0xcd0#64)
    (hsp_sub : dpClosSubStack B ≤ (s0.sp - 0xcd0#64).toNat)
    (hpc1 : s1.pc = closureEntry img ext + 0x0868#64)
    (hrun1 : s1.status = .Running)
    (hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true)
    (hregs1 : StageP1PostRegs s0 s1 (s0.sp - 0xcd0#64) y.fut y.g.msgA y.g.peerA y.g.meA
      y.g.stores (idVt img) (y.g.stores + 0xc8#64) (oneTimeVt img)
      (y.g.stores + 0x50#64) (signedVt img) (y.g.stores + 0x78#64) (kyberVt img)) :
    let prog := tripleRatchetProgAtExt img.base ext
    let K := dpSlotPollKState A img B S
    let sp := s0.sp - 0xcd0#64
    let σ := cliKitStk B
    let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
    let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
    SepWPp prog (s0.readReg64 .x30) s1
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗
       stageP1VtablesAt img kit ikit)
      (fun sf P_f =>
        (Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).post y s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        Steps prog s0 sf → (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ((dpPollSpecState K stk').inImage img).onPanic y s0 sf ∗ R)) := by
  dsimp only
  let sp := s0.sp - 0xcd0#64
  let σ := cliKitStk B
  let pid := pmPreKeyId y.g.msg
  let kit := cliPollSessKit A img.base y.g.F Slots.scopeKit y.g.peer σ
  let ikit := cliPollIdKit A img.base y.g.F y.g.peer σ
  have hloadS : Slots.loadRec Scope y.g.F y.g.peer.val = .ok none :=
    loadRec_of_cliPollSess_loadRel hinjK hsub hfPeer hload_rel
  have hcur : (none : Option (SessionRecord (List (BitVec 8)))).bind (·.currentSession) = none := rfl
  have hroot : rootStack ≤ sp.toNat := Nat.le_trans (rootStack_le_subStack B) hsp_sub
  have hs1_files : s1.fs.files = y.g.F :=
    (pathA_files_eq_of_trace_eq hFs hsteps01 htr1).trans hf0
  have hfiles1 : FsAt (fun f => f = y.g.F) True
      (tripleRatchetProgAtExt img.base ext) s1 :=
    pathAB_fsAt_of_files_eq hFs trivial rfl hs1_files
  let Fr_tail : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
    memRegion y.cx 32 ∗
    stageP1VtablesAt img kit ikit
  have hpre_split :
      stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B) ∗
       memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B) ∗
       memRegion y.cx 32 ∗
       stageP1VtablesAt img kit ikit ⊢
      (stageP2PostP1At A y.fut y.out y.cx y.g.msgA y.g.peerA y.g.meA
         (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
         (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
         (y.g.stores + 0x78#64) (kyberVt img) rngPtr sp v_a8 v_b8 v_d0 s0 ∗
       p1LoadedRecordAt Slots.scopeKit A y.fut none ∗
       preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
       protocolAddressAt A y.g.peer y.g.peerA ∗
       protocolAddressAt A y.g.me y.g.meA ∗
       coinsInstalled img y.g.coinsP y.g.coins ∗
       storesAt A y.g.stores StoresGhost.opened ∗
       TokenInit img ∗
       logOff img ∗
       stackAt sp (dpClosSubStack B)) ∗ Fr_tail := by
    dsimp only [Fr_tail]
    sep_frame
  refine sepWPp_conseq_pre hpre_split (pathAB_sepWPp_pollGoal_frame B S stk' y ?_)
  refine hP2A X S Scope y StoresGhost.opened s0 s1 sp rngPtr v_a8 v_b8 v_d0 _ _
    himg (cliBase_aligned himg) hcoins hdecOk hsub hfPeer hloadS htrusted rfl hfiles1 hinv1
    (htr1 ▸ List.prefix_refl _)
    hs1_sp (sp_frame_sub_add s0.sp) hsp_sub hpc1 hrun1 hsp_align1 hregs1 ?_ ?_ ?_
  · intro sf Pf hoom _ hm_pan
    rw [← sepConj_assoc] at hm_pan
    exact dpPollOnPanic_of_p3p4Oom stk' y hoom hm_pan
  · intro sf Pf _ _ _ hsf_sp hcs_f hvregs_f _ hErr
    rcases hErr with ⟨err, hne_p, hne_s, htr_f, hmodel, hpost_f⟩
    have hcs_full := closureCalleeSaved_toCalleeSavedPreserved hcs_f hvregs_f
    have htr_sf : sf.trace = s0.trace := htr_f.trans htr1
    refine ⟨?_, hsf_sp, hcs_full⟩
    intro hsteps0f hm_f
    have hm1 := Arm64.Satisfies.mono (sepConj_mono_left hpost_f) hm_f
    have hm2 : sf.mem ⊨
        (decResAt A y.out (.error err) ∗
          storesAt A y.g.stores StoresGhost.opened ∗
          protocolAddressAt A y.g.peer y.g.peerA ∗
          protocolAddressAt A y.g.me y.g.meA ∗
          preKeyMsgAt A y.g.msgG y.g.msgA y.g.msg ∗
          logOff img ∗
          A.pool ∗
          (anyHeap ∗ stageP1VtablesAt img kit ikit) ∗
          dpFutDoneAt y.fut ∗
          memRegion y.cx 32 ∗
          memRegion sp 3280 ∗
          stackAt sp (dpClosSubStack B) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk') (stk' - dpPollNeed B)) ∗ R :=
      Arm64.Satisfies.mono (by dsimp only [Fr_tail]; sep_frame) hm1
    have hout : slotOutTr
        (S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins)
        StoresGhost.opened (.error err) s0.trace sf.trace :=
      slotOutTr_of_reject StoresGhost.opened hS hne_p hne_s hmodel
    have hpost_goal := pathA_exit_entails_dpPollPost B S stk' hneed hstk63 y s0 sf StoresGhost.opened
      (.error err) (anyHeap ∗ stageP1VtablesAt img kit ikit) hFs hsteps0f htr_sf hout
    exact Arm64.Satisfies.mono (sepConj_mono_left hpost_goal) hm2
  · intro s2 m i k kp reg dk recG whisperMsgPtr whisperG preKeyMsgRem
      hpm_eq hi hk hkp hreg hacc hex hmsg_fold hsteps12 htr2 hpc2 hrun2
      hs2_sp hsp_align2 _ _ _ hvregs2 hinv2
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st0 := pathAInitState P meE k m dk
    obtain ⟨_hIn0, _hver4, hSeeds, hRC, hPqLt⟩ := pathAInitSession_scopeIn P meE k m dk
    have hsteps02 := Steps.trans hsteps01 hsteps12
    have htr20 : s2.trace = s0.trace := htr2.trans htr1
    have hs2_files : s2.fs.files = y.g.F :=
      (pathA_files_eq_of_trace_eq hFs hsteps02 htr20).trans hf0
    have hpan_model : st0.version = y.g.msg.message.messageVersion.zeroExtend 32 →
        (genP3S5Model P.C P.Q.K y.g.peer y.g.me y.g.msg.message y.g.coins st0).1 = .error .panic →
        (dpSlotPollKState A img B S).panics y.g := by
      intro hver hpan_s5
      show S.decryptPrekey y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins = none
      rw [hS]
      exact decPkDef_pathA_panic X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
        hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver hpan_s5
    let F_p3 : SepProp :=
      stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
        (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
        (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
        (y.g.stores + 0x78#64) (kyberVt img) rngPtr
        (coroOpkIdAtP4 y.fut m.opkId)
        (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
          ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
      stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
      ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
      ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
      preKeyMsgRem ∗
      storesAt A y.g.stores StoresGhost.opened ∗
      memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)
    refine pathAB_sepWPp_genP3_to_tailQpan B S stk' y hpan_model ?_
    refine hP3A s0 s2 y.fut y.cx y.out 8#64 8#64 y.g.peerA y.g.meA whisperMsgPtr y.g.coinsP
      (y.g.msg.message.messageVersion.zeroExtend 32) 0#8 y.g.coins
      recG st0 y.g.peer y.g.me whisperG y.g.msg.message F_p3 _
      (by decide) (Or.inr (distinctSid_of_decPkOk₀ hdecOk)) hSeeds hRC hPqLt
      hinv2.1 hinv2.2 hpc2 hrun2 hsp_align2 (hs2_sp ▸ hroot) htr20 hvregs2 ?_ ?_ ?_
    · intro G₁ G' pt ptCap ptPtr s' P_s' hver hcl hdec_rel hok
        hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
        hx19' hx24' hx25' hx26' hx27' hx28' hfz' hsym' hent_s'
      have hstores_in := pathAB_storesAt_opened_entails_cliPollStoresKitsAt (A := A) img.base σ y.g.stores
        hsub hfPeer hdecOk (pid := pid) (sid := m.spkId) (kid := m.kpkId) (kbk := y.g.msg.baseKey)
      have hunpack_p3 : P_s' ∗ F_p3 ⊢
          P_s' ∗
          (stageP3CoroFrameAt y.fut y.g.msgA y.g.peerA y.g.meA
              (y.g.stores + 0xf0#64) (sessVt img) y.g.stores (idVt img)
              (y.g.stores + 0xc8#64) (oneTimeVt img) (y.g.stores + 0x50#64) (signedVt img)
              (y.g.stores + 0x78#64) (kyberVt img) rngPtr
              (coroOpkIdAtP4 y.fut m.opkId)
              (((y.fut + 0x2a0#64) ↦₆₄ (m.kpkId ++ 1#32)) ∗
                ((y.fut + 0x2a8#64) ↦₃₂ m.spkId)) ∗
            stageP3StackFrameAt sp (y.g.msgA + 0xc8#64) y.g.peerA ∗
            ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
            ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
            preKeyMsgRem ∗
            kit.storeAt (y.g.stores + 0xf0#64) StoresGhost.opened.sessions ∗
            ikit.identityAt y.g.stores StoresGhost.opened.identity ∗
            (cliPollPkKit A img.base y.g.F pid σ).storeAt
              (y.g.stores + 0xc8#64) StoresGhost.opened.oneTime ∗
            (cliPollSpkKit A img.base y.g.F m.spkId σ).storeAt
              (y.g.stores + 0x50#64) StoresGhost.opened.signed ∗
            (cliPollKpkKit A img.base y.g.F m.kpkId m.spkId y.g.msg.baseKey σ).storeAt
              (y.g.stores + 0x78#64) StoresGhost.opened.kyber ∗
            dirAt A (y.g.stores + 0x118#64) StoresGhost.opened.pub ∗
            memRegion (sp - BitVec.ofNat 64 (dpClosSubStack B)) (dpClosSubStack B - rootStack)) := by
        dsimp only [F_p3]
        refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
        refine Entails.trans (sepConj_mono_left hstores_in) ?_
        dsimp only [cliPollStoresKitsAt]
        sep_frame
      exact sepWPp_conseq_pre hunpack_p3
        (closure_pathA_p4_cont_of_stageP4 B S hFs hP4A hS stk' hneed hstk63 y
          hfPeer hdecOk hloadS hcur htrusted m i k kp reg dk recG G₁ G'
          rngPtr whisperMsgPtr ptCap ptPtr whisperG preKeyMsgRem P_s' R pt s0 s2 s'
          hpm_eq hi hk hkp hreg hacc hex hmsg_fold hs2_files htr20 hs2_sp hsp_align2 hsp_sub
          hver hcl hdec_rel hok hpt_le hpt_lt hpt_ne hsteps2' hpc' hrun' hs'_sp htr' hvregs'
          hx19' hx24' hx25' hx26' hx27' hx28' hfz' hsym' hent_s')
    · intro _G₁ _G' e sf P_f hver _hcl _hdec_rel herr hne_p hent_f
        hsf_sp htr_f hcs_f hvregs_f _hfz_f _hsym_f
      exact stageP3_exit_pathA_to_pollPost_ext B S hFs hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem
        (Coins.coinsAfter img.base y.g.coinsP y.g.coins
          (decryptDraws P.C st0 y.g.msg.message.senderRatchetKey y.g.coins))
        P_f R m.opkId m.kpkId m.spkId e hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_err X P Scope y.g.F y.g.peer y.g.me y.g.msg y.g.coins
          hdecOk hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver herr hne_p)
        hent_f hsf_sp htr_f hcs_f hvregs_f
    · intro sf P_f hver_ne hent_f hsf_sp htr_f hcs_f hvregs_f _hfz_f _hsym_f
      exact stageP3_exit_pathA_to_pollPost_ext B S hFs hS stk' hneed hstk63 y s0 s2 sf
        rngPtr whisperMsgPtr whisperG preKeyMsgRem (Coins.coinsAt img.base y.g.coinsP y.g.coins)
        P_f R m.opkId m.kpkId m.spkId (.invalidMessage .preKey .decryptionFailed)
        hs2_sp hsp_sub hmsg_fold
        (decPkDef_pathA_ver_ne X P Scope y.g.F y.g.peer.val y.g.me.val y.g.msg y.g.coins
          hloadS hcur htrusted hpm_eq hi hk hkp hreg hacc hver_ne)
        hent_f hsf_sp htr_f hcs_f hvregs_f

end PathABudgeted

/-- Assembles `ClosurePathAContExtStmt` from stage-decoupled Path A P2 (`StageP2PathAQpanExtAtB`)
and P3 (`StageP3GenPathAExtAt`) `Ext` instantiations plus `stageP4PathAV1_ext_ok`. -/
theorem closure_pathA_cont_of_stages
    (hP2A : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)) (B : RunSkeleton.RunBudgets),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      RunSkeleton.RunHooksExt img A (cliExternsWith ext) →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
        (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile) →
      StageP2PathAQpanExtAtB img P A B (cliExternsWith ext))
    (hP3A : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      StageP3GenPathAExtAt img P A (cliExternsWith ext)) :
    ClosurePathAContExtStmt := by
  intro img P A ext X B S Scope hOk himg hh hRead _ hinjK hsub hS
    stk' hneed hstk63 y s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel
    hsteps01 htr1 hinv1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  exact closure_pathA_ok_of_stages_b P A (cliExternsWith ext) X B S Scope
    himg hh.fs
    (hP2A P A ext B hOk himg hh hRead)
    (hP3A P A ext hOk himg)
    (stageP4PathAV1_ext_ok hOk himg hh hRead)
    hinjK hsub hS stk' hneed hstk63 y s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel
    hsteps01 htr1 hinv1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-- Assembles `ClosurePathBContExtStmt` from `stageP2Matched_framed_ext_ok`,
stage-decoupled Path B P3, and `stageP4Matched_x_inst`. -/
theorem closure_pathB_cont_of_stages
    (hP3B : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      StageP3GenPathBExtAt img P A (cliExternsWith ext)) :
    ClosurePathBContExtStmt := by
  intro img P A ext X B S Scope hOk himg hh hRead hDeser hinjK hsub hS
    stk' hneed hstk63 y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur
    hsteps01 htr1 hinv1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1
  exact closure_pathB_ok_of_stages P A (cliExternsWith ext) X B S Scope
    himg hh.fs
    (stageP2Matched_framed_ext_ok P A ext hOk img himg hh)
    (hP3B P A ext hOk himg)
    (stageP4MatchedExtAt_of_ext stageP4Matched_x_inst hOk himg hh hRead)
    hinjK hsub hS stk' hneed hstk63 y r sess s0 s1 rngPtr v_a8 v_b8 v_d0 R
    hf0 hfPeer hdecOk hcoins htrusted hload_rel hcur
    hsteps01 htr1 hinv1 hs1_sp hsp_sub hpc1 hrun1 hsp_align1 hregs1

/-- Assembles `ClosureStages2ExtStmt` from Path A Stage P2 (`StageP2PathAQpanExtAtB`),
Path A Stage P3 (`StageP3GenPathAExtAt`), and Path B Stage P3 (`StageP3GenPathBExtAt`),
with Stage P1 (`stageP1Ok_x_inst`, `stageP1Untrusted_x_inst`), store kits, and Stage P4
(`stageP4PathAV1_ext_ok`, `stageP4Matched_x_inst`) already discharged. -/
theorem stages2_ext_of_parts
    (hP2A : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)) (B : RunSkeleton.RunBudgets),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      RunSkeleton.RunHooksExt img A (cliExternsWith ext) →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
        (Cli.readFileSpec cliIo.rd cliWrOk A img B.readFile) →
      StageP2PathAQpanExtAtB img P A B (cliExternsWith ext))
    (hP3A : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      StageP3GenPathAExtAt img P A (cliExternsWith ext))
    (hP3B : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext →
      Obj.Loads libsignalSessionImage img →
      StageP3GenPathBExtAt img P A (cliExternsWith ext)) :
    ClosureStages2ExtStmt :=
  { stageP1Ok := stageP1Ok_x_inst
    stageP1Untrusted := stageP1Untrusted_x_inst
    sessKitOk := pollSessKitOk_ext_inst
    idKitOk := pollIdKitOk_ext_inst
    pathA := closure_pathA_cont_of_stages hP2A hP3A
    pathB := closure_pathB_cont_of_stages hP3B }

/-- Budgeted `StageP2PathAQpanExtAtB` on `cliExternsWith ext` from `CliExternsOk`,
`extHookStack ≤ B.readFile`, and the leaf HKDF/initial-state contracts. -/
theorem stageP2PathAQpanExtAtB_of_hkdf_init_read {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {B : RunSkeleton.RunBudgets}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile)
    (hext : ∀ X, E2E.Pqxdh.Initiator.PqxdhHkdfExtractOk_ext
      (E2E.modelPrims X P) img (cliExternsWith ext))
    (hexp : ∀ X, E2E.Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoOk_ext
      (E2E.modelPrims X P) img (cliExternsWith ext))
    (hinit : CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext)) :
    StageP2PathAQpanExtAtB img P A B (cliExternsWith ext) :=
  stageP2PathA_qpan_ext_of_hkdf_init hOk himg
    (RunSkeleton.RunHooksExt.of_externsOk hOk img)
    (cliReadFile_ok_cliExternsWith hOk img hread)
    hext hexp hinit

/-- Assembles `ClosureStages2ExtStmt` from the leaf upstream contracts (`hHkdfExt`, `hHkdfExp`,
`hInit`, `hP3Steps4K`, and `hTryDec`), with Stage P1, store kits, Path B Stage P2, and both
Stage P4 branches already discharged. -/
theorem stages2_ext_of_leaf_contracts
    (hHkdfExt : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)) (X : E2E.UnreachedPqxdhPrimitives),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      E2E.Pqxdh.Initiator.PqxdhHkdfExtractOk_ext (E2E.modelPrims X P) img (cliExternsWith ext))
    (hHkdfExp : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)) (X : E2E.UnreachedPqxdhPrimitives),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      E2E.Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoOk_ext
        (E2E.modelPrims X P) img (cliExternsWith ext))
    (hInit : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
        img A P.C.F (cliExternsWith ext))
    (hP3Steps4K : StageP3GenStepsVRegsStmt4K)
    (hTryDec : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
          CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    ClosureStages2ExtStmt :=
  stages2_ext_of_parts
    (fun P A ext _B hOk himg hh hRead =>
      stageP2PathA_qpan_ext_of_hkdf_init hOk himg hh hRead
        (fun X => hHkdfExt P A ext X hOk himg)
        (fun X => hHkdfExp P A ext X hOk himg)
        (hInit P A ext hOk himg))
    (fun P A ext hOk himg =>
      stageP3GenPathA_ext_of_steps_tryDec P A ext hP3Steps4K hOk himg
        (hTryDec P A ext hOk himg))
    (fun P A ext hOk himg =>
      stageP3GenPathB_ext_of_tryDec P A ext hOk
        (hTryDec P A ext hOk himg))

private theorem hookSat_sessionMemcpyRegionRO4K {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext) :
    Arm64.HookSat (cliExternsWith ext) CryptoVerification.LibsignalTripleRatchet.memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack
        RustHeap.allocHookStack) := by
  refine CryptoVerification.SignalSession.Cli.Slots.hookSat_map
    (CryptoVerification.SignalSession.Cli.Slots.ext_memcpyRO hOk)
    fun _f hh y R s0 hrun hp hsp => ?_
  have hp' : s0.mem ⊨ CryptoVerification.SignalSession.CliExt.memcpyROSpec.pre y s0 ∗ R := by
    simpa only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
      CryptoVerification.SignalSession.CliExt.memcpyROSpec,
      CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack,
      RustHeap.allocHookStack, Arm64.sepConj_assoc] using hp
  obtain ⟨hkf, hsym, hout⟩ := hh y R s0 hrun hp' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hr, hc, ?_⟩
    simpa only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack,
      CryptoVerification.SignalSession.CliExt.memcpyROSpec,
      CryptoVerification.SignalSession.CliExt.withStack,
      CryptoVerification.SignalSession.CliExt.memHookStack,
      RustHeap.allocHookStack, Arm64.sepConj_assoc] using hq
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `InitialStateOkXExt img A P.C.F (cliExternsWith ext)` (`spqr::v1::initial_state`)
directly from `CliExternsOk P A ext` and `Obj.Loads libsignalSessionImage img`. -/
theorem cliInitialState_ok_x_ext {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext) := by
  let hAx := CryptoVerification.SignalSession.Cli.Slots.ext_allocContractsX hOk img
  let hAlloc := CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk
  let hShim := CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk
  let hMemcpy := CryptoVerification.SignalSession.Cli.Slots.hookSat_map
    (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk)
    fun _ hh => CryptoVerification.SignalSession.Cli.Slots.hookOk_sessionMemcpy_of_cliExt hh
      (stk := RustHeap.allocHookStack) (by decide) (by decide)
  let hZero := CryptoVerification.SignalSession.Cli.Slots.ext_allocZeroed hOk
  let hConcat := CryptoVerification.SpqrV1.Alloc.slice_concat_2_ok_x_of_hooks (img := img)
    hShim hAlloc.alloc hMemcpy (hookSat_sessionMemcpyRegionRO4K hOk)
  let hHkdf := CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_ok_ext'
    img himg hOk
  let hAuthUpd := CryptoVerification.SpqrV1.Auth.authUpdate_ok_of_hook_ext
    himg hConcat hHkdf hAx hZero
  let hAuthNew := CryptoVerification.SpqrV1.Auth.authNew_ok_of_hook_ext
    himg hAuthUpd hAx hZero
  let hEnc := CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_okX_ax
    hAx himg
  exact CryptoVerification.SpqrV1.Top.InitialState.initialState_ok_x_ext_of_hooks4k
    himg hAx hAlloc hShim hMemcpy hAuthNew hEnc

/-- Unconditional budgeted `StageP2PathAQpanExtAtB` on `cliExternsWith ext` from `CliExternsOk`,
`Obj.Loads`, and `CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile` (discharging `hHkdfExt`, `hHkdfExp`, and
`InitialStateOkXExt`). -/
theorem stageP2PathAQpanExtAtB_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {B : RunSkeleton.RunBudgets}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile) :
    StageP2PathAQpanExtAtB img P A B (cliExternsWith ext) :=
  stageP2PathAQpanExtAtB_of_hkdf_init_read hOk himg hread
    (fun X => E2E.Pqxdh.ResponderCore.pqxdhHkdfExtract_ok_of_cliExternsOk X himg hOk)
    (fun X => E2E.Pqxdh.ResponderCore.pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk X himg hOk)
    (cliInitialState_ok_x_ext hOk himg)

/-- Unconditional 4K-stack General Stage P3 (`StageP3GenStepsVRegsStmt4K`) assembled from
`stageP3Gen_steps_vregs_4k_ok_of_sub5` and the three 4K `Sub5`/`VerNe` theorems. -/
theorem stageP3Gen_steps_vregs_4k_ok : StageP3GenStepsVRegsStmt4K :=
  stageP3Gen_steps_vregs_4k_ok_of_sub5
    (fun {_A} img b ext hA => GenP3.stageP3_sub5_decResult_ext_4k_ok img b ext hA)
    (fun {_A} img b ext himg hb hA => GenP3.stageP3_sub5_err_ext_4k_ok img b ext himg hb hA)
    (fun {_A} img ext himg hA => GenP3.stageP3_ver_ne_ext_4k_ok img ext himg hA)

/-- Direct `StageP3GenPathAExtAt` on `cliExternsWith ext` from `CliExternsOk`, `Obj.Loads`,
and `hTryDec` (discharging `StageP3GenStepsVRegsStmt4K` via `stageP3Gen_steps_vregs_4k_ok`). -/
theorem stageP3GenPathA_ext_of_tryDec {img : Obj.Image} (P : E2E.PEParams)
    (A : RustHeap.RustAlloc) (ext : String → Option (Arm64.State → Arm64.State))
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTryDec : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
        (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    StageP3GenPathAExtAt img P A (cliExternsWith ext) :=
  stageP3GenPathA_ext_of_steps_tryDec P A ext stageP3Gen_steps_vregs_4k_ok hOk himg hTryDec

/-- Assembles `ClosureStages2ExtStmt` solely from handshake `try_decrypt_with_state` (`hTryDec`),
with `hHkdfExt`, `hHkdfExp`, `InitialStateOkXExt`, and 4K `StageP3GenStepsVRegsStmt4K`
already discharged. -/
theorem stages2_ext_of_tryDec
    (hTryDec : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
          CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    ClosureStages2ExtStmt :=
  stages2_ext_of_leaf_contracts
    (fun _P _A _ext X hOk himg =>
      E2E.Pqxdh.ResponderCore.pqxdhHkdfExtract_ok_of_cliExternsOk X himg hOk)
    (fun _P _A _ext X hOk himg =>
      E2E.Pqxdh.ResponderCore.pqxdhHkdfExpandMultiInfo_ok_of_cliExternsOk X himg hOk)
    (fun _P _A _ext hOk himg => cliInitialState_ok_x_ext hOk himg)
    stageP3Gen_steps_vregs_4k_ok
    hTryDec

/-- Assembles `ClosureStages2ExtStmt` from `SpqrRecvContractsExt` via
`DecryptPq.tryDecryptPqV1_ok_PTight_of_contracts_ext`. -/
theorem stages2_ext_of_spqrContracts
    {H_inner : CryptoVerification.SpqrV1.Top.DecodeState.V1InnerHeapPred}
    (hSpqr : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      CryptoVerification.SpqrV1.Top.Recv.SpqrRecvContractsExt
        H_inner img A P.C.F P.Q.K (cliExternsWith ext)) :
    ClosureStages2ExtStmt :=
  stages2_ext_of_tryDec fun {img} P A ext hOk himg =>
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_of_contracts_ext
      hOk 0#64 img himg (hSpqr P A ext hOk himg)

/-- Unconditional SPQR V1 Recv contract bundle on `cliExternsWith ext` from `CliExternsOk P A ext`
and `Obj.Loads libsignalSessionImage img`. -/
theorem cliSpqrRecvContracts_ext_ok
    {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.SpqrV1.Top.Recv.SpqrRecvContractsExt
      CryptoVerification.SpqrV1.Top.DecodeState.canonicalV1InnerHeap
      img A P.C.F P.Q.K (cliExternsWith ext) := by
  have hAlloc4K :=
    CryptoVerification.Cli.SpqrV1.M4.spqrAllocContracts4K_of_externsOk hOk img.base
  have hGrow :=
    CryptoVerification.SpqrV1.Alloc.vec_deque_grow_ok_x_4k (img := img) hAlloc4K
  exact LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv.spqrRecvContractsExt_of_leaves
    hOk img himg
    (CryptoVerification.Cli.SpqrV1.M4.decodeState_ok_of_externsOk hOk himg)
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv.chainNew_ok_of_grow_ext
      hOk img himg hGrow)
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv.chainAddEpoch_ok_of_grow_ext
      hOk img himg hGrow)
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSpqrRecv.chainRecvKey_ok_of_doReserve_ext
      hOk img himg
      (CryptoVerification.SpqrV1.Alloc.do_reserve_7_ok_inImage_4k (img := img) hAlloc4K))
    (CryptoVerification.SpqrV1.ChainProofs.chain_into_pb_ok_x_4k (img := img) hAlloc4K)
    (CryptoVerification.SpqrV1.States.FromPb.states_from_pb_ok_x_4k
      (img := img) (F := P.C.F) hAlloc4K)
    (LibsignalBinary.Proofs.SpqrV1.States.Recv.ContractsAxExt.statesRecv_ok_x_cli_ext
      P A ext hOk himg)
    (LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopExt.states_into_pb_ok_x_4k
      (img := img) (F := P.C.F) hAlloc4K)

/-- Unconditional handshake `try_decrypt_with_state` contract (`tryDecryptSpecTPTight`) on
`cliExternsWith ext` from `CliExternsOk P A ext` and `Obj.Loads libsignalSessionImage img`. -/
theorem cliTryDecryptPqV1_ok_PTight_ext
    {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
        (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptPqV1_ok_PTight_of_contracts_ext
    hOk 0#64 img himg (cliSpqrRecvContracts_ext_ok hOk himg)

/-- Unconditional Path A Stage P3 witness (`StageP3GenPathAExtAt`) from `CliExternsOk P A ext` and
`Obj.Loads libsignalSessionImage img`. -/
theorem stageP3GenPathA_ext_ok
    {img : Obj.Image} {P : E2E.PEParams} {A : RustHeap.RustAlloc}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img) :
    StageP3GenPathAExtAt img P A (cliExternsWith ext) :=
  stageP3GenPathA_ext_of_tryDec P A ext hOk himg (cliTryDecryptPqV1_ok_PTight_ext hOk himg)

/-- Complete `Ext`-generalized instantiation of all ResponderClosure stage contracts
(`ClosureStages2ExtStmt`) for arbitrary `(P, A, ext)` satisfying `CliExternsOk P A ext`. -/
theorem stages2_ext_inst : ClosureStages2ExtStmt :=
  stages2_ext_of_spqrContracts fun {img} _P _A _ext hOk himg =>
    cliSpqrRecvContracts_ext_ok (img := img) hOk himg

/-- Complete instantiation of the six ResponderClosure stage contracts for `DecryptPrekey/Slot.lean`. -/
theorem stages2_inst : ClosureStages2Stmt :=
  { stageP1Ok := stageP1Ok_inst
    stageP1Untrusted := stageP1Untrusted_inst
    stageP2Matched := stageP2Matched_framed_cli_ok
    stageP3PrevEmpty := stageP3PrevEmpty_inst
    stageP4Matched := stageP4Matched_inst
    stageP2PathA := stageP2PathA_qpan_cli_ok }

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
