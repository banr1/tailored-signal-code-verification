/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverUntrusted
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage3GenInst
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5b
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureCallees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStmts
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt

/-!
# D2(c) Overwrite-Path (`Path C`) `Ext` Stage Instantiations

Contract-backed (`CliExternsOk P A ext`) Stage P3 and Stage P4 overwrite-path witnesses and
assembly of `D2cStagesExtStmt` from Path A, Path B, and Path C stage contracts.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad
open CryptoVerification CryptoVerification.E2E CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

/-- Unconditional 4K-stack General Stage P3 (`StageP3GenStepsVRegsStmt4K`) assembled from
`stageP3Gen_steps_vregs_4k_ok_of_sub5` and the three 4K `Sub5`/`VerNe` theorems. -/
theorem stageP3GenStepsVRegs_4k_ok : StageP3GenStepsVRegsStmt4K :=
  stageP3Gen_steps_vregs_4k_ok_of_sub5
    (fun {_A} img b ext hA => GenP3.stageP3_sub5_decResult_ext_4k_ok img b ext hA)
    (fun {_A} img b ext himg hb hA => GenP3.stageP3_sub5_err_ext_4k_ok img b ext himg hb hA)
    (fun {_A} img ext himg hA => GenP3.stageP3_ver_ne_ext_4k_ok img ext himg hA)

/-- Instantiates `StageP3Prev1PathCExtAt` on `cliExternsWith ext` from explicit
`hClone : GenP3.CloneGenVRegsStmt4K`, `CliExternsOk P A ext`, and `tryDecrypt`. -/
theorem stageP3Prev1PathCExtAt_of_tryDec_clone {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {ext : String → Option (Arm64.State → Arm64.State)}
    (hClone : GenP3.CloneGenVRegsStmt4K)
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTryDec : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
        (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    StageP3Prev1PathCExtAt img P A (cliExternsWith ext) :=
  let hC := StageP3Callees4K.of_cliExternsOk hOk hTryDec
  Over.stageP3Gen_prev1_vregs_at_4k_ok_of_clone hClone Over.overVerNe_1e04_cli_at_4k
    img (cliExternsWith ext) P.C 0#64 P.Q.K
    hC.alloc4K hC.chainClone hC.senderChainClone hC.tryDecrypt hC.dropSs3 himg

/-- Instantiates `StageP3Prev1PathCExtAt` on `cliExternsWith ext` from `CliExternsOk P A ext`
and `tryDecrypt` (discharging `CloneGenVRegsStmt4K` via `GenP3.cloneGen_vregs_4k_ok`). -/
theorem stageP3Prev1PathCExtAt_of_tryDec {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hTryDec : subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
        CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
        (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    StageP3Prev1PathCExtAt img P A (cliExternsWith ext) :=
  stageP3Prev1PathCExtAt_of_tryDec_clone GenP3.cloneGen_vregs_4k_ok hOk himg hTryDec

/-- Budgeted `StageP4Prev1PathCExtAt` on `cliExternsWith ext` from `CliExternsOk P A ext`
and `extHookStack ≤ B.readFile` (via `Over.stageP4_prev1_vregs_at_4k_ok`). -/
theorem stageP4Prev1PathCExtAt_of_externsOk {img : Obj.Image} {P : E2E.PEParams}
    {A : RustHeap.RustAlloc} {B : RunSkeleton.RunBudgets}
    {ext : String → Option (Arm64.State → Arm64.State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hread : extHookStack ≤ B.readFile) :
    StageP4Prev1PathCExtAt img A B (cliExternsWith ext) := by
  intro F0 peer pid kyberPreKeyId signedPreKeyId baseKey remoteIk
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? b_2c0 pt enc G ss
  dsimp only
  intro hsub64 hExtra hrec_ok hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hfiles hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  let σ := cliKitStk B
  let hh := RunSkeleton.RunHooksExt.of_externsOk hOk img
  let hRead := cliReadFile_ok_cliExternsWith hOk img (hstk := hread)
  let hA4K : GenP3.AllocContractsMem4K img.base A (cliExternsWith ext) :=
    GenP3.AllocContractsMem4K.of_hooks img.base A (cliExternsWith ext)
      (CryptoVerification.SignalSession.Cli.Slots.ext_allocHooks hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_shim hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memcpy hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memmove hOk)
      (CryptoVerification.SignalSession.Cli.Slots.ext_memset hOk)
  have hp4_64 : Kits.stageP4CallStack
      (cliPollSessPrev1Kit A img.base F0 peer σ)
      (cliPollIdKit A img.base F0 peer σ)
      (cliPollPkKit A img.base F0 pid σ)
      (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ) ≤ 2 ^ 64 :=
    Nat.le_trans
      (stageP4CallStack_le_subStack img.base F0 Slots.scopeKit peer pid signedPreKeyId
        kyberPreKeyId baseKey B)
      hsub64
  exact Over.stageP4_prev1_vregs_at_4k_ok img (cliExternsWith ext)
    (cliPollSessPrev1Kit A img.base F0 peer σ)
    cliPollStorePrev1Ops
    (cliPollIdKit A img.base F0 peer σ)
    (cliPollPkKit A img.base F0 pid σ)
    (cliPollKpkKit A img.base F0 kyberPreKeyId signedPreKeyId baseKey σ)
    hA4K
    (cliDropSessionStructure3_ok_ext img.base hOk)
    (cliPollSess_prev1KitOkSE_ext hOk himg F0 peer B)
    (cliPollSess_prev1VtablesOk himg F0 peer σ)
    (pollIdKitOk_of_externsOk hOk himg hread F0 peer)
    (cliPollId_vtablesOk himg F0 peer σ)
    (cliPollPk_kitOkImgE_of_hooksExt P.C himg hh B hRead F0 pid)
    (cliPollPk_vtablesOk himg F0 pid σ)
    (cliPollKpk_kitOkImgE_of_hooksExt himg hh B hRead F0 kyberPreKeyId signedPreKeyId baseKey)
    (cliPollKpk_vtablesOk himg F0 kyberPreKeyId signedPreKeyId baseKey σ)
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
    StoresGhost.opened.sessions StoresGhost.opened.identity
    StoresGhost.opened.oneTime StoresGhost.opened.kyber G ss
    (cliBase_aligned himg) hExtra hrec_ok rfl rfl
    hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hp4_64
    (cliPollStageP4_fsAt_ext hh F0 Slots.scopeKit peer pid signedPreKeyId kyberPreKeyId baseKey B hfiles)
    hF hsym hpc hrun hsp_align htr_pfx
    hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Assembles `D2cStagesExtStmt` from an explicit Path C Stage P2 contract (`hP2COver`) and the
four leaf upstream contracts (`hHkdfExt`, `hHkdfExp`, `hInit`, `hTryDec`). -/
theorem d2cStages_ext_of_p2c_and_leaves
    (hP2COver : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      StageP2PathCOverQpanExtAt img P A (cliExternsWith ext))
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
    (hTryDec : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
          CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    D2cStagesExtStmt :=
  { stageP1Ok := stageP1Ok_x_inst
    stageP1Untrusted := stageP1Untrusted_x_inst
    stageP2PathA := fun P A ext _B hOk himg hread =>
      stageP2PathAQpanExtAtB_of_hkdf_init_read hOk himg hread
        (fun X => hHkdfExt P A ext X hOk himg)
        (fun X => hHkdfExp P A ext X hOk himg)
        (hInit P A ext hOk himg)
    stageP3PathA := fun P A ext hOk himg =>
      stageP3GenPathA_ext_of_steps_tryDec P A ext stageP3GenStepsVRegs_4k_ok hOk himg
        (hTryDec P A ext hOk himg)
    stageP4PathA := fun _P _A _ext _B hOk himg hread =>
      stageP4PathAV1ExtAt_of_externsOk hOk himg hread
    stageP2PathB := fun _P _A _ext hOk himg =>
      stageP2MatchedFramedExtAt_of_externsOk hOk himg
    stageP3PathB := fun P A ext hOk himg =>
      stageP3GenPathB_ext_of_tryDec P A ext hOk (hTryDec P A ext hOk himg)
    stageP4PathB := fun _P _A _ext _B hOk himg hread =>
      stageP4Matched_of_externsOk hOk himg hread
    stageP2Over := fun P A ext hOk himg =>
      stageP2Over_qpan_ext_of_pathCOver (hP2COver P A ext hOk himg)
    stageP3Prev1 := fun P A ext hOk himg =>
      stageP3Prev1PathCExtAt_of_tryDec hOk himg (hTryDec P A ext hOk himg)
    stageP4Prev1 := fun _P _A _ext _B hOk himg hread =>
      stageP4Prev1PathCExtAt_of_externsOk hOk himg hread }

/-- Assembles `D2cStagesExtStmt` from the four leaf upstream contracts (`hHkdfExt`, `hHkdfExp`,
`hInit`, `hTryDec`), discharging Path C Stage P2 via `stageP2PathCOver_qpan_ext_of_hkdf_init`,
4K Stage P3 via `stageP3GenStepsVRegs_4k_ok` and `stageP3Prev1PathCExtAt_of_tryDec`, and all
three Stage P4 branches. -/
theorem d2cStages_ext_of_leaf_contracts
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
    (hTryDec : ∀ {img : Obj.Image} (P : E2E.PEParams) (A : RustHeap.RustAlloc)
      (ext : String → Option (Arm64.State → Arm64.State)),
      CliExternsOk P A ext → Obj.Loads libsignalSessionImage img →
      subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
        ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName)
        (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecTPTight P.C A 0#64
          CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 P.C.F P.Q.K) img)) :
    D2cStagesExtStmt :=
  d2cStages_ext_of_p2c_and_leaves
    (fun P A ext hOk himg =>
      stageP2PathCOver_qpan_ext_of_hkdf_init hOk himg
        (fun X => hHkdfExt P A ext X hOk himg)
        (fun X => hHkdfExp P A ext X hOk himg)
        (hInit P A ext hOk himg))
    hHkdfExt hHkdfExp hInit hTryDec

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
