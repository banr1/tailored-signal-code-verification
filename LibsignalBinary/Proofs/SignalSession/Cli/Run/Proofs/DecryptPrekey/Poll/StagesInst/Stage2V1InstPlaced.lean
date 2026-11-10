/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Inst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathATopPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.E2E.Pqxdh.FullPlacementCorollaries
public import LibsignalBinary.Proofs.CliC
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfSpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.ShimsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedB
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecPlaced

/-!
# Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Instantiation

Defines `StageP2V1KitsPlacedStmt` and proves `stageP2PathA_qpan_cli_placed_of_kits`,
`stageP2PathA_qpan_cli_placed_of_seams`, and `[LibsignalFullPlacement]`
`stageP2PathA_qpan_cli_full_placed_of_seams`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns cliGhostExterns_other)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  p2ErrFrameAtPlaced p2OkPostAtPlaced stageP2PreAtPlaced stageP2V1KitsAtPlacedProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX initialStateValue)
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst hiding
  cliPreKeyStoreSpecPlaced cliSignedPreKeyStoreSpecPlaced cliKyberPreKeyStoreSpecPlaced
  cliPreKeyStoreSpecPlaced_quiet cliSignedPreKeyStoreSpecPlaced_quiet

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem cliPollSpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

private theorem cliPollKpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

private theorem cliPollPk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

private theorem cliPollPk_opkOkEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

private theorem cliPollPk_opkOkUpdate_placed (A : RustAlloc) [LibsignalPlacement] (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) StoresGhost.opened.oneTime opt wOpk =
      StoresGhost.opened.oneTime := by
  cases opt <;> rfl

private theorem cliPollSelf_kpEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

private theorem cliPollSelf_regIdEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKitPlaced A F peer σ).regIdEvs ans = [] := rfl

private def pathAIkBSk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.privateKey.bytes
  | .error _ => List.replicate 32 0

private def pathAIkBPk (F : FsFiles) : SignalPqxdh.Bytes :=
  match StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => E2E.vecU8 kp₀.identityKey.publicKey.bytes
  | .error _ => List.replicate 32 0

private theorem pathAIkBSk_length (F : FsFiles) : (pathAIkBSk F).length = 32 := by
  dsimp only [pathAIkBSk]; split
  · exact vecU8_length _
  · simp

private theorem pathAIkBPk_length (F : FsFiles) : (pathAIkBPk F).length = 32 := by
  dsimp only [pathAIkBPk]; split
  · exact vecU8_length _
  · simp

private theorem pathAIkBSk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBSk F = E2E.vecU8 kp.privateKey.bytes := by
  dsimp only [pathAIkBSk]; rw [h]

private theorem pathAIkBPk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBPk F = E2E.vecU8 kp.identityKey.publicKey.bytes := by
  dsimp only [pathAIkBPk]; rw [h]

private theorem cliPollSelf_kpRel_sk_eq_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced A F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.privateKey.bytes.toList = bytesToBv8 (pathAIkBSk F) := by
  have hkpEq := cliPollSelf_kpRel_ok_placed hrel
  dsimp only [pathAIkBSk]
  rw [hkpEq, bytesToBv8_vecU8]

private theorem cliPollSelf_kpRel_pk_eq_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced A F peer σ).kpRel StoresGhost.opened.identity (.ok kp)) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (pathAIkBPk F) := by
  have hkpEq := cliPollSelf_kpRel_ok_placed hrel
  dsimp only [pathAIkBPk]
  rw [hkpEq, bytesToBv8_vecU8]

/-- Relocatable `[LibsignalPlacement]` continuation/postcondition telescope of `stageP2_v1_kits_at`
on `dpPollProgPlaced ext` (`b := 0#64`). -/
abbrev stageP2V1KitsAtPlacedProp := @Kits.stageP2V1KitsAtPlacedProp

/-- Relocatable `[LibsignalPlacement]` counterpart of `StageP2V1KitsExtStmt`. -/
def StageP2V1KitsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State)),
    StructuralPrims P →
    RunHooksPlaced A ext →
    ∀ (ikit : IdentityStoreSpec A 0#64) (skit : IdentitySelfStoreSpec ikit),
      (lsmpl.base 547 ≠ 0#64 → IdentitySelfVtablesPlacedOk ikit skit) →
      ∀ (spkKit : SignedPreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → SignedPreKeyVtablesPlacedOk spkKit) →
      ∀ (kpkKit : KyberPreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → KyberPreKeyVtablesPlacedOk kpkKit) →
      ∀ (pkKit : PreKeyStoreSpec A 0#64),
        (lsmpl.base 547 ≠ 0#64 → PreKeyVtablesPlacedOk pkKit) →
      ∀ (stk : Nat), stageP2V1CallStack spkKit kpkKit pkKit skit ≤ stk →
      stageP2V1KitsAtPlacedProp P A F ext skit spkKit kpkKit pkKit stk

set_option maxHeartbeats 1600000 in
private theorem stageP2PathA_qpan_cli_memInv_placed_of_at [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hAt : ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
      (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      Kits.stageP2V1KitsMemInvAtPlacedProp Φ
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (dpClosSubStack B)) :
    StageP2PathAQpanCliMemInvPlacedStmt Φ mmpl gh W := by
  intro X B S Scope y g1 s0 s1 sp rngPtr v_a8 v_b8 v_d0 Q Qpan
    hh hread hdeser hcoins hdecOk hScope hFok hloadNone htrust hg1 hfs1 hCode1 htr01
    hsp1 hsp0 hsub hpc1 hrun1 halign1 hregs1 hpan herr hok
  subst hg1
  rcases hregs1 with ⟨hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16,
    _, hx19, _, hx22, hx23, hx24, _, _, hx29, hvregs1⟩
  obtain ⟨m, i, _, hi, hpm, hpkToE⟩ := pathA_pm_typed hdecOk
  have hfp_reg : s1.readReg64 .x29 = sp + 0xc70#64 := x29_eq_sp_add_c70 hsp0 hx29
  have hsp_align : (sp &&& 15#64 == 0#64) = true := by rw [← hsp1]; exact halign1
  refine sepWPp_with_steps ?_
  refine sepWPp_conseq_pre
    (stageP2_entry_unpack_pathA_placed y m i s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0
      hpm rfl hdecOk hFok hScope) ?_
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_left fun hopkWord => ?_
  refine sepWPp_conseq_pre
    (stageP2PreAt_dup_kyberPtr_placed y m i w s0 sp (sp + 0xc70#64) rngPtr v_a8 v_b8 v_d0) ?_
  refine SepWPp.pure_left fun hctBuf_nz => ?_
  let ikBSk : SignalPqxdh.Bytes := pathAIkBSk y.g.F
  let ikBPk : SignalPqxdh.Bytes := pathAIkBPk y.g.F
  have hikBSk_len : ikBSk.length = 32 := pathAIkBSk_length y.g.F
  have hikBPk_len : ikBPk.length = 32 := pathAIkBPk_length y.g.F
  have hkp_sk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk :=
    cliPollSelf_kpRel_sk_eq_placed
  have hkp_pk : ∀ kp : IdentityKeyPair,
      (cliPollSelfKitPlaced E2E.HooksE.A0 y.g.F y.g.peer (cliKitStk B)).kpRel
        StoresGhost.opened.identity (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk :=
    cliPollSelf_kpRel_pk_eq_placed
  let err0 : ApiError AddrVal Unit := .protocol .invalidKeyAgreement
  have herr0_p : err0 ≠ .panic := by nofun
  have herr0_s : err0 ≠ .store () := by nofun
  exact hAt X B y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey hh hread
    s0 s1 (pathAInnerFramePlaced y m i rngPtr sp)
    (fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Q sf Pf)
    (Qp := fun sf Pf => Steps (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf → Qpan sf Pf)
    (fun sf Pf hp _ => by
      have hp' := poll_panicOomProp_of_matched emp hp
      rw [sepConj_emp] at hp'
      exact hpan sf Pf hp')
    sp (sp + 0xc70#64) y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
    y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
    y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
    (mkPathAHdr m) ikBSk ikBPk i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
    w.opkWord m.kpkId m.regId m.spkId
    StoresGhost.opened.signed StoresGhost.opened.kyber
    StoresGhost.opened.oneTime StoresGhost.opened.identity
    y.g.me y.g.peer
    hctBuf_nz (sp_sub_576_ne_zero B hsub) hsub
    hikBSk_len hikBPk_len
    (vecU8_length m.idPub) (vecU8_length m.baseKey) (vecU8_length m.kyberCt)
    hCode1
    (cliPollStageP2_fsAt_placed hh y.g.F y.g.peer m.spkId m.kpkId w.opkWord y.g.msg.baseKey B hfs1)
    rfl
    (fun r hrel _ => cliPollSpk_wf_of_preKeysWf_placed hdecOk.preKeysWf r hrel)
    rfl
    (fun r hrel _ => cliPollKpk_wf_of_preKeysWf_placed hdecOk.preKeysWf r hrel)
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid))
    (fun id hid => hopkWord id ((hdrOpkIdBv?_mkPathAHdr m).symm.trans hid) |>.symm)
    (fun id r _ hrel _ => cliPollPk_wf_of_preKeysWf_placed hdecOk.preKeysWf r hrel)
    hkp_sk hkp_pk
    (Or.inr (distinctSid_of_decPkOk₀ hdecOk))
    hpc1 hrun1 hsp1 hsp_align htr01 hvregs1
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hfp_reg
    -- SPK lookup error
    (fun e sf Pf hspkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, List.append_nil] at htr_f
      have hspkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_spk_err
          ((cliSpk_getRel_error_iff (A := E2E.HooksE.A0) (b := 0#64) cliIo.rd y.g.F cliWrOk m.spkId
            (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll
            StoresGhost.opened.signed m.spkId).mp ⟨e, hspkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hspkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollSpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F m.spkId (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- KPK lookup error
    (fun spkRec e sf Pf _ _ hkpkErr hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, List.append_nil, List.append_nil] at htr_f
      have hkpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_kpk_err
          ((cliKpk_getRel_error_iff (A := E2E.HooksE.A0) cliIo.rd y.g.F cliWrOk m.kpkId
            StoresGhost.opened.kyber m.kpkId).mp ⟨e, hkpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hkpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollKpk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- OPK lookup error
    (fun spkRec kpkRec opkId e sf Pf _ _ _ _ hopkHdr hpkErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, cliPollPk_getEvs_placed,
          List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hmOpk : m.opkId = some opkId := (hdrOpkIdBv?_mkPathAHdr m).symm.trans hopkHdr
      have hpkNone : pkStoreKeys y.g.F m = none :=
        pkStoreKeys_eq_none_of_opk_err hmOpk
          ((cliPk_getRel_error_iff (A := E2E.HooksE.A0) (b := 0#64) cliIo.rd y.g.F cliWrOk w.opkWord
            (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
            (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll
            StoresGhost.opened.oneTime opkId).mp ⟨e, hpkErr⟩)
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inl hpkNone)
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (cliPollPk_getErr_entails_decResAt_anyHeap E2E.HooksE.A0 0#64
          y.g.F w.opkWord (cliKitStk B) y.out e err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Identity keypair lookup error
    (fun spkRec kpkRec wOpk e sf Pf _ _ _ _ _ hkpErr hpc_f hrun_f htr_f hsp_f
        hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, cliPollPk_opkOkEvs_placed,
          cliPollSelf_kpEvs_placed, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpNone := cliPollSelf_kpRel_err_placed hkpErr
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inl hkpNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_kpErr_entails_decResAt_err E2E.HooksE.A0 0#64
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- PQXDH acceptKeys rejection
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf Pf
        hspkRel _ _ _ hspkPubEq hspkPrivEq hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccNone _ _
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, cliPollPk_opkOkEvs_placed,
          cliPollSelf_kpEvs_placed, List.append_nil, List.append_nil, List.append_nil,
          List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, _, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk hspkRel hspkPubEq hspkPrivEq
        hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkpOk hikBSk_ok hikBPk_ok
      have haccNone0 : ∀ reg : BitVec 32,
          SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = none := by
        intro reg
        have hmap :
            (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
              (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)).map
                ofSignalPqxdhDRKey = none := by
          rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp reg]
          exact haccNone
        exact Option.map_eq_none_iff.mp hmap
      have hmod := decPkDef_pathA_accept_none_anyReg X ⟨W.C, W.Q⟩ Scope y.g.F
        y.g.peer.val y.g.me.val y.g.msg y.g.coins hloadNone htrust hpkToE hi hk hkpOk haccNone0
      have hPf' := Entails.trans hPf (by rw [← sepConj_assoc]; exact Entails.refl _)
      have hpost := Entails.trans hPf' (Entails.trans
        (sepConj_mono_left (pqxdhAcceptErr_entails_decResAt_anyHeap y.out errTag w2 w3 w4 w5 w6 err0))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Local registration-ID lookup error
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey e sf Pf
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hregErr
        hpc_f hrun_f htr_f hsp_f hcs_f hvregs_f hinv_f hPf hSteps => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, cliPollPk_opkOkEvs_placed,
          cliPollSelf_kpEvs_placed, cliPollSelf_regIdEvs_placed, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil, List.append_nil] at htr_f
      have hopkUpd := cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      rw [hopkUpd] at hPf
      have hregNone := cliPollSelf_regIdRel_err_placed hregErr
      have hmod := decPkDef_pathA_lookup_err X ⟨W.C, W.Q⟩ Scope y.g.F y.g.peer.val y.g.me.val
        y.g.msg y.g.coins hloadNone rfl htrust hpkToE (Or.inr (Or.inr hregNone))
      have hpost := Entails.trans hPf (Entails.trans
        (sepConj_mono_left (entails_decResAt_anyHeap_of_err y.out err0
          (cliPollSelf_regIdErr_entails_decResAt_err E2E.HooksE.A0 0#64
            y.g.F y.g.peer (cliKitStk B) y.out e err0)))
        (p2ErrFrame_fold_pathA_placed y m i w s0 sp (sp + 0xc70#64) rngPtr err0 hpm rfl hopkWord))
      exact herr sf Pf hpc_f hrun_f hSteps (hsp_f.trans hsp0) hcs_f hvregs_f hinv_f
        ⟨err0, herr0_p, herr0_s, htr_f, hmod, hpost⟩)
    -- Success case: `+0x1778` fresh Bob V1 session
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey localRegId G_bob s2
        hspkRel _ hspkPub_len hspkPriv_len hspkPubEq hspkPrivEq
        hkpkRel _ _ _ hkpkPubEq hkpkPrivEq
        hopkOk _ _ hopkBytes hkpRel haccSome hregRel
        hG_pend hG_kyb hG_alice hG_regs
        hSteps12 _ hpc2 hrun2 hsp2 htr2
        _ _ _ _ hx19_2 _ _ _ _ _ _ hx27_2 _ hx29_2
        hvregs2 _hCode2 => by
      rw [cliPollSpk_getEvs_placed, cliPollKpk_getEvs_placed, cliPollPk_opkOkEvs_placed,
          cliPollSelf_kpEvs_placed, cliPollSelf_regIdEvs_placed, List.append_nil, List.append_nil,
          List.append_nil, List.append_nil, List.append_nil] at htr2
      have hopkUpd := cliPollPk_opkOkUpdate_placed E2E.HooksE.A0 y.g.F w.opkWord (cliKitStk B)
        (hdrOpkIdBv? (mkPathAHdr m)) wOpk
      have hkpOk := cliPollSelf_kpRel_ok_placed hkpRel
      have hregOk := cliPollSelf_regIdRel_ok_placed hregRel
      have hikBSk_ok : ikBSk = E2E.vecU8 kp.privateKey.bytes := pathAIkBSk_of_ok hkpOk
      have hikBPk_ok : ikBPk = E2E.vecU8 kp.identityKey.publicKey.bytes := pathAIkBPk_of_ok hkpOk
      obtain ⟨k, hk, hspkPub_eq, _, hinp⟩ := pathA_acceptInput_agree_placed hdecOk
        hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes
        hkpOk hikBSk_ok hikBPk_ok
      have hmapSome :
          (SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
            (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m)).map
              ofSignalPqxdhDRKey = some drKey := by
        rw [← Model.acceptKeys_ofSignalPqxdhPrimitives, ← hinp localRegId]
        exact haccSome
      obtain ⟨dk0, haccModel, hdk0⟩ := Option.map_eq_some_iff.mp hmapSome
      have hikBPk_bv :
          bytesToBv8 ikBPk = (keyPairOf W.C kp.privateKey.bytes).publicKey.bytes.toList := by
        rw [hikBPk_ok, hdecOk.idPairDerived kp hkpOk, bytesToBv8_vecU8]
      have hst_eq := p2BobInitSessionV1_eq_pathAInitState (cliModelPrims_structural X W)
        W kp localRegId k m drKey dk0 ikBPk spkPubBytes
        (mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes)
        hikBPk_len (vecU8_length m.idPub)
        (by simp [toU8, hspkPub_len])
        (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len])
        haccSome hdk0 (hinp localRegId) hikBPk_bv hspkPub_eq
      have hextra := sessionExtraRel_pathAInitSession W kp localRegId k m dk0 G_bob
        hG_pend hG_kyb hG_alice hG_regs
      have hmsg_reasm :
          signalMessageAt E2E.HooksE.A0 y.g.msgG.msg y.g.msgA y.g.msg.message ∗
          ((y.g.msgA + 0xa8#64) ↦ₛ y.g.msg.baseKey.bytes.toList) ∗
          ((y.g.msgA + 0xc8#64) ↦ₛ y.g.msg.identityKey.publicKey.bytes.toList) ∗
          preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg ⊢
          preKeyMsgAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg := by
        rw [preKeyMsgAt_eq_base_idKey_sep]
        exact Entails.of_eq (by ac_rfl)
      have halign2 : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have hx29_sp0 : s2.readReg64 .x29 = s0.sp - 0x60#64 := x29_eq_sp0_sub_60 hsp0 hx29_2
      rw [hst_eq, hopkUpd]
      exact sepWPp_drop_steps hSteps12 (sepWPp_conseq_pre
        (p2OkPost_fold_pathA_placed y m i w s0 s2 sp (sp + 0xc70#64) rngPtr G_bob
          (pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, localRegId⟩ k m dk0)
          hpm hcoins hsub rfl hopkWord hsp2 hx19_2 hx27_2)
        (hok s2 m i k kp localRegId dk0 G_bob y.g.msgA y.g.msgG.msg
          (preKeyMsgRemBaseIdKeyAt E2E.HooksE.A0 y.g.msgG y.g.msgA y.g.msg)
          hpm hi hk hkpOk hregOk haccModel hextra hmsg_reasm
          hSteps12 htr2 hpc2 hrun2 hsp2 halign2 hx19_2 hx27_2 hx29_sp0 hvregs2
          (hInv.of_keepsFrozen hCode1 hSteps12.keepsFrozen))))

private theorem stageP2PathA_qpan_cli_placed_of_at [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hAt : ∀ (X : UnreachedPqxdhPrimitives) (B : RunBudgets)
      (F0 : FsFiles) (peer : AddrGhost) (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      stageP2V1KitsAtPlacedProp
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
        (cliGhostExterns gh (cliExternsPlaced mmpl W))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (dpClosSubStack B)) :
    StageP2PathAQpanCliPlacedStmt mmpl gh W :=
  stageP2PathA_qpan_cli_memInv_placed_of_at StageP2MemInv.codeRoLoaded mmpl gh W hAt

/-- Stage P2 Path A (`+0x0868 -> +0x1778` or `s0.x30` error) from `StageP2V1KitsPlacedStmt`. -/
theorem stageP2PathA_qpan_cli_placed_of_kits [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hKits : StageP2V1KitsPlacedStmt) :
    StageP2PathAQpanCliPlacedStmt mmpl gh W :=
  stageP2PathA_qpan_cli_placed_of_at mmpl gh W fun X B F0 peer spkId kpkId opkWord kbk hh _ =>
    hKits
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (cliModelPrims_structural X W)
      hh
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B))
      (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
      (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
      (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B))
      (dpClosSubStack B)
      (stageP2V1CallStack_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
        spkId kpkId opkWord kbk B)

private theorem hookSat_sessionMemcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat)
    (h : HookSat H sym CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec) :
    HookSat H sym (CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      ProofLib.libcMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      ProofLib.memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.sessionMemcpySpec,
      CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem framelessMemcpySpec_eq_sessionMemcpyRegionSpec :
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec =
      CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec := rfl

theorem cliStageP2ClosureHooksPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2ClosureHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  exact StageP2ClosureHooksPlaced.of_hooks
    hh.codecHooks.shim
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpy_of_frameless allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)

private theorem cliUuidTryParse_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok
      ((blkPC_252).rebase (blkPl_252).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
  refine subroutine_ok_map_panic
    (UuidFs.uuidTryParse_placed_okFs_F (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_, fun _ hpan => ?_⟩)
    (fun _ _ _ _ _ _ he => False.elim (by
      rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onExit _ _ _ _ =
        ⌜False⌝ from rfl, satisfies_pure_sepConj] at he; exact he.1))
    (fun _ _ _ _ _ _ _ ho => False.elim (by
      rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onOom _ _ _ =
        ⌜False⌝ from rfl, satisfies_pure_sepConj] at ho; exact ho.1))
  · dsimp only [withLsCodeLoaded, Spec.keepsFs] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.2
  · rw [show (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse).keepsFs).onPanic _ _ _ =
      ⌜False⌝ from rfl, satisfies_pure_sepConj] at hpan; exact False.elim hpan.1

private theorem cliIsSameAccount_placed_ok_on_stageP1 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (stageP1ProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec E2E.HooksE.A0 uuidTryParse)) :=
  Kits.isSameAccount_placed_ok_on_stageP1
    (IdKit.cliGhostExterns_blackBox mmpl gh W) (cliUuidTryParse_placed_ok mmpl gh W)

theorem cliStageP2PureCalleesPlaced_of_seams [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0)) :
    StageP2PureCalleesPlaced
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0 W.C.F
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  exact StageP2PureCalleesPlaced.of_hooks (cliModelPrims_structural X W)
    hh.codecHooks.shim hh.codecHooks.alloc
    hh.codecHooks.dealloc hh.codecHooks.memcpy
    (framelessMemcpySpec_eq_sessionMemcpyRegionSpec ▸ hh.codecHooks.memcpy)
    (hookSat_sessionMemcpy_of_frameless allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (cliIsSameAccount_placed_ok_on_stageP1 mmpl gh W) h_accept hS.initialStateMemInv_lsProg75

theorem cliStageP2PureCalleesPlaced4K_of_seams [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hS : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 79)
      (pqxdhAcceptOptFieldsPlacedSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0)) :
    StageP2PureCalleesPlaced4K (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      E2E.HooksE.A0 W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  exact StageP2PureCalleesPlaced4K.of_hooks (cliModelPrims_structural X W)
    hh.codecHooks.shim hh.codecHooks.alloc hh.codecHooks.dealloc
    (framelessMemcpySpec_eq_sessionMemcpyRegionSpec ▸ hh.codecHooks.memcpy)
    (hookSat_sessionMemcpy_of_frameless allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (Kits.isSameAccount_4k_placed_ok_on_stageP1
      (IdKit.cliGhostExterns_blackBox mmpl gh W) (cliUuidTryParse_placed_ok mmpl gh W))
    h_accept hS.initialStateMemInv_lsProg75

private theorem cliPollSpk_getShim_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getShimOff) (withLsRoCl lsmpl (kitSpkGetShimSpec spkKit)) := by
  intro spkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 606)
    (Store.PkShims.spkGetShim_placed_ok_of_deps hh.alloc hh.panics
      (stk := (cliKitStk B).spkGetShim) (by dsimp [cliKitStk]; omega)) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 606) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun x R s0 hp => ?_
  dsimp only [withLsRoCl, kitSpkGetShimSpec, spkKit, cliPollSpkKitPlaced,
    Poll.cliSignedPreKeyStoreSpecPlaced, cliSignedPreKeyStoreSpec] at hp ⊢
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).spkGetShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  rw [satisfies_pure_sepConj] at hp1
  exact ⟨⟨x.self, x.id⟩, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl))
    ((satisfies_pure_sepConj ..).mpr ⟨hp1.1.2, hp1.2⟩),
    fun sf hq => by simpa only [BitVec.zero_add] using hq, fun _ hpan => hpan⟩

private theorem cliPollKpk_getShim_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.getShimOff) (withLsRoCl lsmpl (kitKpkGetShimSpec kpkKit)) := by
  intro kpkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 611)
    (Store.PkShims.kpkGetShim_placed_ok_of_deps hh.alloc hh.panics
      (stk := (cliKitStk B).kpkGetShim) (by dsimp [cliKitStk]; omega)) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 611) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun x R s0 hp => ?_
  dsimp only [withLsRoCl, kitKpkGetShimSpec, kpkKit, cliPollKpkKitPlaced,
    cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec] at hp ⊢
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkGetShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  rw [satisfies_pure_sepConj] at hp1
  exact ⟨⟨x.self, x.id⟩, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl))
    ((satisfies_pure_sepConj ..).mpr ⟨hp1.1.2, hp1.2⟩),
    fun sf hq => by simpa only [BitVec.zero_add] using hq, fun _ hpan => hpan⟩

private theorem cliPollPk_getShim_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.getShimOff) (withLsRoCl lsmpl (kitPreKeyGetShimSpec pkKit)) := by
  intro pkKit
  have h608 := Store.PkShims.pkGetShim_placed_ok_of_deps hh.alloc hh.panics
    (stk := (cliKitStk B).pkGetShim) (by dsimp [cliKitStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 608)
    h608 hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 608) _; rw [BitVec.zero_add]
  refine subroutine_ok_map_panic hrocl fun x R s0 hp => ?_
  dsimp only [withLsRoCl, kitPreKeyGetShimSpec, pkKit, cliPollPkKitPlaced,
    Poll.cliPreKeyStoreSpecPlaced, cliPreKeyStoreSpec] at hp ⊢
  have hp1 : s0.mem ⊨ ⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkGetShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  rw [satisfies_pure_sepConj] at hp1
  have hp2 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗
    (E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkGetShim ∗
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R) := (satisfies_pure_sepConj ..).mpr ⟨hp1.1.2, hp1.2⟩
  refine ⟨⟨x.self, x.id⟩, R, Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp2, fun sf hq => ?_, fun _ hpan => hpan⟩
  simpa only [BitVec.zero_add] using hq

private theorem cliSignedHooksPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    SignedHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  dealloc := hh.codecHooks.dealloc
  decodeErrorFrom :=
    subroutine_ok_withLsCodeLoaded_of_plain
      (Prost.decode_error_from_placed_ok
        hh.codecHooks.shim hh.codecHooks.alloc hh.codecHooks.panic_alloc)
  decodeErrorPush :=
    Assembly.decode_error_push_spec_placed_ok
      hh.codecHooks.panic_raw hh.codecHooks.shim hh.codecHooks.alloc hh.codecHooks.realloc

theorem cliDecodeKyberPreKey_placed_ok_of_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (RecordCodecs.Placed.lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec E2E.HooksE.A0) :=
  cliDecodeKyberPreKey_placed_ok mmpl gh W (cliSignedHooksPlaced mmpl gh W hh)
    (CryptoVerification.CliC.signedPortDepsPlaced_ok hh.codecHooks)

private theorem cliDecodeSignedPreKey_placed_ok_of_hooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (RecordCodecs.Placed.lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 595)
      (decodeSignedPreKeyPlacedSpec E2E.HooksE.A0) :=
  cliDecodeSignedPreKey_placed_ok mmpl gh W (cliSignedHooksPlaced mmpl gh W hh)
    (CryptoVerification.CliC.signedPortDepsPlaced_ok hh.codecHooks)

private theorem cliPollSpk_getPoll_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getPollOff)
      (withLsRoCl lsmpl (kitSpkGetPollSpecE spkKit)) := by
  intro spkKit
  have hDec := SessKit.cliDecimal_placed_ok hh
  have hGet := SessKit.cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hh
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
  have hhop := Store.SpkGetPoll.spkGetPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (spkDecProg := RecordCodecs.Placed.lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (spkDecBlk := 595)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).spkGetPoll)
    hh.alloc hDec hGet (cliDecodeSignedPreKey_placed_ok_of_hooks mmpl gh W hh)
    (Store.DropSpeWord.dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_571 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 571)
    (Nat.le_refl _) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 571) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_map_panic hhop ?_)
  rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
  change DirGhost at st0
  dsimp only [StoreKit.withLsCodeRoLoaded, kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec,
    spkKit, cliPollSpkKitPlaced, Poll.cliSignedPreKeyStoreSpecPlaced,
    cliSignedPreKeyStoreSpec, cliSpkStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = spkId⌝ ∗
      (⌜CliSpkInv cliIo.rd F0 cliWrOk spkId st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0 ∗ memRegion out 88 ∗
        E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).spkGetPoll ∗ R)))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, rfl⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
  have hm_hop : s0.mem ⊨
      (spkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).spkGetPoll).pre
        ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
    dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, StoreKit.withLsCodeRoLoaded]
    have h1 : s0.mem ⊨
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          PkNameOk cliWrOk st0 id ∧ PkSizeOk cliIo.rd s0.fs.files st0 id⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0 ∗ memRegion out 88 ∗
          E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).spkGetPoll ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
  refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
  intro sf hpost
  dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, StoreKit.withLsCodeRoLoaded] at hpost
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hpost
  obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
  rw [hfiles] at hpa; subst hpa
  have hent := KitInst.spkAnsAt_entails_pollOut_placed E2E.HooksE.A0 cliIo.rd F0 cliWrOk id
    (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll st0 id out
  dsimp only at hent
  have hout_eq : spkGetPollOutAt (KitInst.cliSignedPreKeyStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F0
      cliWrOk id (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll) out =
      spkGetPollOutAt spkKit out := by funext ans; cases ans <;> rfl
  rw [hout_eq] at hent
  have hm' := Arm64.Satisfies.mono (sepConj_mono_left hent) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm'
  obtain ⟨ans, hrel, hm'⟩ := hm'
  dsimp only [StoreKit.withLsCodeRoLoaded, kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec,
    spkKit, cliPollSpkKitPlaced, Poll.cliSignedPreKeyStoreSpecPlaced,
    cliSignedPreKeyStoreSpec, cliSpkStoreAt]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  have hgoal : sf.mem ⊨
      ⌜spkKit.getRel st0 id ans ∧ sf.trace = s0.trace ++ []⌝ ∗
      (⌜CliSpkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
        (spkGetPollOutAt spkKit out ans ∗ pkBoxAt fut self id 1#8 ∗
          dirAt E2E.HooksE.A0 self st0 ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).spkGetPoll ∗ R)) := by
    rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
  dsimp only [spkKit, cliPollSpkKitPlaced, Poll.cliSignedPreKeyStoreSpecPlaced,
    cliSignedPreKeyStoreSpec] at hgoal
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

theorem cliPollSpk_kitPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (spkId : BitVec 32) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile)) :
    SignedPreKeyStoreKitPlacedOk
      (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollSpk_getShim_rocl mmpl gh W B F0 spkId hh hblk
  getPoll hblk := cliPollSpk_getPoll_rocl mmpl gh W B F0 spkId hh hread hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_getPoll_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.getPollOff)
      (withLsRoCl lsmpl (kitPreKeyGetPollSpecE pkKit)) := by
  intro pkKit
  have hDec := SessKit.cliDecimal_placed_ok hh
  have hGet := SessKit.cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hh
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hread)
  have hhop := Store.PkGetPoll.pkGetPoll_placed_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (pkDecProg := RecordCodecs.Placed.lsProg_65 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (pkDecBlk := 65)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).pkGetPoll)
    hh.alloc hDec hGet (cliPreKeyDeserialize_placed_ok mmpl gh W hh)
    (Store.DropSpeWord.dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_573 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 573)
    (Nat.le_refl _) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 573) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_map_panic hhop ?_)
  rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
  change DirGhost at st0
  dsimp only [StoreKit.withLsCodeRoLoaded, kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec,
    pkKit, cliPollPkKitPlaced, Poll.cliPreKeyStoreSpecPlaced,
    cliPreKeyStoreSpec, cliPkStoreAt] at hpre
  have hpre' : s0.mem ⊨
      ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗
      (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = pkId⌝ ∗
      (⌜CliPkInv cliIo.rd F0 cliWrOk pkId st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0 ∗ memRegion out 56 ∗
        E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkGetPoll ∗ R)))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, rfl⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
  have hm_hop : s0.mem ⊨
      (pkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).pkGetPoll).pre
        ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
    dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, StoreKit.withLsCodeRoLoaded]
    have h1 : s0.mem ⊨
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          PkNameOk cliWrOk st0 id ∧ PkSizeOk cliIo.rd s0.fs.files st0 id⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0 ∗ memRegion out 56 ∗
          E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).pkGetPoll ∗ R)) := by
      rw [satisfies_pure_sepConj]; refine ⟨hcrl, ?_⟩
      rw [satisfies_pure_sepConj]; exact ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk⟩, hsp⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
  refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
  intro sf hpost
  dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, StoreKit.withLsCodeRoLoaded] at hpost
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hpost
  obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost
  rw [hfiles] at hpa; subst hpa
  have hent := KitInst.pkGetAnsAt_entails_pollOut_placed E2E.HooksE.A0 cliIo.rd F0 cliWrOk id
    (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
    (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll st0 id out
  dsimp only at hent
  have hout_eq : preKeyGetPollOutAt (KitInst.cliPreKeyStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F0
      cliWrOk id (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
      (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll) out =
      preKeyGetPollOutAt pkKit out := by funext ans; cases ans <;> rfl
  rw [hout_eq] at hent
  have hm' := Arm64.Satisfies.mono (sepConj_mono_left hent) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm'
  obtain ⟨ans, hrel, hm'⟩ := hm'
  dsimp only [StoreKit.withLsCodeRoLoaded, kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec,
    pkKit, cliPollPkKitPlaced, Poll.cliPreKeyStoreSpecPlaced,
    cliPreKeyStoreSpec, cliPkStoreAt]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  have hgoal : sf.mem ⊨
      ⌜pkKit.getRel st0 id ans ∧ sf.trace = s0.trace ++ []⌝ ∗
      (⌜CliPkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
        (preKeyGetPollOutAt pkKit out ans ∗ pkBoxAt fut self id 1#8 ∗
          dirAt E2E.HooksE.A0 self st0 ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).pkGetPoll ∗ R)) := by
    rw [satisfies_pure_sepConj]; refine ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩, ?_⟩
    rw [satisfies_pure_sepConj]; exact ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩
  dsimp only [pkKit, cliPollPkKitPlaced, Poll.cliPreKeyStoreSpecPlaced,
    cliPreKeyStoreSpec] at hgoal
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

theorem cliPollPk_kitPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (pkId : BitVec 32) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile)) :
    PreKeyStoreKitPlacedOk
      (cliPollPkKitPlaced E2E.HooksE.A0 F0 pkId (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollPk_getShim_rocl mmpl gh W B F0 pkId hh hblk
  getPoll hblk := cliPollPk_getPoll_rocl mmpl gh W B F0 pkId hh hread hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk
  removeShim hblk :=
    (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hread).removeShim hblk
  removePoll hblk :=
    (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hread).removePoll hblk
  removeFutDrop hblk :=
    (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hread).removeFutDrop hblk

private theorem cliPollKpk_getPoll_rocl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hKpkGetPoll : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 576)
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.getPollOff)
      (withLsRoCl lsmpl (kitKpkGetPollSpecE kpkKit)) := by
  intro kpkKit
  have hhop := Store.PlacedCommon.ls_transfer_lscro (callerProg := callerProg) (j := 518)
    hKpkGetPoll hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 576) _; rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_map_panic hhop ?_)
  rintro ⟨⟨fut, out, self, id⟩, st0⟩ R s0 hpre
  change KyberGhost at st0
  dsimp only [StoreKit.withLsCodeRoLoaded, kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec,
    kpkKit, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced,
    cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkGetSide, cliKpkStoreAtFull] at hpre
  have hpre' : s0.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (⌜s0.fs.files = F0⌝ ∗
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧ id = kpkId⌝ ∗
      (⌜CliKpkInvFull cliIo.rd F0 cliWrOk kpkId spkId kbk st0⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0.oneTime ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
          E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll ∗ R)))) :=
    Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcrl, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨_, hx0, hx8, rfl⟩, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hsp⟩ := hpre'
  have hm_hop : s0.mem ⊨
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll).pre
        ⟨fut, out, self, id, st0⟩ s0 ∗ R := by
    dsimp only [kpkGetPollSpecPlaced, StoreKit.withLsCodeRoLoaded]
    have h1 : s0.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          PkNameOk cliWrOk st0.oneTime id ∧ PkNameOk cliWrOk st0.lastResort id ∧
          PkSizeOk cliIo.rd s0.fs.files st0.oneTime id ∧
          PkSizeOk cliIo.rd s0.fs.files st0.lastResort id⌝ ∗
        (pkBoxAt fut self id 0#8 ∗ dirAt E2E.HooksE.A0 self st0.oneTime ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
          E2E.HooksE.A0.pool ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll ∗ R)) :=
      (satisfies_pure_sepConj ..).mpr ⟨hcrl, (satisfies_pure_sepConj ..).mpr
        ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
          hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk⟩, hsp⟩⟩
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1
  refine ⟨⟨fut, out, self, id, st0⟩, R, hm_hop, ?_, fun _ hp => hp⟩
  intro sf hpost
  dsimp only [kpkGetPollSpecPlaced, StoreKit.withLsCodeRoLoaded] at hpost
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hpost
  obtain ⟨pa, ⟨hpa, htr⟩, hm⟩ := hpost; rw [hfiles] at hpa; subst hpa
  have hent := KitInst.kpkAnsAt_entails_pollOut_placed E2E.HooksE.A0 cliIo.rd F0 cliWrOk id spkId kbk
    (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
    (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll st0 id out
  dsimp only at hent
  have hout_eq : kpkGetPollOutAt (KitInst.cliKyberPreKeyStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F0
      cliWrOk id spkId kbk (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
      (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll) out =
      kpkGetPollOutAt kpkKit out := by funext ans; cases ans <;> rfl
  rw [hout_eq] at hent
  have hm' := Arm64.Satisfies.mono (sepConj_mono_left hent) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm'
  obtain ⟨ans, hrel, hm'⟩ := hm'
  dsimp only [StoreKit.withLsCodeRoLoaded, kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec,
    kpkKit, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced, Poll.cliKyberPreKeyStoreSpecPlaced,
    cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkGetSide, cliKpkStoreAtFull]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  have hgoal : sf.mem ⊨ ⌜kpkKit.getRel st0 id ans ∧ sf.trace = s0.trace ++ []⌝ ∗
      (⌜CliKpkInvFull cliIo.rd F0 cliWrOk id spkId kbk st0⌝ ∗
        (kpkGetPollOutAt kpkKit out ans ∗ pkBoxAt fut self id 1#8 ∗
          dirAt E2E.HooksE.A0 self st0.oneTime ∗
          dirAt E2E.HooksE.A0 (self + 0x28#64) st0.lastResort ∗ E2E.HooksE.A0.pool ∗
          stackAt s0.sp (cliKitStk B).kpkGetPoll ∗ R)) :=
    (satisfies_pure_sepConj ..).mpr ⟨⟨hrel, by rw [List.append_nil]; exact htr⟩,
      (satisfies_pure_sepConj ..).mpr ⟨hinv, Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hm'⟩⟩
  dsimp only [kpkKit, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
    Poll.cliKyberPreKeyStoreSpecPlaced, cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkGetSide] at hgoal
  exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hgoal

theorem cliPollKpk_kitPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey) (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hread : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (hKpkGetPoll : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 576)
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll)) :
    KyberPreKeyStoreKitPlacedOk
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollKpk_getShim_rocl mmpl gh W B F0 kpkId spkId kbk hh hblk
  getPoll hblk := cliPollKpk_getPoll_rocl mmpl gh W B F0 kpkId spkId kbk hKpkGetPoll hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]; exact IdKit.cliIdFutDrop_rocl_placed_ok hblk
  markShim hblk :=
    (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread).markShim hblk
  markPoll hblk :=
    (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread).markPoll hblk
  markFutDrop hblk :=
    (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread).markFutDrop hblk

/-- Path A Stage P2 V1 Instantiation (`StageP2PathAQpanCliPlacedStmt`) from
`(hDropNz : lsmpl.base 547 ≠ 0#64)`, `SpqrV1PlacedSeams`, the Block `79` `Pqxdh::accept` seams,
`hSelfKit`, and `hKpkGetPoll`. -/
theorem stageP2PathA_qpan_cli_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (h_accept : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (h_accept_err : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) E2E.HooksE.A0))
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      IdentitySelfStoreKitPlacedOkI
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkGetPoll : ∀ (B : RunBudgets),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 576)
        (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll)) :
    StageP2PathAQpanCliPlacedStmt mmpl gh W :=
  stageP2PathA_qpan_cli_placed_of_at mmpl gh W fun X B F0 peer spkId kpkId opkWord kbk hh hread =>
    Kits.stageP2_v1_kits_placed
      (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
      (cliStageP2ClosureHooksPlaced mmpl gh W hh)
      (cliStageP2PureCalleesPlaced_of_seams X mmpl gh W hh hSpqr (h_accept X))
      (Kits.initializeBobSession_err_owned_placed_ok_on_stageP1 (h_accept_err X))
      (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
      (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B) hDropNz)
      (hSelfKit B F0 peer hh hread)
      (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
      (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B) hDropNz)
      (cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hread)
      (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B) hDropNz)
      (cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread
        (hKpkGetPoll B hh hread))
      (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
      (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B) hDropNz)
      (cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hread)
      (dpClosSubStack B)
      (stageP2V1CallStack_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
        spkId kpkId opkWord kbk B)

/-- `StageP2BaseCalleesPlaced4K` at `cliGhostExterns gh (cliExternsPlaced mmpl W)` under
`[LibsignalPlacement]`, with zero Block `79` (`Pqxdh::accept`) or Block `327` (`spqr::initial_state`)
seams. -/
theorem cliStageP2BaseCalleesPlaced4K [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2BaseCalleesPlaced4K E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  exact StageP2BaseCalleesPlaced4K.of_hooks
    hh.codecHooks.shim
    hh.codecHooks.alloc
    hh.codecHooks.dealloc
    (hookSat_sessionMemcpy_of_frameless allocHookStack hh.codecHooks.memcpy)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (Kits.isSameAccount_4k_placed_ok_on_stageP1
      (IdKit.cliGhostExterns_blackBox mmpl gh W)
      (cliUuidTryParse_placed_ok mmpl gh W))

private theorem initializeBobSession_err_owned_exactSat_full_placed_ok_on_stageP1
    [LibsignalFullPlacement]
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec) :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec P A)) := by
  have h_acc_err : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (ResponderCore.pqxdhAcceptErrOwnedFrozenPlacedSpec P A) :=
    ResponderCore.pqxdhAccept_err_owned_placed_ok_of_block hWF
      (ResponderCore.ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
      (hH.calculateAgreement_ok hP)
      hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.handleError
  have hbase :=
    ResponderCore.ls_subroutine_ok_withLsFrozen_of_block
      (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext) (i := 518) (j := 75)
      (ResponderCore.initializeBobSession_err_owned_frozen_placed_ok_of_accept h_acc_err)
  refine subroutine_ok_map_panic hbase ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec, withLsFrozen] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec,
        ResponderCore.initializeBobSessionErrOwnedInnerPlacedSpec, withLsFrozen] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun _ hpost => hpost, fun _ hpan => hpan⟩
  dsimp only [StoreKit.withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  exact hpre.2

private theorem initializeBobSession_ok_v1_exactSat_full_placed_on_stageP1
    [LibsignalFullPlacement]
    {P : Initiator.Primitives} {C : Crypto} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hWF : Initiator.StructuralPrims P)
    (hP : ResponderCore.PrimitivesMatchCrypto P C)
    (hH : LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat.PqxdhPlacedHookContractsExactSat
      P C A ext)
    (h_memcpy : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hMemcpySess : HookSat ext lsMemcpySym sessionMemcpyRegionSpec)
    (hinit : CryptoVerification.Cli.E2E.V1.InitialStateMemInvPlacedOk
      (StoreKit.LibsignalCodeRoLoaded lsmpl) A F ext) :
    Kits.InitializeBobV1FrozenOkPlaced P A F ext := by
  have h_acc : subroutine_ok (lsProg_75 ext) (lsmpl.base 79)
      (ResponderCore.pqxdhAcceptOptFieldsFrozenPlacedSpec P A) :=
    ResponderCore.pqxdhAccept_opt_fields_placed_ok_of_block hWF
      (ResponderCore.ecPubKeyIsCanonical_placed_ok_cl hWF hH.dalekMontToEd hH.dalekTorsionFree)
      (hH.calculateAgreement_ok hP)
      (CryptoVerification.E2E.Pqxdh.Shared.vecAppendElements_fast_placed_ok_cl h_memcpy)
      (hH.hkdfExtract_ok hP)
      (hH.hkdfExpandMultiInfo_ok hP)
      hH.noAllocShim hH.alloc hH.dealloc h_memcpy hH.kyberDecaps
      hH.handleError hH.handleAllocError
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  exact ls_sepWPp_of_block (callerProg := stageP1ProgPlaced ext) (calleeProg := lsProg_75 ext)
    (i := 518) (j := 75) (LibsignalCodeLoaded.of_codeLoaded hfr.2)
    (CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_frozen_placed_of_accept
      hWF hH.noAllocShim hH.alloc hH.dealloc hMemcpySess hH.handleError
      h_acc
      (CryptoVerification.Cli.E2E.V1.initialStateMemInvPlacedOk_mono
        (fun _ h => ⟨LibsignalCodeLoaded.of_codeLoaded h.2, h.1⟩) hinit)
      s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hfr hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)
    (by decide) (by decide) (by decide)

/-- Closed `[LibsignalFullPlacement]` Path A Stage P2 V1 Instantiation
(`StageP2PathAQpanCliFrozenPlacedStmt`) discharging Block `79` (`Pqxdh::accept`) via `withLsFrozen`
with zero `h_accept` / `h_accept_err` seams. -/
theorem stageP2PathA_qpan_cli_full_placed_of_seams [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hSelfKit : ∀ (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      IdentitySelfStoreKitPlacedOkI
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hKpkGetPoll : ∀ (B : RunBudgets),
      RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
        (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 576)
        (kpkGetPollSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 (cliKitStk B).kpkGetPoll)) :
    StageP2PathAQpanCliFrozenPlacedStmt mmpl gh W := by
  exact stageP2PathA_qpan_cli_memInv_placed_of_at StageP2MemInv.frozen mmpl gh W
    fun X B F0 peer spkId kpkId opkWord kbk hh hread =>
      Kits.stageP2_v1_kits_frozen_placed
        (P := ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) (A := E2E.HooksE.A0) (F := W.C.F)
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) (cliModelPrims_structural X W)
        (cliStageP2ClosureHooksPlaced mmpl gh W hh)
        (cliStageP2BaseCalleesPlaced4K mmpl gh W hh)
        (cliIsSameAccount_placed_ok_on_stageP1 mmpl gh W)
        (initializeBobSession_err_owned_exactSat_full_placed_ok_on_stageP1
          (cliModelPrims_structural X W) (cliModelPrims_matchCrypto X W)
          (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh)
          hh.codecHooks.memcpy)
        (initializeBobSession_ok_v1_exactSat_full_placed_on_stageP1
          (cliModelPrims_structural X W) (cliModelPrims_matchCrypto X W)
          (cliResponderPqxdhHookContractsPlaced X mmpl gh W hG hh)
          hh.codecHooks.memcpy
          (framelessMemcpySpec_eq_sessionMemcpyRegionSpec ▸ hh.codecHooks.memcpy)
          hSpqr.initialStateMemInv_lsProg75)
        (cliPollIdKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced E2E.HooksE.A0 F0 peer (cliKitStk B))
        (cliPollSelf_vtablesPlacedOk F0 peer (cliKitStk B) hDropNz)
        (hSelfKit B F0 peer hh hread)
        (cliPollSpkKitPlaced E2E.HooksE.A0 F0 spkId (cliKitStk B))
        (cliPollSpk_vtablesPlacedOk F0 spkId (cliKitStk B) hDropNz)
        (cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hread)
        (cliPollKpkKitPlaced E2E.HooksE.A0 F0 kpkId spkId kbk (cliKitStk B))
        (cliPollKpk_vtablesPlacedOk F0 kpkId spkId kbk (cliKitStk B) hDropNz)
        (cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hread
          (hKpkGetPoll B hh hread))
        (cliPollPkKitPlaced E2E.HooksE.A0 F0 opkWord (cliKitStk B))
        (cliPollPk_vtablesPlacedOk F0 opkWord (cliKitStk B) hDropNz)
        (cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hread)
        (dpClosSubStack B)
        (stageP2V1CallStack_le_subStack_placed (A := E2E.HooksE.A0) F0 peer
          spkId kpkId opkWord kbk B)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
