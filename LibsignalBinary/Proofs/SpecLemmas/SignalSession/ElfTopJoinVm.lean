/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
public import LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVmHW4
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.Digits
import LibsignalBinary.Proofs.SignalSession.Cli.Main.WritePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Unbundled `MainOkValidMatchD3F3` Assembly on `cliElfBytes`

**Checked by Lean.**

Proves `hole_m24slot_validMatch_assembly_closed`, establishing `MainOkValidMatchD3F3`
on `cliElfBytes` over `cliDecPkCanonSlotEnvExact'` via `etjv_validMatch_of_w4` and
`ElfTopJoinVmHW4.etjv_hW4_closed`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVm

open Arm64 (GhostName HookSat Memory subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (IdentityKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi
  (PreKeySignalMessage SessionRecord StoreCall fullTrace messageDecryptSignal_trace_prefix)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E
  (PEParams UnreachedPqxdhPrimitives partyAddressName pqxdhSpqrModel recvPrekeyState wirePrekey
   wireWhisper)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs baseKeysFile cliElfBytes cliElfImage cliExternsPlaced identityFile
   libsignalSessionLib lsReadFileSym oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress
   sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost KyberGhost StoresGhost addressText baseKeysName keyName pathOf removePreKey utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV DirWrOk RunCall StoreCallPeerPlaced StoresWrOk addrParse cliIo
   cliMainStk cliResStack cliRunBudgets cliRunNeeds cliWrOk inputOf
   instLsCodeInvFrozen keyName_length mProgPlaced mainFrameSize messageDecryptSignal_calls_peer_placed
   namedWrites namedWrites_ascii okPeerPath parseArgs saveUpd_own saveUpd_peers_path)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunSem SlotAns finish readBundleV runAns runFiles runProgPlaced runRel)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm cliAnswers cliDecryptPrekeyNeed cliFinal cliStep decPkDef decPkDefD2c
   decPkDefD2c_eq_decPkDef_of_match decPkDefD2c_eq_decPkDef_of_noCurrent
   decPkDefD2c_eq_decPkDef_of_untrusted decPkDefD2c_namedWrites_sub decSigDef decSigKey encDef
   initDef initParty pkRecvCoins pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrValE runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (w1EncExactCum w1EncExactGrpS w1EncExactLive w1EncExactMaxReq w1EncExactPeak
   w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
  (ckx2_w2DecSigExact_groupSpec ckx2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
  (d3SlotMainFitsOneGiBOf mainEntryBudgetFitsCapOf_pqD3Recv_dom0)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal (pqRunAns_namedWrites_bounds)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (recv_rest_length_le_msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (cliDecPkCanonSlotEnvExact' cliDecPkCanonSlotEnvExact'_ghost_congr)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
  (cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom
   cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom
   fits2_zbDom0'Cum fits2_zbDom0'GrpS109 fits2_zbDom0'Live fits2_zbDom0'MaxReq fits2_zbDom0'Peak)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (Block617TransferFixedHyp cliRunSemD3ValidMatch
   mainOkValidMatchD3F3_of_runSem mainSubroutineD3F3_of_domScopedRunTight)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3 (MainOkValidMatchD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
  (MainIoOfPlaced ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliRunHooksBundle cliPubCallees_d2c_frozen_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunEnv run_ok_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (decSigSlotSpecBasePlaced decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf
   encSlotSpecPlaced slotsOfPlaced slotsOfSigFrozenPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
  (subsetA4PksmTryFromPlaced_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (cliPksmTryFrom_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
  (hc_kemDeserialize_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
  (CliSpqrRecvTightLinkedEnv SpqrSendCoinsTightLinkedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr hole3_initEnv_r1c_congr
   hole3_pksmTryFromEnv_congr hole3_w1_inner hole3_w2_inner hole3_w3_init
   libsignalFullPlacementOf)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)

private theorem etjv_agree_encDef_eq_runProofs (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef P Scope = encDef P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls = cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F = cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
        (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer) =
        cliAnswers Scope F peer
          (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer) := by
    intro F peer
    have hKey :
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer =
          CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer := by
      unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey
        CryptoVerification.SignalSession.Cli.RunProofs.encKey
      rcases loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer with _ | _ <;> rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef encDef
  rw [hAns F peer]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (cliAnswers Scope F peer (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer))
    ptext peer me CryptoVerification.SignalSession.Cli.RunCompose.unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

private theorem etjv_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def etjv_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem etjv_utf8_eq (s : String) : utf8 s = etjv_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, etjv_kutf8, List.utf8Encode, etjv_byteArray_toList_eq_data]

private theorem etjv_utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [etjv_utf8_eq, etjv_utf8_eq, etjv_utf8_eq]
  simp [etjv_kutf8, String.toList_append, List.flatMap_append]

private theorem etjv_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private theorem etjv_sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  simp only [sessionFile, partyAddress, CryptoVerification.SignalSession.Address.text,
    etjv_toString_one, String.append_assoc]

private theorem etjv_okPeerPath_id (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  have hpath : pathOf (utf8 "identities") (addrValE P).name =
      utf8 (identityFile (partyAddressName P)) := by
    have hne : utf8 "identities" ≠ [] := by rw [etjv_utf8_eq]; decide
    simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
    rw [← etjv_utf8_append, ← etjv_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inl ?_⟩
  · rw [etjv_utf8_eq]
    intro b hb
    have hall :
        (etjv_kutf8 (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [etjv_utf8_eq]
    cases P <;> decide

private theorem etjv_okPeerPath_sess (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  have hpath : pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
    have hne : utf8 "sessions" ≠ [] := by rw [etjv_utf8_eq]; decide
    have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
      have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
      simp only [addressText, addrValE, CryptoVerification.SignalSession.Cli.decimalText, h1,
        CryptoVerification.SignalSession.Address.text, partyAddress]
      rw [← etjv_utf8_append, ← etjv_utf8_append]
    rw [had]
    simp only [pathOf, hne, ↓reduceIte, sessionFile]
    rw [← etjv_utf8_append, ← etjv_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inr ?_⟩
  · rw [etjv_utf8_eq, etjv_sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (etjv_kutf8 ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [etjv_utf8_eq, etjv_sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem etjv_list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar; dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := etjv_list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem etjv_string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, etjv_byteArray_toList_eq_data]
  rw [hutf]
  exact etjv_list_length_le_flatMap_utf8EncodeChar l

private theorem etjv_u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (etjv_string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem etjv_identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem etjv_sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  rw [etjv_sessionFile_partyAddress_eq]
  cases P <;> decide

private theorem etjv_oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := etjv_u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile; rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem etjv_baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := etjv_u32_toString_len_le_10 id
  unfold baseKeysFile; simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem etjv_oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := etjv_u32_toString_len_le_10 id
  unfold oneTimePreKeyFile; rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem etjv_setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons _ _ ih =>
    unfold DirGhost.setOrPush
    split <;> [simp; (simp only [List.length_cons]; omega)]

private theorem etjv_dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact etjv_setOrPush_length_le_succ d.changed k v

private theorem etjv_saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact etjv_dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem etjv_foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    have h1 : (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
      cases c with
      | loadSession _ | isTrustedIdentity _ _ _ => exact Nat.le_succ _
      | saveIdentity rem k =>
        obtain ⟨hp, ho⟩ := etjv_saveUpd_peers_writes_length_le_succ F g.identity rem k
        dsimp only [cliStep, StoresGhost.writes]; rw [ho]; simp only [List.length_append]; omega
      | storeSession rem r =>
        dsimp only [cliStep, StoresGhost.writes]
        have hs := etjv_dirPut_writes_length_le_succ g.sessions (addressText rem)
          (CryptoVerification.E2E.Record.encodeRecord r)
        simp only [List.length_append]; omega
    have h2 := etjv_foldl_cliStep_writes_length_le F cs (cliStep F g c)
    dsimp only [List.foldl, List.length_cons]; omega

private theorem etjv_storesWrOk_foldl (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ etjv_okPeerPath_id P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ etjv_okPeerPath_sess P) _ } hp hs

private theorem etjv_decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h; dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (CryptoVerification.E2E.pqxdhSpqrSession W)
                  ((CryptoVerification.E2E.pqxdhSessionParams W).expectedAddrs
                    (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1; injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := etjv_saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := etjv_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (CryptoVerification.E2E.Record.encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]; rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err => cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h; dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h; dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h; dsimp only at h
                  cases hrecv : recvPrekeyState X W
                      (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u; dsimp only at h
                          injection h with h1; injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          have hkyb : kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
                            unfold KyberGhost.mark at hkm
                            cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F
                                (keyName m.kpkId) with
                            | error _ => rw [hot] at hkm; cases hkm
                            | ok bs =>
                              rw [hot] at hkm
                              cases bs with
                              | cons _ _ =>
                                dsimp only at hkm; injection hkm with _ hk; subst hk; dsimp only
                                have h1 := etjv_dirPut_writes_length_le_succ
                                  StoresGhost.opened.kyber.oneTime (keyName m.kpkId) []
                                have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                omega
                              | nil =>
                                dsimp only at hkm
                                cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F
                                    (baseKeysName m.kpkId) with
                                | error _ => rw [hlr] at hkm; cases hkm
                                | ok seen =>
                                  rw [hlr] at hkm; dsimp only at hkm
                                  split at hkm
                                  · cases hkm
                                  · split at hkm
                                    · cases hkm
                                    · injection hkm with _ hk; subst hk; dsimp only
                                      have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                      have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                      rw [h0a, Nat.zero_add]
                                      exact Nat.le_trans (etjv_dirPut_writes_length_le_succ _ _ _)
                                        (by rw [h0b])
                          obtain ⟨hp_le, ho⟩ := etjv_saveUpd_peers_writes_length_le_succ F
                            StoresGhost.opened.identity (addrValE P) pm.identityKey
                          have hs_le := etjv_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                            (addressText (addrValE P))
                            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
                          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                          unfold StoresGhost.writes; dsimp only; rw [ho]
                          simp only [List.length_append, h0_own, h0_signed, h0_pub]
                          cases pm.preKeyId with
                          | none =>
                            dsimp only
                            have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                            omega
                          | some j =>
                            dsimp only; unfold removePreKey
                            cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                            | error _ =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | ok bs =>
                              cases bs with
                              | nil =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | cons _ _ =>
                                dsimp only
                                have hot_put := etjv_dirPut_writes_length_le_succ
                                  StoresGhost.opened.oneTime (keyName j) []
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega

private theorem etjv_decPkDef_some_some_eq_d2c {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F peer me pm coins = some (some (g', pt))) :
    decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)) := by
  by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true
  · cases hload : loadRec Scope F peer with
    | error _ =>
      unfold decPkDef at h; simp [hload] at h
    | ok opt =>
      cases opt with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
          (fun _ hl => by rw [hload] at hl; cases hl)]
        exact h
      | some r =>
        cases hcur : r.currentSession with
        | none =>
          rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
            (fun _ hl => by
              rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)]
          exact h
        | some s =>
          by_cases hm : SessMatchesPm s pm
          · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F peer me pm coins hload hcur hm]
            exact h
          · unfold decPkDef at h
            simp [hload, htr, hcur, hm] at h
  · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F peer me pm coins htr]
    exact h

private theorem etjv_finish_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1; injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

private theorem etjv_runAns_some_some_to_d2c
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    {i : Inputs} {nw : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (ha : runAns S i = some (some (nw, out))) :
    runAns (cliRunSemD2c_placed X W) i = some (some (nw, out)) := by
  unfold runAns at ha ⊢
  cases hp : parseArgs uuidTryParse (i.argv.map bytesOfString) with
  | none => rw [hp] at ha; cases ha
  | some c =>
    rw [hp] at ha; dsimp only at ha ⊢
    cases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    | error _ => rw [hown] at ha; cases ha
    | ok ownB =>
      rw [hown] at ha; dsimp only at ha ⊢
      cases had : addrParse uuidTryParse ownB with
      | none => rw [had] at ha; cases ha
      | some meV =>
        rw [had] at ha; dsimp only at ha ⊢
        cases c with
        | keygen _ _ => cases ha
        | init peerV dir =>
          dsimp only at ha ⊢
          cases hbv : readBundleV (runFiles i) dir peerV.device with
          | none => rw [hbv] at ha; cases ha
          | some b =>
            rw [hbv] at ha; dsimp only at ha ⊢
            have hd2c_in : (cliRunSemD2c_placed X W).initiate = initDef X ⟨W.C, W.Q⟩ := rfl
            rw [hinit] at ha; rw [hd2c_in]; exact ha
        | send peerV =>
          dsimp only at ha ⊢
          have hd2c_enc : (cliRunSemD2c_placed X W).encrypt = encDef ⟨W.C, W.Q⟩ scopeIn :=
            etjv_agree_encDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn
          rw [henc] at ha; rw [hd2c_enc]; exact ha
        | recv peerV =>
          dsimp only at ha ⊢
          cases hst : i.stdin with
          | nil => rw [hst] at ha; cases ha
          | cons t rest =>
            rw [hst] at ha; dsimp only at ha ⊢
            by_cases ht2 : t = 2#8
            · simp only [ht2, ↓reduceIte] at ha ⊢
              have hd2c_sig : (cliRunSemD2c_placed X W).decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn :=
                decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn
              rw [hdecSig] at ha; rw [hd2c_sig]; exact ha
            · simp only [ht2, ↓reduceIte] at ha ⊢
              by_cases ht3 : t = 3#8
              · simp only [ht3, ↓reduceIte] at ha ⊢
                have hd2c_pk : (cliRunSemD2c_placed X W).pksmParse = pksmParse := rfl
                have hd2c_dp : (cliRunSemD2c_placed X W).decryptPrekey =
                    decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn := rfl
                rw [hpksm] at ha; rw [hd2c_pk, hd2c_dp]
                cases hpm : pksmParse rest with
                | none => rw [hpm] at ha; cases ha
                | some pm =>
                  rw [hpm] at ha; dsimp only at ha ⊢
                  rw [hdecPk] at ha
                  obtain ⟨g', v, hg, hnw, hout⟩ := etjv_finish_inv ha
                  rw [etjv_decPkDef_some_some_eq_d2c hg]
                  simp [finish, hnw, hout]
              · simp only [ht3, ↓reduceIte] at ha; cases ha

private theorem etjv_decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨k, r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := etjv_foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]; omega
  · cases h
  · cases h

private theorem etjv_storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (CryptoVerification.LibsignalTripleRatchetRepr.coinsOf coins)
    rw [heq] at hc
    exact etjv_storesWrOk_foldl F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem etjv_nwDom_pqD3Recv
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    (i : Inputs)
    (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns S i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  have ha_d2c := etjv_runAns_some_some_to_d2c hinit henc hdecSig hdecPk hpksm ha
  rcases hi with hi_pq | ⟨st, ct, rc, _hwf, rfl⟩
  · exact pqRunAns_namedWrites_bounds hi_pq ha_d2c
  · cases ct with
    | nil =>
      rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st [] rc (by decide) (by decide)] at ha; cases ha
    | cons t rest =>
      by_cases ht2 : t = wireWhisper
      · subst ht2
        rw [runAns_pqRecvWhisper_eq S ⟨W.C, W.Q⟩ st rest rc, hdecSig] at ha
        cases hsm : SignalMessage.tryFrom protoSignalCodec rest with
        | error _ => rw [hsm] at ha; cases ha
        | ok msg =>
          rw [hsm] at ha; dsimp only at ha
          obtain ⟨g', v, hg, rfl, _⟩ := etjv_finish_inv ha
          have hlen4 : g'.writes.length ≤ 4 := etjv_decSigDef_writes_bounds hg
          have hwr : StoresWrOk (okPeerPath st.party.other) g' := etjv_storesWrOk_decSigDef hg
          refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
          have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
            fun w hw => (hwr.writes w hw).1
          rw [namedWrites_ascii g'.writes hasc] at hq
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          rcases (hwr.writes w hw).2 with hp | hp <;> rw [hp]
          · exact etjv_identityFile_len_le_64 st.party.other
          · exact etjv_sessionFile_len_le_64 st.party.other
      · by_cases ht3 : t = wirePrekey
        · subst ht3
          rw [runAns_pqRecvPrekey_eq S ⟨W.C, W.Q⟩ st rest rc, hpksm, hdecPk] at ha
          cases hpm : pksmParse rest with
          | none => rw [hpm] at ha; cases ha
          | some pm =>
            rw [hpm] at ha; dsimp only at ha
            obtain ⟨g', v, hg, rfl, _⟩ := etjv_finish_inv ha
            have hg_d2c := etjv_decPkDef_some_some_eq_d2c hg
            obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub hg_d2c
            have hlen4 := etjv_decPkDef_writes_len_le_4 hg
            refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
            rcases hsub q hq with h | h | h | h | h <;> rw [h]
            · exact etjv_identityFile_len_le_64 st.party.other
            · exact etjv_sessionFile_len_le_64 st.party.other
            · exact etjv_oneTimeKyberPreKeyFile_len_le_64 kpkId
            · exact etjv_baseKeysFile_len_le_64 kpkId
            · exact etjv_oneTimePreKeyFile_len_le_64 opkId
        · rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st (t :: rest) rc
            (fun h => ht2 (Option.some.inj h)) (fun h => ht3 (Option.some.inj h))] at ha
          cases ha

private theorem etjv_fitsCap_validMatch [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          PksmTryFromEnv (cliRunSemD3ValidMatch X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W))) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0
    (fun {M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    img (cliRunSemD3ValidMatch X W) X W A cliRunBudgets
    (cliDecPkCanonSlotEnvExact' X W)
    fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109
    (etjv_nwDom_pqD3Recv rfl rfl rfl rfl rfl)
    (fun g peerV M' A' w1R hi hp hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_phaseCredit W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun g peerV M' A' w1R hi hp hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_groupSpec W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun g peerV M' A' w2R hi hp hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w2DecSigExact_phaseCredit W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun g peerV M' A' w2R hi hp hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w2DecSigExact_groupSpec W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun g meV peerV rest pm hi hp hin hc hst hpk =>
      cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom X W hi hp rfl rfl
        (Nat.le_trans (pksmParse_lengths_le hpk).2.2.1 (recv_rest_length_le_msgCapBytes hin hc hst)))
    (by decide)
    (fun g meV peerV rest pm hi hp hin hc hst hpk =>
      cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom X W hi hp rfl rfl
        (Nat.le_trans (pksmParse_lengths_le hpk).2.2.1 (recv_rest_length_le_msgCapBytes hin hc hst)))
    (by unfold d3SlotMainFitsOneGiBOf; decide)
    rfl

private theorem etjv_hrun_validMatch_of_w4
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (ghFixed : CliGhostHooks)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostSpqrAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hW4 :
      letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
      let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
      let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
      let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs (cliRunSemD3ValidMatch X W) needs).decryptPrekey.OkPlaced
        (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    @subroutine_ok _
      (@mProgPlaced (libsignalPlacementOf mpl hblk hext_nodup)
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (mpl.base 579)
      (@runSpecTightPlaced
        (libsignalPlacementOf mpl hblk hext_nodup)
        (libsignalPlacementOf mpl hblk hext_nodup) _
        (LibsignalFrozen mpl)
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliBudgetLimits
        (letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
         RunEnv
           (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
             (binaryKitRunSlotEnvsExact W
               (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
               cliRunBudgets (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
             PksmTryFromEnv (cliRunSemD3ValidMatch X W)))
        uuidTryParse (runRel (cliRunSemD3ValidMatch X W)) cliWrOk cliResStack) := by
  letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  let S := cliRunSemD3ValidMatch X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hHooks := hHooksBundle W γ tp
  have hh := hHooks.runHooks
  have hpub :=
    cliPubCallees_d2c_frozen_ok (sEnvs := sEnvs) (PksmTryFromEnv := PksmTryFromEnv)
      mmpl ghFixed W hHooks
      (hole3_initEnv_r1c_congr W)
      (hole3_encEnv_r2_congr W A)
      (hole3_decSigEnv_r3a_congr W A)
      hole3_pksmTryFromEnv_congr
      (cliDecPkCanonSlotEnvExact'_ghost_congr X W)
  have hW1Inner :=
    hole3_w1_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
      (hGSpqr γ tp) hFs (hReadSat W γ tp) hHooks h547
  have hW2Inner :=
    hole3_w2_inner hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
      (hGSpqr γ tp) hFs (hReadSat W γ tp) hHooks h547
  have hInit :=
    hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
      (hGSpqr γ tp) hFs (hReadSat W γ tp) hghNoAlloc hHooks h547
  have hEncSpecEq :
      encSlotSpecPlaced A cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W) =
      encSlotSpecPlaced A cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        S := by
    funext stk
    unfold encSlotSpecPlaced
    have hfiles : (cliRunSemD2c_placed X W).filesOk = S.filesOk := rfl
    have hencOk : (cliRunSemD2c_placed X W).encOk = S.encOk := rfl
    have henc : (cliRunSemD2c_placed X W).encrypt = S.encrypt :=
      (etjv_agree_encDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
    rw [hfiles, hencOk, henc]
  have hDecSigSpecEq :
      decSigSlotSpecFrozenPlaced A cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W) =
      decSigSlotSpecFrozenPlaced A cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        S := by
    funext stk
    unfold decSigSlotSpecFrozenPlaced decSigSlotSpecPlacedOf decSigSlotSpecBasePlaced
    have hfiles : (cliRunSemD2c_placed X W).filesOk = S.filesOk := rfl
    have hdec : (cliRunSemD2c_placed X W).decryptSignal = S.decryptSignal :=
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
    rw [hfiles, hdec]
  have hcallees : RunCalleesPlaced A cliBudgetLimits
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      H cliRunBudgets (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs S needs) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := by
        dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced, slotsOfPlaced,
          sEnvs, binaryKitRunSlotEnvsExact]
        rw [← hEncSpecEq]
        exact hW1Inner
      decryptSignal := by
        dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced,
          sEnvs, binaryKitRunSlotEnvsExact]
        rw [← hDecSigSpecEq]
        exact hW2Inner
      initiate := hInit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hW4
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S (cliDecryptPrekeyNeed cliRunBudgets))
      hh
      hcallees
      (cliPksmTryFrom_placed_at_block
        (callerProg := runProgPlaced H) (i := 579)
        (subsetA4PksmTryFromPlaced_cli mmpl ghFixed W (hGSpqr γ tp).toCliGhostAllocHooks) (fun _ => rfl))
      (runNeed_cli_le_resStack_placed A cliBudgetLimits sEnvs
        (S := S) (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets) (by decide))
      (by decide)
      (by decide)

/-- Reduces `MainOkValidMatchD3F3` over `cliDecPkCanonSlotEnvExact'` to the block-520 `decryptPrekey.OkPlaced` obligation `hW4`. -/
theorem etjv_validMatch_of_w4
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (ghFixed : CliGhostHooks)
    (hookStack : Nat)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hTrFrozen : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostSpqrAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (hW4 : mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
        let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
        let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
          (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
        let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs (cliRunSemD3ValidMatch X W) needs).decryptPrekey.OkPlaced
          (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)) :
    MainOkValidMatchD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  refine mainOkValidMatchD3F3_of_runSem fun h547 X W => ?_
  exact
    mainSubroutineD3F3_of_domScopedRunTight
      hblk hext_nodup ghFixed
      (@instLsCodeInvFrozen (libsignalPlacementOf mpl hblk hext_nodup))
      (RunEnvOf := fun γ tp =>
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (binaryKitRunSlotEnvsExact W
              (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
              cliRunBudgets (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
            PksmTryFromEnv (cliRunSemD3ValidMatch X W)))
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩)
      (cliRunSemD3ValidMatch X W)
      rfl hTrFrozen
      (by
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        exact fun γ tp => (hGSpqr γ tp).toCliGhostAllocHooks)
      (hioOf W) hMainStk
      (fun γ tp => by
        letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
        exact etjv_fitsCap_validMatch (default : Image) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
      (fun γ tp =>
        etjv_hrun_validMatch_of_w4 hLs ghFixed hblk hext_nodup hPl_mng hGSpqr hFs
          hReadSat hghNoAlloc hHooksBundle h547 X W γ tp (hW4 h547 X W γ tp))

/-- Establishes `MainOkValidMatchD3F3` on `cliElfBytes` from unbundled ghost-witness field hypotheses. -/
theorem hole_m24slot_validMatch_assembly_closed
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (ghFixed : CliGhostHooks)
    (hookStack : Nat)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk)
    (hTrFrozen : Block617TransferFixedHyp mpl mmpl ghFixed
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      ∀ (γ : GhostName) (tp : BitVec 64),
        CliGhostSpqrAllocHooks fineCostModel
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hReadSat : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (readFileSpecPlaced cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hioOf : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @MainIoOfPlaced (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd))
    (hHooksBundle : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd))
    (_hF3Frozen : ∀ m : Memory, F3CodeOk mpl mmpl m → LibsignalFrozen mpl m)
    (_hSpqr : ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @SpqrV1PlacedSeamsOfEnv (libsignalPlacementOf mpl hblk hext_nodup)
        fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        mmpl ghFixed W
        (InitialStateEnv W.C.F)
        (CliSpqrRecvTightLinkedEnv W)
        (SpqrSendCoinsTightLinkedEnv W.C.F W.Q.K)) :
    MainOkValidMatchD3F3 mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk :=
  etjv_validMatch_of_w4 hLs ghFixed hookStack hblk hext_nodup hPl_mng hMainStk hTrFrozen
    hGSpqr hFs hReadSat hghNoAlloc hioOf hHooksBundle
    (LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVmHW4.etjv_hW4_closed
      hLs ghFixed hblk hext_nodup hPl_mng hGSpqr hReadSat hHooksBundle)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinVm
