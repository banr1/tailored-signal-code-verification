/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G -- proof-setup: allow-public-import
public import Symbolic.Specifications.Refinement.ElfBinding
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3
import Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed
import Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ModelV2SlotsBase
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3PureGates
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot
import Symbolic.Proofs.Swarm.CREF.Cli.DirCodecBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.UA.Assembly
import Symbolic.Proofs.Swarm.UA.SlotInit
import Symbolic.Proofs.Swarm.UA.SlotRecvW
import Symbolic.Proofs.Swarm.UA.SlotRpkNO
import Symbolic.Proofs.Swarm.UA.SlotRpkProm
import Symbolic.Proofs.Swarm.UA.SlotSend
import Symbolic.Proofs.Swarm.UA.Top
import Symbolic.Proofs.Swarm.UA.XlateInv
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers

/-!
# Guarded Relocatable Two-Placement Progress Proof (`ProgressElfPlacedG`)

- **Role**: `Role::Proof` (outside the TCB).
- **Overview**:
  Route-2 (`w2_c12_route2_stmts.md` §3.2 `R2-P1`) entry-guarded twin of
  `ProgressElfPlaced.cliElfProgressPlaced_of_strict`, proving the unchanged guard-free
  `CliElfProgressPlaced mpl mmpl elf` from `CliElfF3B2NeedLocksAssumptionsG` and the six
  entry-guarded `MainOk*G` hypotheses together with the `R2-D2` strict / `≠ none` whole-process
  witnesses (without importing `ProgressElfPlaced` / `ElfSlicesPqOomPlacedInst`).
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedG

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.E2E (PEParams initiateTapeLen wirePrekey wireWhisper)
open CryptoVerification.SignalSession
  (CliHooks PqSessionMatches bundleDir encodeDir filesOf partyAddress pqRecvInputs pqSendInputs
   publicBundleOf)
open CryptoVerification.SignalSession.Cli (InputsLoadable)
open CryptoVerification.SignalSession.Cli.RunProofs (SessMatchesPm pkToE?)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF parsePreKeyWire)
open DY.Libsignal.Composed.Refinement.Cli
  (CliElfProgressPlaced CliReachable CliTurn ExternContractsHoldCli HooksMatchInterpretation
   InputsEquiv InputsFor ModelAgree PqFieldsMatch PqModelPost PqModelPostB2 PqModelRel
   PqModelRel.of_post StdinBounded ValidCall coinsLen elfRelPlaced initDirs parseBundleFiles
   peerOf pqInitInputsF preKeyOfBody?)
open DY.Libsignal.Composed.Refinement.Cli.ParD3
  (PqTurnSim1A bundleTyped_of_parseBundleFiles parsePreKeyWire_wirePrekey_cons
   pqFieldsMatch_iff_pqSessionMatches pqTurnSim1A_clearSession pqTurnSim1A_init
   preKeyOfBody?_some_inv regularFileList_of_bundleFilesFlat wireWhisper_eq_wireWhisperTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (d3PqSessionOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitRunSemOkF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G
   cliPqBinaryV2OomF3Placed_of_f3B2NeedLocksG cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3G
   cliRunPlacedSig_pqInitOverCap_ne_none_of_f3G cliRunPlacedSig_pqInitReject_ne_none_of_f3G
   d3_matchingPathB_strict_of_f3G d3_pksmParseNone_strict_of_f3G d3_untypedReject_strict_of_f3G
   d3_valid_match_strict_of_f3G d3_valid_over_strict_of_f3G mainOkCliF3OverG_of_mainOkOverD3F3G
   mainOkParseNoneD3F3G_of_untypedG)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3 (CliPqBinaryV2OomF3Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (CliElfF3B2NeedLocksAssumptionsG MainOkCliF3PqB2NeedLocksPlacedAtG
   cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG')
open LibsignalBinary.Proofs.SignalSession.Cli.Parity (BundleReadWithinCap parseBundleDir)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.ElfInputsExtF3
  (filesVisibleRaw_pqRecvInputs filesVisibleRaw_pqSendInputs)
open Symbolic.Proofs.Refinement.Composed.Cli (pksmParse_parsePreKey_cases)
open Symbolic.Proofs.Refinement.Composed.Cli.BundleInitElfF3Placed
  (parseBundleFiles_eq_parseBundleDir)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
  (pqModelPostB2_of_cliElf_exited_f3)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedHelpers
  (CallWithinCap aboveCap_after_eq_self_f3 caller_st_of_validCall_f3
   cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv cliRunPlacedSig_ne_none_of_inputsEquiv
   defaultExtrasProg inputsLoadable_of_init_inputsFor pqFieldsMatch_iff_sessMatchesPm_f3
   pqModelPost_of_b2_withinCap_f3 preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3)
open Symbolic.Swarm.CREF.Cli
  (bundleTyped_iff_exists_bundleE initDirs_interpOfParams inputsEquiv_pqInputs
   inputsEquiv_pqRecvInputs inputsEquiv_pqSendInputs interpOfParams keyToBytes32_bytesToKey32
   modelAgree_interpOfParams peerOf_eq_addrE_other records_of_pqPartyInv)

private theorem reachable_pqTurnSim1A_placedG {mpl mmpl : MultiPlacement} {elf : ElfImage}
    (hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf)
    {interp : ExternInterpretation} (hext : ExternContractsHoldCli interp)
    {W : CliHooks} (hAgree : HooksMatchInterpretation interp W)
    {r : ProtocolSetup} (hr : ProtocolSetupWF r) {t : CliTurn}
    (ht : CliReachable (elfRelPlaced mpl mmpl elf interp W) interp r
      (CliTurn.init (initDirs interp r)) t) :
    ∃ t_clean accepted,
      PqTurnSim1A (interpOfParams interp ⟨W.C, W.Q⟩) ⟨W.C, W.Q⟩ r t t_clean accepted := by
  let P : PEParams := ⟨W.C, W.Q⟩
  have hMA : ModelAgree interp P := hAgree
  induction ht with
  | init =>
    have hdirs_eq : initDirs interp r = initDirs (interpOfParams interp P) r :=
      congrFun (initDirs_interpOfParams interp P).symm r
    rw [hdirs_eq]
    exact ⟨_, [], pqTurnSim1A_init hr ((modelAgree_interpOfParams interp P).mpr hMA)⟩
  | clear p _ ih =>
    obtain ⟨t_clean, accepted, hsim⟩ := ih
    exact ⟨_, _, pqTurnSim1A_clearSession p hr hsim⟩
  | @step t c i code out files _ hval hin hRel ih =>
    obtain ⟨t_clean, accepted, hsim⟩ := ih
    have hpost : PqModelPostB2 interp P i (.exited code out files) :=
      pqModelPostB2_of_cliElf_exited_f3 hv2 interp hin.2.2.2.2 hRel
    by_cases hcap : CallWithinCap c
    · obtain ⟨_, st₀, hst₀, _⟩ := caller_st_of_validCall_f3 hr hsim hval
      have hpost1 : PqModelPost interp P i (.exited code out files) :=
        pqModelPost_of_b2_withinCap_f3 hval hin hst₀.dir_eq hcap hpost
      have hRel1 : PqModelRel interp P i (some (.exited code out files)) :=
        PqModelRel.of_post hpost1
      obtain ⟨t_clean', accepted', hsim', _⟩ :=
        Symbolic.Proofs.Swarm.UA.Assembly.uaSlot_dispatch
          Symbolic.Proofs.Swarm.UA.SlotInit.slot_init_ua
          Symbolic.Proofs.Swarm.UA.SlotSend.slot_send_ua
          (Symbolic.Proofs.Swarm.UA.SlotRecvW.slot_recvw_ua_of
            Symbolic.Proofs.Swarm.UA.XlateInv.xlate_inv
            Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
          Symbolic.Proofs.Swarm.UA.SlotRpkNO.slot_rpk_no_ua
          (Symbolic.Proofs.Swarm.UA.SlotRpkProm.slot_rpk_prom_ua_of_exc_w
            Symbolic.Proofs.Swarm.UA.Top.xlate_exc_w)
          interp P r hext hMA hr (evs_pre := []) hsim hval hin hRel1
      exact ⟨t_clean', accepted', hsim'⟩
    · have hafter : t.after r c code out files = t :=
        aboveCap_after_eq_self_f3 hr hsim hval hin hcap hpost
      exact ⟨t_clean, accepted, hafter.symm ▸ hsim⟩

/-- Guarded twin of `ProgressElfPlaced.cliElfProgressPlaced_of_strict` proving the unchanged
guard-free `CliElfProgressPlaced mpl mmpl elf` from `CliElfF3B2NeedLocksAssumptionsG` and the six
entry-guarded `main`-level binary witnesses (`R2-P1`). -/
theorem cliElfProgressPlaced_of_strictG
    {mpl mmpl : MultiPlacement}
    {exitStk : Nat} {libcAddr : BitVec 64} {stk : Nat} {CodeOk : Memory → Prop}
    {elf : ElfImage}
    (H : CliElfF3B2NeedLocksAssumptionsG mpl mmpl exitStk libcAddr stk CodeOk elf)
    (hmain : MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hoverD3 : MainOkOverD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (huntyped : MainOkUntypedD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hpathB : MainOkPathBD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hvalidMatch : MainOkValidMatchD3F3G mpl mmpl CodeOk libcAddr elf.brkStart stk)
    (hinitSem : MainInitRunSemOkF3G mpl mmpl CodeOk libcAddr elf.brkStart stk) :
    CliElfProgressPlaced mpl mmpl elf := by
  have hv2 : CliPqBinaryV2OomF3Placed mpl mmpl elf :=
    cliPqBinaryV2OomF3Placed_of_f3B2NeedLocksG H hmain hoverD3 huntyped hpathB hvalidMatch hinitSem
  have hbaseStrict :=
    cliPqxdhElfCorrectStrictPlaced2_of_f3B2NeedLocksG' H hmain
      (mainOkCliF3OverG_of_mainOkOverD3F3G hoverD3)
  intro interp hext W hAgree r hr t hreach c i hval hin
  let P : PEParams := ⟨W.C, W.Q⟩
  obtain ⟨t_clean, accepted, hsim⟩ := reachable_pqTurnSim1A_placedG hv2 hext hAgree hr hreach
  obtain ⟨_, st, hinv, hwf⟩ := caller_st_of_validCall_f3 hr hsim hval
  obtain ⟨hcoins, hsb, _, _, hguard⟩ := hval
  cases hm : c.cmd with
  | init peer dir =>
    rw [hm] at hcoins hguard
    obtain ⟨halice, rfl, rfl, hstdin, hrec_none, hflat, _⟩ := hguard
    have hsess_none : st.session = none := by
      have hrec_eq : t.records r r.alice = _ := halice ▸ records_of_pqPartyInv hinv
      rw [hrec_none] at hrec_eq
      cases hs : st.session with
      | none => rfl
      | some _ => rw [hs] at hrec_eq; cases hrec_eq
    let tape : List.Vector (BitVec 8) initiateTapeLen := ⟨c.coins, hcoins⟩
    have hpeer' : peerOf r r.alice = partyAddress st.party.other := by
      rw [← halice, peerOf_eq_addrE_other, ← hinv.party_eq]
    have hcmd_st : c.cmd = .init (partyAddress st.party.other) bundleDir := hpeer' ▸ hm
    have hi_enc : InputsFor c (filesOf (encodeDir P st)) i := by rwa [hinv.dir_eq] at hin
    have heq_f : InputsEquiv i (pqInitInputsF P st c.bundle tape) := by
      have heq0 := inputsEquiv_pqInputs hi_enc (regularFileList_of_bundleFilesFlat hflat) rfl
      unfold pqInitInputsF
      rwa [hcmd_st, hstdin] at heq0
    have hloadable : InputsLoadable i := inputsLoadable_of_init_inputsFor hm rfl hin
    cases hp : parseBundleFiles (filesOf c.bundle) with
    | none =>
      have hp_dir : parseBundleDir (filesOf c.bundle) bundleDir = none :=
        (parseBundleFiles_eq_parseBundleDir (filesOf c.bundle)).symm.trans hp
      exact cliRunPlacedSig_pqInitReject_ne_none_of_f3G
        H hinitSem W heq_f hloadable hwf hsess_none hflat hp_dir
    | some pb =>
      obtain ⟨b, rfl⟩ := (bundleTyped_iff_exists_bundleE pb).mp (bundleTyped_of_parseBundleFiles hp)
      have hp_dir : parseBundleDir (filesOf c.bundle) bundleDir = some (publicBundleOf b) :=
        (parseBundleFiles_eq_parseBundleDir (filesOf c.bundle)).symm.trans hp
      by_cases hcap : BundleReadWithinCap (filesOf c.bundle) bundleDir
      · exact cliRunPlacedSig_pqInitFiles_exact_ne_none_of_f3G
          H hinitSem W defaultExtrasProg heq_f hloadable hwf hsess_none hflat hcap hp_dir
      · exact cliRunPlacedSig_pqInitOverCap_ne_none_of_f3G
          H hinitSem W heq_f hloadable hwf hsess_none hflat hcap
  | send peer =>
    have hsb' : c.stdin.length < 2 ^ 32 := by simpa [StdinBounded, hm] using hsb
    rw [hm] at hcoins hguard
    obtain ⟨_, rfl, hbun, _, _⟩ := hguard
    let coins : List.Vector (BitVec 8) 64 := ⟨c.coins, hcoins⟩
    have hpeer' : peerOf r c.party = partyAddress st.party.other := by
      rw [peerOf_eq_addrE_other, ← hinv.party_eq]
    have hcmd_st : c.cmd = .send (partyAddress st.party.other) := hpeer' ▸ hm
    have hi_enc : InputsFor c (filesOf (encodeDir P st)) i := by rwa [hinv.dir_eq] at hin
    have heq : InputsEquiv i (pqSendInputs P st c.stdin coins) :=
      inputsEquiv_pqSendInputs (coins := coins) hi_enc hcmd_st hbun rfl
    have hne₀ : cliRunPlacedSig mpl mmpl elf W (pqSendInputs P st c.stdin coins) ≠ none := by
      rw [((hbaseStrict.2 W defaultExtrasProg).1 st hwf).2.1 c.stdin coins hsb']
      split_ifs <;> simp
    exact cliRunPlacedSig_ne_none_of_inputsEquiv hne₀ heq hin.2.2.2.2
      (filesVisibleRaw_pqSendInputs P st c.stdin coins)
  | recv peer =>
    have hcoins' : c.coins.length = 32 := by simpa [coinsLen, hm] using hcoins
    have hguard' := hguard
    rw [hm] at hguard'
    obtain ⟨_, rfl, hbun, _⟩ := hguard'
    let rc : BitVec 256 := CryptoGames.HKDF.bytesToKey32 c.coins
    have hcoins_rc : c.coins = CryptoGames.HMAC.keyToBytes32 rc :=
      (keyToBytes32_bytesToKey32 hcoins').symm
    have hpeer' : peerOf r c.party = partyAddress st.party.other := by
      rw [peerOf_eq_addrE_other, ← hinv.party_eq]
    have hcmd_st : c.cmd = .recv (partyAddress st.party.other) := hpeer' ▸ hm
    have hi_enc : InputsFor c (filesOf (encodeDir P st)) i := by rwa [hinv.dir_eq] at hin
    have heq_recv : InputsEquiv i (pqRecvInputs P st c.stdin rc) :=
      inputsEquiv_pqRecvInputs hi_enc hcmd_st hbun hcoins_rc
    unfold StdinBounded at hsb; rw [hm] at hsb
    by_cases hw : ∃ body, c.stdin = wireWhisperTag :: body
    · obtain ⟨body, hstdin⟩ := hw
      have hbody_lt : body.length < 2 ^ 32 := hsb.1 body hstdin
      have hstdin_w : c.stdin = wireWhisper :: body := by rwa [wireWhisper_eq_wireWhisperTag]
      have hne₀ :
          cliRunPlacedSig mpl mmpl elf W (pqRecvInputs P st (wireWhisper :: body) rc) ≠ none := by
        rw [((hbaseStrict.2 W defaultExtrasProg).1 st hwf).2.2.1 body rc hbody_lt]
        split_ifs <;> simp
      exact cliRunPlacedSig_ne_none_of_inputsEquiv hne₀ (hstdin_w ▸ heq_recv) hin.2.2.2.2
        (filesVisibleRaw_pqRecvInputs P st (wireWhisper :: body) rc)
    · have hnw_tag : c.stdin.head? ≠ some wireWhisperTag := by
        intro hh; cases hcs : c.stdin with
        | nil => simp [hcs] at hh
        | cons b tl =>
          simp only [hcs, List.head?_cons, Option.some.injEq] at hh
          exact hw ⟨tl, hh ▸ hcs⟩
      have hlen_lt : c.stdin.length < 2 ^ 32 := hsb.2.1 hnw_tag
      by_cases hpk : ∃ body, c.stdin = wirePrekey :: body
      · obtain ⟨body, hstdin⟩ := hpk
        have hbody_lt : body.length < 2 ^ 32 := by rw [hstdin, List.length_cons] at hlen_lt; omega
        have heq_body : InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) :=
          hstdin ▸ heq_recv
        rcases pksmParse_parsePreKey_cases body with ⟨hpnone, _⟩ | ⟨pm, q, hpm, hq, _⟩
        · exact cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv
            (d3_pksmParseNone_strict_of_f3G H (mainOkParseNoneD3F3G_of_untypedG huntyped) W st hwf
              body rc hbody_lt hpnone)
            heq_body hin.2.2.2.2 (filesVisibleRaw_pqRecvInputs P st (wirePrekey :: body) rc)
        · by_cases hsm_ex : ∃ x g, st.session = some (x, g) ∧ SessMatchesPm (d3PqSessionOf x g) pm
          · obtain ⟨x, g, hsess, hsm⟩ := hsm_ex
            exact cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv
              (d3_matchingPathB_strict_of_f3G H hpathB W st x g body pm rc hwf hsess
                (Nat.succ_le_of_lt hbody_lt) hpm hsm)
              heq_body hin.2.2.2.2 (filesVisibleRaw_pqRecvInputs P st (wirePrekey :: body) rc)
          · have hnsm : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm :=
              fun x g hs hsm => hsm_ex ⟨x, g, hs, hsm⟩
            cases hm_pk : pkToE? pm with
            | none =>
              exact cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv
                (d3_untypedReject_strict_of_f3G H huntyped W st hwf body pm rc hbody_lt hpm hm_pk
                  hnsm)
                heq_body hin.2.2.2.2 (filesVisibleRaw_pqRecvInputs P st (wirePrekey :: body) rc)
            | some m =>
              have hpre : preKeyOfBody? body = some m := by
                rw [preKeyOfBody?_eq_pksmParse_bind_pkToE?_f3, hpm]; exact hm_pk
              obtain ⟨q₁, hq₁, _, hminner, _, _, _, _, _, _, _⟩ := preKeyOfBody?_some_inv hpre
              cases Option.some.inj (hq.symm.trans hq₁)
              have hp_b : parsePreKeyWire (wirePrekey :: body) = some q := by
                rw [parsePreKeyWire_wirePrekey_cons]; exact hq
              have hmlt : m.inner.length + 2048 < 2 ^ 32 :=
                hminner ▸ hsb.2.2.1 q (hstdin ▸ hp_b)
              cases hsess : st.session with
              | none =>
                exact cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv
                  (d3_valid_match_strict_of_f3G H hvalidMatch W defaultExtrasProg st hwf body pm m
                    rc hbody_lt hpm hm_pk hmlt (fun _ _ hs => by rw [hsess] at hs; cases hs))
                  heq_body hin.2.2.2.2 (filesVisibleRaw_pqRecvInputs P st (wirePrekey :: body) rc)
              | some xg =>
                rcases xg with ⟨x, g⟩
                have hno_fm : ¬ PqFieldsMatch x g q :=
                  fun hfm => hnsm x g hsess ((pqFieldsMatch_iff_sessMatchesPm_f3 x g hq hpm).mp hfm)
                have hnomatch : ¬ PqSessionMatches x g m :=
                  fun hsm => hno_fm ((pqFieldsMatch_iff_pqSessionMatches x g hq hpre).mpr hsm)
                obtain ⟨_, hr₀, _⟩ :=
                  d3_valid_over_strict_of_f3G H hoverD3 W defaultExtrasProg st hwf x g hsess body
                    pm m rc hbody_lt hpm hm_pk hmlt hnomatch
                exact cliRunPlacedSig_ne_none_of_eq_some_inputsEquiv hr₀ heq_body hin.2.2.2.2
                  (filesVisibleRaw_pqRecvInputs P st (wirePrekey :: body) rc)
      · have hnw : c.stdin.head? ≠ some wireWhisper := by
          rwa [wireWhisper_eq_wireWhisperTag]
        have hnp : c.stdin.head? ≠ some wirePrekey := by
          intro hh; cases hcs : c.stdin with
          | nil => simp [hcs] at hh
          | cons b tl =>
            simp only [hcs, List.head?_cons, Option.some.injEq] at hh
            exact hpk ⟨tl, hh ▸ hcs⟩
        have hne₀ : cliRunPlacedSig mpl mmpl elf W (pqRecvInputs P st c.stdin rc) ≠ none := by
          rw [((hbaseStrict.2 W defaultExtrasProg).1 st hwf).2.2.2.2 c.stdin rc hlen_lt hnw hnp]
          split_ifs <;> simp
        exact cliRunPlacedSig_ne_none_of_inputsEquiv hne₀ heq_recv hin.2.2.2.2
          (filesVisibleRaw_pqRecvInputs P st c.stdin rc)

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlacedG
