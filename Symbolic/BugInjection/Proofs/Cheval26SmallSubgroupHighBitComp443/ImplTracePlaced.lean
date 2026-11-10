/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShapePlaced
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace

/-!
# Placed 3-Call Small-Subgroup CLI Implementation Trace Builder

Adapts `ImplTrace` from `cliRunAbortOnPanic` to `Placed.cliRunPlacedSig mpl mmpl`: reduces
`(cliCompShapePlaced mpl mmpl).ImplHalf` for `Cheval26SmallSubgroupHighBitCli` to three placed CLI
executions (`hbInp0`, `hbInp1`, `hbInp2`) validated by `ValidCall0Files`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTracePlaced

open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
  (parsePreKeyWire sentBody PqFromHonest)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot ValidCall InputsFor FilesBounded StdinBounded BobCallAllowed
   PreKeyNoMatch CliTraces HonestBundleDir scrub bundleBlob aliceUuid bobUuid initDirs runInput
   runEventOf)
open CryptoVerification.SignalSession (filesOf)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded cliCompShapePlaced)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (compHooks0 cliCompFitsPinned compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompRX0SS38 (bunBytes bunBytes_eq)
open Symbolic.BugInjection.Proofs.Common443.CompSmallSubgroupTrace
  (bundleFast sentWireBytes highBitWireBytes highBitWireBytes_eq highBit_pqFromHonest)
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (cliCoins0_length)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_cryptoEquationsHold)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend evRecv cliEvents)
open Symbolic.Proofs.Tests.Refinement.Cli
  (CliFilePath filesBounded_of_cliFilePaths bundleFiles_cliFilePath inputsFor_of_cliFilePaths
   honestBundleDir_honestPublicBundle parseBundleFiles_of_honestBundleDir
   honestBundleDir_to_flat_and_honest commonFiles_alice_cliFilePath commonFiles_bob_cliFilePath
   bobPreKeyFiles_cliFilePath commonFiles_alice_bounded commonFiles_bob_bounded
   bobPreKeyFiles_bounded initDirs_alice_no_session)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTrace
  (cliCompFits_of_pinned compRecordsI0_wf_of_plausible cliCompFitsPinned_compI0_of_plausible
   invertsGuarded_of_noInverts checkCanonicalPreKey canonicalPreKey_of_check
   checkRecvStdinBounded stdinBounded_recv_of_check canonicalPreKey_head_ne_whisper
   scrubList scrub_filesOf_eq_filesOf_scrubList ValidCall0Files ValidCall1Files
   validCall0Files_cliFilePath validCall0Files_scrub_cliFilePath validCall0Files_scrub_bounded
   validCall0Files_alice_records_ne_none ssBundle honestPublicBundle_eq_ssBundle
   ssAliceBaseFiles commonFiles_alice_eq_ssAliceBaseFiles ssBobBaseFiles bobFiles_eq_ssBobBaseFiles
   ssC0Coins cliCoins0_eq_ssC0Coins ssC1Pt ptB_eq_ssC1Pt ssC1Coins cB_eq_ssC1Coins
   ssC1Out sentWirePlant_eq_ssC1Out sentWireSS_eq_ssC1Out ssC2Coins rngMsg39_eq_ssC2Coins
   ssC2Out acceptMsg40_eq_ssC2Out ssCall0 ssCall1 ssCall2 mkInp ssInp0 ssInp1 ssInp2
   ssOut0 ssOut1 ssOut2 mkTurn hbC2Msg hbInp0 hbInp1 hbInp2 hbOut0 hbOut1 hbOut2 hbBundle_blob_eq)

private theorem nat_repr_one : Nat.repr 1 = "1" := by
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl

private theorem ssInp0_eq_mkInp (w : PQXDHSpqrSetup) :
    ssInp0 w = mkInp (ssCall0 w) (ssAliceBaseFiles w) := by
  simp [ssInp0, mkInp, ssCall0, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, bobUuid, nat_repr_one]

private theorem ssInp1_eq_mkInp (files0 : List (String × HwBytes)) :
    ssInp1 files0 = mkInp ssCall1 (scrubList files0) := by
  simp [ssInp1, mkInp, ssCall1, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, bobUuid, nat_repr_one]

private theorem ssInp2_eq_mkInp (w : PQXDHSpqrSetup) (c2Msg c2Coins : HwBytes) :
    ssInp2 w c2Msg c2Coins = mkInp (ssCall2 c2Msg c2Coins) (ssBobBaseFiles w) := by
  simp [ssInp2, mkInp, ssCall2, CryptoVerification.SignalSession.Cmd.argv,
    CryptoVerification.SignalSession.Address.text, aliceUuid, nat_repr_one]

private theorem cliTurn_mk_eq {d1 d2 : Participant → DirectorySnapshot}
    {s1 s2 : List HwBytes} {b1 b2 : Bool}
    (hd : d1 = d2) (hs : s1 = s2) (hb : b1 = b2) :
    CliTurn.mk d1 s1 b1 = CliTurn.mk d2 s2 b2 := by
  subst hd hs hb; rfl

private theorem initTurn_eq_mkTurn (w : PQXDHSpqrSetup)
    (hSpk : w.spkId = 7) (hKpk : w.kpkId = 9) :
    CliTurn.init (initDirs compI0 (compRecordsI0 w)) =
      mkTurn (filesOf (ssAliceBaseFiles w)) (filesOf (ssBobBaseFiles w)) [] false := by
  unfold CliTurn.init mkTurn
  refine cliTurn_mk_eq (funext fun p => ?_) rfl rfl
  simp only [initDirs,
    show (compRecordsI0 w).alice = "alice" from rfl,
    show (compRecordsI0 w).bob = "bob" from rfl]
  by_cases hpa : p = "alice"
  · subst hpa
    simp [commonFiles_alice_eq_ssAliceBaseFiles w]
  · by_cases hpb : p = "bob"
    · subst hpb
      simp [hpa, bobFiles_eq_ssBobBaseFiles w hSpk hKpk]
    · simp [hpa, hpb]

open Classical in
private theorem after_alice_mkTurn {w : PQXDHSpqrSetup} {aDir bDir outDir : DirectorySnapshot}
    {sent : List HwBytes} {c : CliCall} {out : HwBytes} (hp : c.party = "alice") :
    (mkTurn aDir bDir sent false).after (compRecordsI0 w) c 0 out outDir =
      mkTurn (scrub outDir) bDir
        (sent ++ (match c.cmd with | .send _ => (sentBody out).toList | _ => [])) false := by
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch (compRecordsI0 w) (mkTurn aDir bDir sent false) c) := by
    rintro ⟨_, hbob, _⟩
    have hab : ("alice" : String) = "bob" := hp.symm.trans hbob
    exact absurd hab (by decide)
  have hbob : ((mkTurn aDir bDir sent false).bobOff ||
      decide (0 = 0 ∧ PreKeyNoMatch (compRecordsI0 w) (mkTurn aDir bDir sent false) c)) = false := by
    rw [show (mkTurn aDir bDir sent false).bobOff = false from rfl, Bool.false_or]
    exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]; simp only [hp]; unfold mkTurn
  refine cliTurn_mk_eq (funext fun q => ?_) (by cases c.cmd <;> rfl) rfl
  by_cases hqa : q = "alice" <;> simp [hqa]

/-- Builds `(cliCompShapePlaced mpl mmpl).ImplHalf` at `cliCompFitsPinned w` from three
`cliRunPlacedSig` executions (`init`, `send`, `recv`) with arbitrary Call 1 and Call 2 output
snapshots. -/
theorem ss_impl_half_pinned_of_three_calls_dirs_placed
    {w : PQXDHSpqrSetup} {evs : List CliEvent}
    (hPlaus : w.Plausible)
    (hTor : TorsionShiftsRecorded compI0 w.torsionShifts)
    (hSpkId : w.spkId = 7) (hKpkId : w.kpkId = 9)
    (hBun : bundleBlob (ssBundle w) = bundleFast)
    {c2Msg : HwBytes}
    (hCanon : checkCanonicalPreKey c2Msg = true)
    (hStdin2 : checkRecvStdinBounded c2Msg = true)
    (hPq2 : ∀ q, parsePreKeyWire c2Msg = some q →
      PqFromHonest (sentBody sentWireBytes).toList q.message)
    (hEvs : cliEvents c2Msg = evs)
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 : List (String × HwBytes)) (outDir1 outDir2 : DirectorySnapshot)
    (hValid0 : ValidCall0Files files0 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp0 w) = some (ssOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp1 files0) =
      some (.exited 0 ssC1Out outDir1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp2 w c2Msg ssC2Coins) =
      some (.exited 0 ssC2Out outDir2)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf (cliCompFitsPinned w) H evs := by
  have hFits := cliCompFitsPinned_compI0_of_plausible w hPlaus hTor
  have hwf := compRecordsI0_wf_of_plausible w hPlaus
  refine ⟨(compI0, compHooks0), compRecordsI0 w, hFits, ⟨hFits.2.1, hFits.2.2⟩, ?_, ?_⟩
  ·
    rw [← hEvs]
    have hHonBun : HonestBundleDir compI0 (compRecordsI0 w) (ssBundle w) := by
      rw [← honestPublicBundle_eq_ssBundle w]
      exact honestBundleDir_honestPublicBundle compI0_cryptoEquationsHold hwf
    have hAliceFp : ∀ x ∈ ssAliceBaseFiles w, CliFilePath x.1 := by
      rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
      exact commonFiles_alice_cliFilePath compI0 (compRecordsI0 w)
    have hBobFp : ∀ x ∈ ssBobBaseFiles w, CliFilePath x.1 := by
      rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
      intro x hx
      rcases List.mem_append.mp hx with h1 | h2
      · exact commonFiles_bob_cliFilePath hwf.1 x h1
      · exact bobPreKeyFiles_cliFilePath rfl hSpkId hKpkId x h2
    have hAliceBd : FilesBounded (filesOf (ssAliceBaseFiles w)) := by
      rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
      exact filesBounded_of_cliFilePaths (commonFiles_alice_cliFilePath compI0 (compRecordsI0 w))
        (commonFiles_alice_bounded compI0_cryptoEquationsHold hwf)
    have hBobBd : FilesBounded (filesOf (ssBobBaseFiles w)) := by
      rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
      apply filesBounded_of_cliFilePaths
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact commonFiles_bob_cliFilePath hwf.1 x h1
        · exact bobPreKeyFiles_cliFilePath rfl hSpkId hKpkId x h2
      · intro x hx
        rcases List.mem_append.mp hx with h1 | h2
        · exact commonFiles_bob_bounded compI0_cryptoEquationsHold hwf x h1
        · exact bobPreKeyFiles_bounded compI0_cryptoEquationsHold hwf rfl x h2
    let t0 := mkTurn (filesOf (ssAliceBaseFiles w)) (filesOf (ssBobBaseFiles w)) [] false
    rw [initTurn_eq_mkTurn w hSpkId hKpkId]
    have hVal0 : ValidCall compI0 (compRecordsI0 w) t0 (ssCall0 w) := by
      have hNoSess0 : t0.records (compRecordsI0 w) "alice" = none := by
        dsimp only [t0]
        rw [← initTurn_eq_mkTurn w hSpkId hKpkId]
        exact initDirs_alice_no_session compI0 (compRecordsI0 w)
      have hc0Len : ssC0Coins.length = 192 := cliCoins0_length
      dsimp only [ValidCall, StdinBounded, BobCallAllowed, ssCall0, t0]
      exact ⟨hc0Len, trivial, by simpa [mkTurn] using hAliceBd, (fun h => nomatch h),
        rfl, rfl, rfl, rfl, hNoSess0, honestBundleDir_to_flat_and_honest hHonBun⟩
    have hInp0 : InputsFor (ssCall0 w) (t0.dirs "alice") (ssInp0 w) := by
      rw [ssInp0_eq_mkInp]
      exact inputsFor_of_cliFilePaths (ssCall0 w) (ssAliceBaseFiles w) hAliceFp
        (bundleFiles_cliFilePath (ssBundle w))
        (by rw [← commonFiles_alice_eq_ssAliceBaseFiles w]
            exact commonFiles_alice_bounded compI0_cryptoEquationsHold hwf)
        (fun x hx => ((honestBundleDir_to_flat_and_honest hHonBun).1 x hx).2)
        (by have hc0Len : ssC0Coins.length = 192 := cliCoins0_length; dsimp only [ssCall0]; omega)
    have hEv0 : runEventOf (ssCall0 w) (some (0, [])) = evInit := by
      have hpbf := parseBundleFiles_of_honestBundleDir hHonBun
      have hbunEq : bunBytes = bundleFast := by
        rw [bunBytes_eq]; rfl
      unfold runEventOf runInput ssCall0 evInit
      dsimp only
      rw [hpbf, Option.map_some, Option.getD_some, hBun, ← hbunEq, cliCoins0_eq_ssC0Coins]
      rfl
    let t1 := mkTurn (filesOf (scrubList files0)) (filesOf (ssBobBaseFiles w)) [] false
    have hAfter0 : t0.after (compRecordsI0 w) (ssCall0 w) 0 [] (filesOf files0) = t1 := by
      rw [after_alice_mkTurn (w := w) rfl,
        scrub_filesOf_eq_filesOf_scrubList (validCall0Files_cliFilePath hValid0)]
      rfl
    have hVal1 : ValidCall compI0 (compRecordsI0 w) t1 ssCall1 := by
      have hc1Len : ssC1Coins.length = 64 := by decide +kernel
      have hptLen : ssC1Pt.length < 2 ^ 32 := by decide +kernel
      dsimp only [ValidCall, StdinBounded, BobCallAllowed, ssCall1, t1, mkTurn]
      exact ⟨hc1Len, hptLen,
        validCall0Files_scrub_bounded hValid0,
        (fun h => nomatch h), Or.inl rfl, rfl, rfl, by decide,
        validCall0Files_alice_records_ne_none hValid0 rfl (filesOf (ssBobBaseFiles w)) [] false⟩
    have hInp1 : InputsFor ssCall1 (t1.dirs "alice") (ssInp1 files0) := by
      rw [ssInp1_eq_mkInp]
      exact inputsFor_of_cliFilePaths ssCall1 (scrubList files0)
        (validCall0Files_scrub_cliFilePath hValid0) (fun _ h => nomatch h)
        (fun x hx => by
          have hv := hValid0; unfold ValidCall0Files at hv; simp only [Bool.and_eq_true] at hv
          exact of_decide_eq_true (List.all_eq_true.mp hv.1.2 x hx))
        (fun _ h => nomatch h)
        (by change ssC1Coins.length < 2 ^ 31; decide +kernel)
    have hEv1 : runEventOf ssCall1 (some (0, ssC1Out)) = evSend := by
      unfold runEventOf runInput ssCall1 evSend
      rw [ptB_eq_ssC1Pt, cB_eq_ssC1Coins, sentWirePlant_eq_ssC1Out]
      rfl
    let t2 := mkTurn (scrub outDir1) (filesOf (ssBobBaseFiles w)) (sentBody ssC1Out).toList false
    have hAfter1 : t1.after (compRecordsI0 w) ssCall1 0 ssC1Out outDir1 = t2 :=
      after_alice_mkTurn (w := w) rfl
    have hVal2 : ValidCall compI0 (compRecordsI0 w) t2 (ssCall2 c2Msg ssC2Coins) := by
      have hba : ("bob" : String) ≠ "alice" := by decide
      have hc2Len : ssC2Coins.length = 32 := by decide +kernel
      have hHeadNe := canonicalPreKey_head_ne_whisper (canonicalPreKey_of_check hCanon)
      dsimp only [ValidCall, BobCallAllowed, ssCall2, t2]
      refine ⟨hc2Len, stdinBounded_recv_of_check hStdin2,
        by simpa [mkTurn, hba] using hBobBd, (fun h => nomatch h),
        Or.inr rfl, rfl, rfl, Or.inr ⟨rfl, Or.inl hHeadNe, ?_⟩⟩
      intro q hq
      have hPq2' := hPq2 q hq
      rw [sentWireSS_eq_ssC1Out] at hPq2'
      exact hPq2'
    have hba : ("bob" : String) ≠ "alice" := by decide
    have hInp2 : InputsFor (ssCall2 c2Msg ssC2Coins) (t2.dirs "bob")
        (ssInp2 w c2Msg ssC2Coins) := by
      dsimp only [t2, mkTurn]
      simp only [hba, ↓reduceIte]
      rw [ssInp2_eq_mkInp]
      exact inputsFor_of_cliFilePaths (ssCall2 c2Msg ssC2Coins) (ssBobBaseFiles w) hBobFp
        (fun _ h => nomatch h)
        (by rw [← bobFiles_eq_ssBobBaseFiles w hSpkId hKpkId]
            intro x hx
            exact (List.mem_append.mp hx).elim
              (commonFiles_bob_bounded compI0_cryptoEquationsHold hwf x)
              (bobPreKeyFiles_bounded compI0_cryptoEquationsHold hwf rfl x))
        (fun _ h => nomatch h)
        (by change ssC2Coins.length < 2 ^ 31; decide +kernel)
    have hEv2 : runEventOf (ssCall2 c2Msg ssC2Coins) (some (0, ssC2Out)) = evRecv c2Msg := by
      unfold runEventOf runInput ssCall2 evRecv
      rw [rngMsg39_eq_ssC2Coins, acceptMsg40_eq_ssC2Out]
      rfl
    unfold cliEvents
    rw [← hEv0, ← hEv1, ← hEv2]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal0 hInp0 hRun0 ?_
    rw [hAfter0]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal1 hInp1 hRun1 ?_
    rw [hAfter1]
    refine CliTraces.step (leaks := []) (fun _ h => nomatch h) hVal2 hInp2 hRun2 ?_
    exact CliTraces.done _
  ·
    rw [← hEvs]
    apply invertsGuarded_of_noInverts
    unfold cliEvents evInit evSend evRecv
    rfl

/-- Specialization of `ss_impl_half_pinned_of_three_calls_dirs_placed` to concrete post-call file
lists. -/
theorem ss_impl_half_pinned_of_three_calls_placed
    {w : PQXDHSpqrSetup} {evs : List CliEvent}
    (hPlaus : w.Plausible)
    (hTor : TorsionShiftsRecorded compI0 w.torsionShifts)
    (hSpkId : w.spkId = 7) (hKpkId : w.kpkId = 9)
    (hBun : bundleBlob (ssBundle w) = bundleFast)
    {c2Msg : HwBytes}
    (hCanon : checkCanonicalPreKey c2Msg = true)
    (hStdin2 : checkRecvStdinBounded c2Msg = true)
    (hPq2 : ∀ q, parsePreKeyWire c2Msg = some q →
      PqFromHonest (sentBody sentWireBytes).toList q.message)
    (hEvs : cliEvents c2Msg = evs)
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (_hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp0 w) = some (ssOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp1 files0) = some (ssOut1 files1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 (ssInp2 w c2Msg ssC2Coins) =
      some (ssOut2 ssC2Out files2)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf (cliCompFitsPinned w) H evs :=
  ss_impl_half_pinned_of_three_calls_dirs_placed hPlaus hTor hSpkId hKpkId hBun hCanon hStdin2 hPq2
    hEvs mpl mmpl H files0 (filesOf files1) (filesOf files2) hValid0 hRun0 hRun1 hRun2

private theorem hb_pqFromHonest :
    ∀ q, parsePreKeyWire hbC2Msg = some q →
      PqFromHonest (sentBody sentWireBytes).toList q.message := by
  intro q hq
  apply highBit_pqFromHonest q
  rw [highBitWireBytes_eq]
  exact hq

private theorem hb_cliEvents_eq :
    cliEvents hbC2Msg = Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  have h1 : hbC2Msg = highBitWireBytes :=
    highBitWireBytes_eq.symm
  rw [h1,
    ← Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.recvMsg38_eq_ss_highBitWireBytes]
  exact Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.cliEvents_eq

theorem impl_half_pinned_of_three_calls_dirs_placed
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 : List (String × HwBytes)) (outDir1 outDir2 : DirectorySnapshot)
    (hValid0 : ValidCall0Files files0 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (hbInp1 files0) =
      some (.exited 0 ssC1Out outDir1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp2 = some (.exited 0 ssC2Out outDir2)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      H Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  ss_impl_half_pinned_of_three_calls_dirs_placed
    (w := Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
    (by decide +kernel) (fun _ h => nomatch h) rfl rfl hbBundle_blob_eq
    (by decide +kernel) (by decide +kernel) hb_pqFromHonest hb_cliEvents_eq
    mpl mmpl H files0 outDir1 outDir2 hValid0 hRun0 hRun1 hRun2

/-- Placed pinned `ImplHalf` for `Cheval26SmallSubgroupHighBitCli` from three concrete CLI runs. -/
theorem impl_half_pinned_of_three_calls_placed
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (hbInp1 files0) = some (hbOut1 files1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp2 = some (hbOut2 files2)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
      H Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace :=
  ss_impl_half_pinned_of_three_calls_placed
    (w := Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup)
    (by decide +kernel) (fun _ h => nomatch h) rfl rfl hbBundle_blob_eq
    (by decide +kernel) (by decide +kernel) hb_pqFromHonest hb_cliEvents_eq
    mpl mmpl H files0 files1 files2 hValid0 hValid1 hRun0 hRun1 hRun2

/-- Placed unpinned `ImplHalf` for `Cheval26SmallSubgroupHighBitCli` from three concrete CLI runs. -/
theorem impl_half_of_three_calls_placed
    (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 : List (String × HwBytes))
    (hValid0 : ValidCall0Files files0 = true)
    (hValid1 : ValidCall1Files files1 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp0 = some (hbOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (hbInp1 files0) = some (hbOut1 files1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 hbInp2 = some (hbOut2 files2)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf
      Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.fits
      H Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.trace := by
  obtain ⟨iw, r, hfit, hc, htr⟩ :=
    impl_half_pinned_of_three_calls_placed mpl mmpl H files0 files1 files2 hValid0 hValid1
      hRun0 hRun1 hRun2
  exact ⟨iw, r, cliCompFits_of_pinned hfit, hc, htr⟩

end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.ImplTracePlaced
