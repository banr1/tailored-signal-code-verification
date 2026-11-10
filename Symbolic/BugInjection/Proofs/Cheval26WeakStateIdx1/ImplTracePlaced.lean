/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShapePlaced
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace

/-!
# Placed 7-Call CLI Implementation Trace Builder for `Cheval26WeakStateIdx1Cli`

Reduces `(cliCompShapePlaced mpl mmpl).ImplHalf` for `Cheval26WeakStateIdx1Cli` (both pinned and
unpinned) on any `H : Arm64.Process.ElfImage` to the seven `Placed.cliRunPlacedSig mpl mmpl H compHooks0`
call outcomes (`wsInp0`..`wsInp6` → `wsOut0`..`wsOut6`) and the decidable guard `ValidStepFiles`.
Payload definitions, precompiled byte equalities, and trace inversion lemmas are imported from
`ImplTrace`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTracePlaced

open Arm64 (FsPath normalizePath)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup HonestBundle ecKey kyberKey pubBytes secretBytes setupPublic parsePreKeyWire
   preKeyWire sentBody PqFromHonest slice)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot ValidCall InputsFor FilesBounded StdinBounded BobCallAllowed
   PreKeyNoMatch CliTraces SamePath scrub parseBundleFiles bundleBlob BundleFilesFlat
   HonestBundleFiles aliceUuid bobUuid addrOf peerOf nameOf peerNameOf sessionPathOf textBytes
   idSecret peerIdSecret regIdOf commonFiles bobPreKeyFiles initDirs runInput runEventOf coinsLen
   elfRelPlaced)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.SignalSession
  (PublicBundle Cmd Address filesOf stdioPaths bundleDir coinsFile signedPreKeyFile
   lastResortKyberPreKeyFile baseKeysFile sessionFile)
open CryptoVerification.SignalSession.Placed (cliRunPlacedSig)
open Symbolic.BugInjection (cliCompShapePlaced compFitsPinned)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliCompFitsPinned compHooks0 compI0_externContractsHoldCli compI0_hooksAgree
   cliCompFitsPinned_satisfiable_ws1)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_publicKey)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
  (FileList wsSetup wsTrace rawRunAt rawExitOutAt c0InFast coins0 pt1 coins1 c1Out pt2 coins2
   c2Out c3In coins3 pt3Out c4InFast coins4 pt5 coins5 c5Out c6In coins6 pt6Out nilBytes
   rawRun0_in_eq rawRun0_coins_eq rawRun0_out_eq rawRun1_in_eq rawRun1_coins_eq rawRun1_out_eq
   rawRun2_in_eq rawRun2_coins_eq rawRun2_out_eq rawRun3_in_eq rawRun3_coins_eq rawRun3_out_eq
   rawRun4_in_eq rawRun4_coins_eq rawRun4_out_eq rawRun5_in_eq rawRun5_coins_eq rawRun5_out_eq
   rawRun6_in_eq rawRun6_coins_eq rawRun6_out_eq wsTrace_invertsGuarded cliDirPaths isCliFilePath
   validFileList foldStep evalFileList filesOf_eq_evalFileList scrubPred scrubList clearSessionList
   mkInpArgv wsAliceSessPath wsBobSessPath wsPub textBytesFast wsBundle wsAliceBaseList
   wsBobBaseList s1 s2 s5 c6BaseKey wsCall0 wsCall1 wsCall2 wsCall3 wsCall4 wsCall5 wsCall6
   wsInp0 wsInp1 wsInp2 wsInp3 wsInp4 wsInp5 wsInp6 wsOut0 wsOut1 wsOut2 wsOut3 wsOut4 wsOut5
   wsOut6 hasNonEmptySession hasNoMatchBobSession ValidStepFiles mkTurn
   preKeyNoMatch_call6_of_files3)

private theorem isCliFilePath_props {p : String} (h : isCliFilePath p = true) :
    normalizePath p ≠ [] ∧ normalizePath p ∉ stdioPaths.map normalizePath ∧
    normalizePath p ∉ cliDirPaths ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast, pref ∈ cliDirPaths) ∧
    Arm64.hasLeadingSlash p = false ∧ Arm64.hasDotDot p = false := by
  unfold isCliFilePath at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨(fun hemp => by rw [hemp] at h; cases h.1.1.1.1.1), h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem foldStep_eq_none_of_not_match {l : FileList} {np : FsPath}
    (h : ∀ x ∈ l, (np == normalizePath x.1) = false) : l.foldl (foldStep np) none = none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.foldl_cons]; unfold foldStep; rw [h x (List.mem_cons_self ..)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem validFileList_paths {l : FileList} (h : validFileList l = true) :
    l.all (fun x => isCliFilePath x.1) = true :=
  List.all_eq_true.mpr fun x hx => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h x hx)).1

private theorem validFileList_filter {l : FileList} (pred : (String × HwBytes) → Bool)
    (h : validFileList l = true) : validFileList (l.filter pred) = true :=
  List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_filter hx)

private theorem foldStep_init (np : FsPath) (l : FileList) (init : Option HwBytes) :
    l.foldl (foldStep np) init = (l.foldl (foldStep np) none).or init := by
  induction l generalizing init with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldl_cons]; rw [ih (foldStep np init x), ih (foldStep np none x), Option.or_assoc]
    congr 1; unfold foldStep; split <;> rfl

private theorem evalFileList_append (l1 l2 : FileList) (p : String) :
    evalFileList (l1 ++ l2) p = (evalFileList l2 p).or (evalFileList l1 p) := by
  unfold evalFileList; rw [List.foldl_append, foldStep_init]

private theorem foldStep_mem {np : FsPath} {l : FileList} {init : Option HwBytes} {b : HwBytes}
    (h : l.foldl (foldStep np) init = some b) : init = some b ∨ ∃ q, (q, b) ∈ l := by
  induction l generalizing init with
  | nil => exact Or.inl h
  | cons x rest ih =>
    rw [List.foldl_cons] at h; rcases ih h with hinit | ⟨q, hq⟩
    · unfold foldStep at hinit; split at hinit
      · injection hinit with hb; exact Or.inr ⟨x.1, hb ▸ List.mem_cons_self ..⟩
      · exact Or.inl hinit
    · exact Or.inr ⟨q, List.mem_cons_of_mem x hq⟩

private theorem filesBounded_of_validFileList {l : FileList} (h : validFileList l = true) :
    FilesBounded (filesOf l) := by
  intro path b hb; rw [filesOf_eq_evalFileList (validFileList_paths h), evalFileList] at hb
  rcases foldStep_mem hb with hnone | ⟨q, hq⟩
  · cases hnone
  · exact of_decide_eq_true ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h (q, b) hq)).2

private theorem foldStep_filter_neg (pred : FsPath → Bool) (np : FsPath)
    (hpred : pred np = false) (l : FileList) (init : Option HwBytes) :
    (l.filter (fun x => !pred (normalizePath x.1))).foldl (foldStep np) init = l.foldl (foldStep np) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.filter_cons, List.foldl_cons]; cases hx : pred (normalizePath x.1)
    · simp only [Bool.not_false, ↓reduceIte, List.foldl_cons]; exact ih (foldStep np init x)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hne : (np == normalizePath x.1) = false :=
        beq_eq_false_iff_ne.mpr fun heq => by rw [heq, hx] at hpred; cases hpred
      rw [show foldStep np init x = init by simp [foldStep, hne]]; exact ih init

private theorem evalFileList_filterOutPath (pred : FsPath → Bool) (l : FileList) (p : String) :
    evalFileList (l.filter (fun x => !pred (normalizePath x.1))) p =
      if pred (normalizePath p) then none else evalFileList l p := by
  unfold evalFileList; cases hpred : pred (normalizePath p)
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact foldStep_filter_neg pred (normalizePath p) hpred l none
  · simp only [↓reduceIte]; refine foldStep_eq_none_of_not_match fun x hx => beq_eq_false_iff_ne.mpr fun heq => ?_
    have hx' : (!pred (normalizePath x.1)) = true := (List.mem_filter.mp hx).2
    rw [← heq, hpred] at hx'; cases hx'

private theorem scrubList_valid {l : FileList} (h : validFileList l = true) :
    validFileList (scrubList l) = true := validFileList_filter (fun x => !scrubPred (normalizePath x.1)) h
private theorem clearSessionList_valid (s : String) {l : FileList} (h : validFileList l = true) :
    validFileList (clearSessionList s l) = true :=
  validFileList_filter (fun x => !(normalizePath x.1 == normalizePath s)) h

private theorem scrub_filesOf_eq_scrubList {l : FileList} (hl : validFileList l = true) :
    scrub (filesOf l) = filesOf (scrubList l) := by
  have hp_orig := validFileList_paths hl; have hp_scr := validFileList_paths (scrubList_valid hl)
  funext p; rw [filesOf_eq_evalFileList hp_scr, scrubList, evalFileList_filterOutPath]
  unfold scrub SamePath scrubPred; rw [filesOf_eq_evalFileList hp_orig]

private theorem clearSession_filesOf_eq_clearSessionList (sessPath : String) {l : FileList}
    (hl : validFileList l = true) :
    (fun path => if SamePath path sessPath then none else filesOf l path) =
      filesOf (clearSessionList sessPath l) := by
  funext path; rw [filesOf_eq_evalFileList (validFileList_paths (clearSessionList_valid sessPath hl)),
    clearSessionList, evalFileList_filterOutPath (fun np => np == normalizePath sessPath) l path,
    filesOf_eq_evalFileList (validFileList_paths hl)]; rfl

private theorem extra_paths_valid (c : CliCall) (hb : c.bundle.all (fun x => isCliFilePath x.1) = true) :
    c.extra.all (fun x => isCliFilePath x.1) = true := by
  unfold CliCall.extra; rw [List.all_append, hb, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true]
  dsimp only; decide

private theorem inputsFor_mkInpArgv (argv : List String) (c : CliCall) (base : FileList)
    (hargv : argv = c.cmd.argv)
    (hbase : validFileList base = true)
    (hbundle : c.bundle.all (fun x => isCliFilePath x.1) = true)
    (hbundle_len : c.bundle.all (fun x => decide (x.2.length < 2 ^ 31)) = true)
    (hcoins_len : c.coins.length < 2 ^ 31) :
    InputsFor c (filesOf base) (mkInpArgv argv c base) := by
  have hbp := validFileList_paths hbase; have hexp := extra_paths_valid c hbundle
  have hall : (base ++ c.extra).all (fun x => isCliFilePath x.1) = true := by
    rw [List.all_append, hbp, hexp]; rfl
  refine ⟨hargv, rfl, rfl, fun p _ => ?_, fun f hf => ?_⟩
  · show filesOf (base ++ c.extra) p = (filesOf c.extra p).or (filesOf base p)
    rw [filesOf_eq_evalFileList hall, evalFileList_append,
        filesOf_eq_evalFileList hexp, filesOf_eq_evalFileList hbp]
  · obtain ⟨hne, hstd, _, _, hsl, hdd⟩ := isCliFilePath_props (List.all_eq_true.mp hall f hf)
    have hlt : f.2.length < 2 ^ 31 := by
      rcases List.mem_append.mp hf with hb | hex
      · exact of_decide_eq_true ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp hbase f hb)).2
      · simp only [CliCall.extra, List.mem_append, List.mem_singleton] at hex
        rcases hex with hbun | rfl
        · exact of_decide_eq_true (List.all_eq_true.mp hbundle_len f hbun)
        · exact hcoins_len
    exact ⟨hne, hstd, hsl, hdd, Nat.le_trans (Nat.le_of_lt hlt) (by decide)⟩

private theorem byteArray_loop_eq (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop; split
  · next h =>
    have hi : i < arr.size := h; have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons his]
  · next h =>
    have hi : arr.toList.length ≤ i := by have : ¬ i < arr.size := h; simp at *; omega
    rw [List.drop_eq_nil_of_le hi, List.append_nil]
termination_by arr.size - i
decreasing_by have : i < arr.size := ‹_›; omega

private theorem textBytes_eq_fast (s : String) : textBytes s = textBytesFast s := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  unfold textBytes textBytesFast
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode]
  have hba : ∀ l : List UInt8, l.toByteArray.toList = l := fun l => by
    have h1 : l.toByteArray = ⟨l.toArray⟩ := by ext1; exact List.data_toByteArray
    rw [ByteArray.toList.eq_1, h1, byteArray_loop_eq]; simp
  rw [hba]

private theorem nat_repr_one : Nat.repr 1 = "1" := by
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl
private theorem toString_seven : toString (7 : Nat) = "7" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_seven.mpr rfl]; rfl
private theorem toString_nine : toString (9 : Nat) = "9" := by
  rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega), Nat.digitChar_eq_nine.mpr rfl]; rfl

private theorem wsAliceBaseList_valid : validFileList wsAliceBaseList = true := by decide +kernel
private theorem wsBobBaseList_valid : validFileList wsBobBaseList = true := by decide +kernel
private theorem wsBundle_paths_valid : (wsBundle.files bundleDir).all (fun x => isCliFilePath x.1) = true := by decide +kernel
private theorem wsAliceBaseList_no_sess : evalFileList wsAliceBaseList wsAliceSessPath = none := by decide +kernel
private theorem wsBobBaseList_no_sess : evalFileList wsBobBaseList wsBobSessPath = none := by decide +kernel

private theorem parseBundleFiles_congr {d1 d2 : DirectorySnapshot} (h : ∀ p, d1 p = d2 p) :
    parseBundleFiles d1 = parseBundleFiles d2 := by have hd : d1 = d2 := funext h; subst hd; rfl

private def publicBundleEq (a b : PublicBundle) : Bool :=
  a.identityKey == b.identityKey && a.registrationId == b.registrationId &&
  a.signedId == b.signedId && a.signedKey == b.signedKey && a.signedSig == b.signedSig &&
  a.kyberId == b.kyberId && a.kyberKey == b.kyberKey && a.kyberSig == b.kyberSig && a.oneTime == b.oneTime

private theorem parseBundle_wsBundle_eval :
    parseBundleFiles (evalFileList (wsBundle.files bundleDir)) = some wsBundle := by
  have h : (match parseBundleFiles (evalFileList (wsBundle.files bundleDir)) with
      | some b => publicBundleEq b wsBundle | none => false) = true := by decide +kernel
  cases hp : parseBundleFiles (evalFileList (wsBundle.files bundleDir)) <;> rw [hp] at h
  · cases h
  · rename_i b; cases b; unfold publicBundleEq at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
    cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9; rfl

private theorem parseBundle_wsBundle : parseBundleFiles (filesOf (wsBundle.files bundleDir)) = some wsBundle := by
  rw [parseBundleFiles_congr (filesOf_eq_evalFileList wsBundle_paths_valid)]; exact parseBundle_wsBundle_eval

private theorem bundleBlob_wsBundle_eq_c0In : bundleBlob wsBundle = c0InFast := by decide +kernel
private theorem bundleBlob_wsBundle_eq_c4In : bundleBlob wsBundle = c4InFast := by decide +kernel

private theorem wsBundle_flat : BundleFilesFlat (wsBundle.files bundleDir) := by
  have hdec : (wsBundle.files bundleDir).all (fun f =>
      (match normalizePath f.1 with | [d, _] => d == bundleDir | _ => false) &&
      decide (f.2.length < 2 ^ 31)) = true := by decide +kernel
  intro f hf; have h := (Bool.and_eq_true _ _).mp (List.all_eq_true.mp hdec f hf)
  refine ⟨?_, of_decide_eq_true h.2⟩
  rcases hnp : normalizePath f.1 with _ | ⟨d, _ | ⟨name, _ | _⟩⟩ <;> rw [hnp] at h
  · cases h.1
  · cases h.1
  · exact ⟨name, congrArg (· :: [name]) (beq_iff_eq.mp h.1)⟩
  · cases h.1

private theorem pubBytes_compI0 (sk : HwBytes) : pubBytes compI0 sk = wsPub sk := by
  rw [pubBytes, compI0_publicKey]; rfl

private theorem wsBundle_honest_slices :
    slice (bundleBlob wsBundle) 46 33 = ecKey (wsPub wsSetup.spk) ∧
    slice (bundleBlob wsBundle) 79 64 = wsSetup.spkSig ∧
    slice (bundleBlob wsBundle) 147 1569 = kyberKey wsSetup.kyberPk ∧
    slice (bundleBlob wsBundle) 1716 64 = wsSetup.kyberPkSig ∧
    slice (bundleBlob wsBundle) 1780 33 = ecKey (wsPub wsSetup.bobId) := by decide +kernel

private theorem wsBundle_honestFiles {r : ProtocolSetup} (hfit : compFitsPinned wsSetup compI0 r) :
    HonestBundleFiles compI0 r (wsBundle.files bundleDir) := by
  intro b hb; rw [parseBundle_wsBundle] at hb; injection hb with hb'; subst hb'; intro _
  obtain ⟨_, _, _, _, _, _, _, hs1, hs2, ho5, ho6, ho7, _⟩ := hfit.1
  dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecBytes,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecBytes,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm,
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]
  rw [pubBytes_compI0, pubBytes_compI0, hs1, hs2, ho5, ho6, ho7]; exact wsBundle_honest_slices

private theorem initDirs_eq_wsBase {r : ProtocolSetup} (hfit : compFitsPinned wsSetup compI0 r) :
    initDirs compI0 r = (fun q => if q = "alice" then filesOf wsAliceBaseList
      else if q = "bob" then filesOf wsBobBaseList else fun _ => none) := by
  obtain ⟨_, hopk, hregA, hregB, hspkId, hkpkId, hs0, hs1, hs2, ho5, ho6, ho7, hsec, _⟩ := hfit.1
  obtain ⟨halice, hbob⟩ := hfit.2.2.2.1; have hba : ("bob" : String) ≠ "alice" := by decide
  have haddrA : (addrOf r "alice").text = "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1" := by
    simp [addrOf, nameOf, halice, aliceUuid, Address.text, nat_repr_one]
  have haddrB : (addrOf r "bob").text = "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1" := by
    simp [addrOf, nameOf, halice, hba, bobUuid, Address.text, nat_repr_one]
  have hspkF : signedPreKeyFile r.spkId = "signed-pre-keys/7" := by
    rw [hspkId]; unfold signedPreKeyFile; rw [show wsSetup.spkId.toNat = 7 from rfl, toString_seven]; rfl
  have hkpkF : lastResortKyberPreKeyFile r.kpkId = "last-resort-kyber-pre-keys/9" := by
    rw [hkpkId]; unfold lastResortKyberPreKeyFile; rw [show wsSetup.kpkId.toNat = 9 from rfl, toString_nine]; rfl
  have hbkF : baseKeysFile r.kpkId = "last-resort-kyber-pre-keys/9.base-keys" := by
    rw [hkpkId]; unfold baseKeysFile; rw [show wsSetup.kpkId.toNat = 9 from rfl, toString_nine]; rfl
  funext q; unfold initDirs; rw [halice, hbob]
  by_cases hqa : q = "alice"
  · subst hqa; simp only [↓reduceIte]; congr 1; unfold commonFiles wsAliceBaseList
    rw [haddrA, textBytes_eq_fast]
    simp [idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
      regIdOf, peerNameOf, halice, pubBytes_compI0, hs0, hs1, hregA]
  · by_cases hqb : q = "bob"
    · subst hqb; simp only [hba, ↓reduceIte]; congr 1
      unfold commonFiles bobPreKeyFiles wsBobBaseList
      rw [haddrB, textBytes_eq_fast, hspkF, hkpkF, hbkF]
      simp [idSecret, peerIdSecret, ProtocolSetup.ikASecBytes, ProtocolSetup.ikBSecBytes,
        ProtocolSetup.spkSecBytes, ProtocolSetup.spkSigTerm, ProtocolSetup.pqpkPubTerm,
        ProtocolSetup.pqpkSigTerm, regIdOf, peerNameOf, halice, hba, hopk,
        pubBytes_compI0, hs0, hs1, hs2, ho5, ho6, ho7, hregB, hspkId, hkpkId, hsec]
    · simp [hqa, hqb]

private theorem sentBody_c1Out : sentBody c1Out = some s1 := by decide +kernel
private theorem sentBody_c2Out : sentBody c2Out = some s2 := by decide +kernel
private theorem sentBody_c5Out : sentBody c5Out = some s5 := by decide +kernel
private theorem coins0_len : coins0.length = 192 := by decide +kernel
private theorem coins1_len : coins1.length = 64 := by decide +kernel
private theorem coins2_len : coins2.length = 64 := by decide +kernel
private theorem coins3_len : coins3.length = 32 := by decide +kernel
private theorem coins4_len : coins4.length = 192 := by decide +kernel
private theorem coins5_len : coins5.length = 64 := by decide +kernel
private theorem coins6_len : coins6.length = 32 := by decide +kernel
private theorem pt1_len_lt : pt1.length < 2 ^ 32 := by decide +kernel
private theorem pt2_len_lt : pt2.length < 2 ^ 32 := by decide +kernel
private theorem pt5_len_lt : pt5.length < 2 ^ 32 := by decide +kernel
private theorem c3In_head_ne_whisper : c3In.head? ≠ some wireWhisperTag := by decide +kernel
private theorem c6In_head_ne_whisper : c6In.head? ≠ some wireWhisperTag := by decide +kernel
private theorem c3In_len_short : c3In.length + 2048 < 2 ^ 32 := by decide +kernel
private theorem c6In_len_short : c6In.length + 2048 < 2 ^ 32 := by decide +kernel
private theorem c3In_parsed_ok : ((parsePreKeyWire c3In).map (fun q =>
    decide (q.message ∈ [s1, s2]) && decide (q.message.length + 2048 < 2 ^ 32))) = some true := by decide +kernel
private theorem c6In_parsed_ok : ((parsePreKeyWire c6In).map (fun q =>
    decide (q.message ∈ [s1, s2, s5]) && decide (q.message.length + 2048 < 2 ^ 32) &&
    (q.baseKey.take 33 == c6BaseKey))) = some true := by decide +kernel

private theorem msg_length_le_preKeyWire (preKeyId : Option (BitVec 32))
    (spkId kpkId regId : BitVec 32) (ik ek ct msg : HwBytes) :
    msg.length ≤ (preKeyWire preKeyId spkId kpkId regId ik ek ct msg).length := by
  unfold preKeyWire DY.Libsignal.PQXDH.Refinement.PreKeyProto.encode
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
  simp only [List.length_cons, List.length_append]; omega

private theorem pqFromHonest_of_mem {sent : List HwBytes} {body : HwBytes} (hmem : body ∈ sent) :
    PqFromHonest sent body := fun m hm => ⟨body, hmem, m, hm, rfl⟩

private theorem cliTurn_mk_eq {d1 d2 : Participant → DirectorySnapshot} {s1' s2' : List HwBytes} {b1 b2 : Bool}
    (hd : d1 = d2) (hs : s1' = s2') (hb : b1 = b2) : CliTurn.mk d1 s1' b1 = CliTurn.mk d2 s2' b2 := by
  subst hd hs hb; rfl
private theorem sessPath_alice_eq {r : ProtocolSetup} (ha : r.alice = "alice") :
    sessionPathOf r "alice" = wsAliceSessPath := by
  simp [sessionPathOf, peerOf, peerNameOf, ha, sessionFile, Address.text, bobUuid, wsAliceSessPath, nat_repr_one]
private theorem sessPath_bob_eq {r : ProtocolSetup} (ha : r.alice = "alice") :
    sessionPathOf r "bob" = wsBobSessPath := by
  simp [sessionPathOf, peerOf, peerNameOf, ha, (by decide : ("bob" : String) ≠ "alice"),
    sessionFile, Address.text, aliceUuid, wsBobSessPath, nat_repr_one]
private theorem peerOf_alice_eq {r : ProtocolSetup} (ha : r.alice = "alice") :
    peerOf r "alice" = ⟨bobUuid, 1⟩ := by simp [peerOf, peerNameOf, ha]
private theorem peerOf_bob_eq {r : ProtocolSetup} (ha : r.alice = "alice") :
    peerOf r "bob" = ⟨aliceUuid, 1⟩ := by simp [peerOf, peerNameOf, ha, (by decide : ("bob" : String) ≠ "alice")]
private theorem records_alice_of_eval_none {r : ProtocolSetup} (ha : r.alice = "alice")
    {l : FileList} (hl : validFileList l = true) (hnone : evalFileList l wsAliceSessPath = none)
    (bDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn (filesOf l) bDir sent off).records r "alice" = none := by
  simp [CliTurn.records, mkTurn, sessPath_alice_eq ha, filesOf_eq_evalFileList (validFileList_paths hl), hnone]
private theorem records_bob_of_eval_none {r : ProtocolSetup} (ha : r.alice = "alice")
    {l : FileList} (hl : validFileList l = true) (hnone : evalFileList l wsBobSessPath = none)
    (aDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn aDir (filesOf l) sent off).records r "bob" = none := by
  simp [CliTurn.records, mkTurn, (by decide : ("bob" : String) ≠ "alice"), sessPath_bob_eq ha,
    filesOf_eq_evalFileList (validFileList_paths hl), hnone]
private theorem records_alice_ne_none {r : ProtocolSetup} (ha : r.alice = "alice")
    {l : FileList} (hl : validFileList l = true) (hsess : hasNonEmptySession l wsAliceSessPath = true)
    (bDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    (mkTurn (filesOf l) bDir sent off).records r "alice" ≠ none := by
  unfold hasNonEmptySession at hsess; cases hev : evalFileList l wsAliceSessPath <;> rw [hev] at hsess
  · cases hsess
  · rename_i bs; have hne : bs ≠ [] := fun h => by rw [h] at hsess; cases hsess
    simp [CliTurn.records, mkTurn, sessPath_alice_eq ha, filesOf_eq_evalFileList (validFileList_paths hl), hev, hne]

open Classical in
private theorem after_alice_mkTurn {r : ProtocolSetup} (hb : r.bob = "bob")
    {aDir bDir : DirectorySnapshot} {sent : List HwBytes} {c : CliCall} {out : HwBytes}
    {files : FileList} (hp : c.party = "alice") (hv : validFileList files = true) :
    (mkTurn aDir bDir sent false).after r c 0 out (filesOf files) =
      mkTurn (filesOf (scrubList files)) bDir
        (sent ++ (match c.cmd with | .send _ => (sentBody out).toList | _ => [])) false := by
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch r (mkTurn aDir bDir sent false) c) := fun ⟨_, hbob, _⟩ =>
    absurd (hp.symm.trans (hbob.trans hb)) (by decide)
  have hbob : ((mkTurn aDir bDir sent false).bobOff ||
      decide (0 = 0 ∧ PreKeyNoMatch r (mkTurn aDir bDir sent false) c)) = false := by
    rw [show (mkTurn aDir bDir sent false).bobOff = false from rfl, Bool.false_or]; exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]; simp only [hp, scrub_filesOf_eq_scrubList hv]; unfold mkTurn
  refine cliTurn_mk_eq (funext fun q => ?_) (by cases c.cmd <;> rfl) rfl
  by_cases hqa : q = "alice" <;> simp [hqa]

open Classical in
private theorem after_bob_call3 {r : ProtocolSetup} (ha : r.alice = "alice") (hb : r.bob = "bob")
    {aDir : DirectorySnapshot} {sent : List HwBytes} {files3 : FileList} (hv3 : validFileList files3 = true) :
    (mkTurn aDir (filesOf wsBobBaseList) sent false).after r wsCall3 0 pt3Out (filesOf files3) =
      mkTurn aDir (filesOf (scrubList files3)) sent false := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hnm : ¬ (0 = 0 ∧ PreKeyNoMatch r (mkTurn aDir (filesOf wsBobBaseList) sent false) wsCall3) := by
    rintro ⟨_, _, _, _, rec_, hrec, _⟩
    rw [hb, records_bob_of_eval_none ha wsBobBaseList_valid wsBobBaseList_no_sess] at hrec; cases hrec
  have hbob : ((mkTurn aDir (filesOf wsBobBaseList) sent false).bobOff ||
      decide (0 = 0 ∧ PreKeyNoMatch r (mkTurn aDir (filesOf wsBobBaseList) sent false) wsCall3)) = false := by
    rw [show (mkTurn aDir (filesOf wsBobBaseList) sent false).bobOff = false from rfl, Bool.false_or]
    exact decide_eq_false hnm
  unfold CliTurn.after; rw [hbob]
  simp only [show wsCall3.party = "bob" from rfl, show wsCall3.cmd = .recv ⟨aliceUuid, 1⟩ from rfl,
    scrub_filesOf_eq_scrubList hv3, List.append_nil]; unfold mkTurn
  refine cliTurn_mk_eq (funext fun q => ?_) rfl rfl
  by_cases hqa : q = "alice"
  · subst hqa; simp [hba.symm]
  · by_cases hqb : q = "bob" <;> simp [hqa, hqb]

private theorem clearSession_alice_mkTurn {r : ProtocolSetup} (ha : r.alice = "alice")
    {l : FileList} (hl : validFileList l = true) (bDir : DirectorySnapshot) (sent : List HwBytes) :
    (mkTurn (filesOf l) bDir sent false).clearSession r "alice" =
      mkTurn (filesOf (clearSessionList wsAliceSessPath l)) bDir sent false := by
  unfold CliTurn.clearSession mkTurn; simp only [Bool.false_and, sessPath_alice_eq ha]
  refine cliTurn_mk_eq (funext fun q => ?_) rfl rfl
  by_cases hqa : q = "alice"
  · subst hqa; simp only [↓reduceIte]; exact clearSession_filesOf_eq_clearSessionList wsAliceSessPath hl
  · simp [hqa]

private theorem validCall_init {r : ProtocolSetup} (hfit : compFitsPinned wsSetup compI0 r)
    {aList : FileList} (ha_valid : validFileList aList = true)
    (ha_nosess : evalFileList aList wsAliceSessPath = none)
    {bDir : DirectorySnapshot} {sent : List HwBytes} {c : CliCall}
    (hc : c = { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir,
                bundle := wsBundle.files bundleDir, stdin := [], coins := c.coins })
    (hcoins : c.coins.length = 192) :
    ValidCall compI0 r (mkTurn (filesOf aList) bDir sent false) c := by
  obtain ⟨ha, _⟩ := hfit.2.2.2.1; rw [hc]; dsimp only [ValidCall, StdinBounded, BobCallAllowed, coinsLen]
  refine ⟨hcoins, trivial, (by simpa [mkTurn] using filesBounded_of_validFileList ha_valid),
    (fun h => nomatch h), ha.symm, (by rw [ha, peerOf_alice_eq ha]), rfl, rfl,
    (by rw [ha]; exact records_alice_of_eval_none ha ha_valid ha_nosess bDir sent false),
    wsBundle_flat, wsBundle_honestFiles hfit⟩

private theorem validCall_send {r : ProtocolSetup} (ha : r.alice = "alice")
    {aList : FileList} (ha_valid : validFileList aList = true)
    (ha_sess : hasNonEmptySession aList wsAliceSessPath = true)
    {bDir : DirectorySnapshot} {sent : List HwBytes} (hsent : sent.length < 2 ^ 32 - 1) {c : CliCall}
    (hc : c = { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := c.stdin, coins := c.coins })
    (hcoins : c.coins.length = 64) (hstdin : c.stdin.length < 2 ^ 32) :
    ValidCall compI0 r (mkTurn (filesOf aList) bDir sent false) c := by
  rw [hc]; dsimp only [ValidCall, StdinBounded, BobCallAllowed, coinsLen]
  refine ⟨hcoins, hstdin, (by simpa [mkTurn] using filesBounded_of_validFileList ha_valid),
    (fun h => nomatch h), Or.inl ha.symm, (peerOf_alice_eq ha).symm, rfl, hsent,
    records_alice_ne_none ha ha_valid ha_sess bDir sent false⟩

private theorem stdinBounded_recv {c : CliCall} {peer : Address} (hcmd : c.cmd = .recv peer)
    (hshort : c.stdin.length + 2048 < 2 ^ 32)
    (hparsed : ∀ q, parsePreKeyWire c.stdin = some q → q.message.length + 2048 < 2 ^ 32) :
    StdinBounded c := by
  unfold StdinBounded; rw [hcmd]
  refine ⟨fun body h => ?_, fun _ => by omega, hparsed,
    fun preKeyId spkId kpkId regId ik ek ct msg _ _ _ hst => ?_⟩
  · rw [h] at hshort; simp only [List.length_cons] at hshort; omega
  · have hle := msg_length_le_preKeyWire preKeyId spkId kpkId regId (ecKey ik) ek ct msg; rw [← hst] at hle; omega

private theorem validCall3 {r : ProtocolSetup} (ha : r.alice = "alice") (hb : r.bob = "bob")
    (aDir : DirectorySnapshot) : ValidCall compI0 r (mkTurn aDir (filesOf wsBobBaseList) [s1, s2] false) wsCall3 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hparsed : ∀ q, parsePreKeyWire c3In = some q → q.message ∈ [s1, s2] ∧ q.message.length + 2048 < 2 ^ 32 :=
    fun q hq => by
      have hok := c3In_parsed_ok; rw [hq, Option.map_some, Option.some.injEq] at hok
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hok; exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  refine ⟨coins3_len, stdinBounded_recv rfl c3In_len_short (fun q hq => (hparsed q hq).2),
    (by simpa [mkTurn, wsCall3, hba] using filesBounded_of_validFileList wsBobBaseList_valid),
    (fun h => nomatch h), Or.inr hb.symm, (peerOf_bob_eq ha).symm, rfl,
    Or.inr ⟨hb.symm, Or.inl c3In_head_ne_whisper, fun q hq => pqFromHonest_of_mem (hparsed q hq).1⟩⟩

private theorem validCall6 {r : ProtocolSetup} (ha : r.alice = "alice") (hb : r.bob = "bob")
    {bList : FileList} (hb_valid : validFileList bList = true) (aDir : DirectorySnapshot) :
    ValidCall compI0 r (mkTurn aDir (filesOf bList) [s1, s2, s5] false) wsCall6 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hparsed : ∀ q, parsePreKeyWire c6In = some q → q.message ∈ [s1, s2, s5] ∧ q.message.length + 2048 < 2 ^ 32 :=
    fun q hq => by
      have hok := c6In_parsed_ok; rw [hq, Option.map_some, Option.some.injEq] at hok
      obtain ⟨h12, _⟩ := (Bool.and_eq_true _ _).mp hok; obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
  refine ⟨coins6_len, stdinBounded_recv rfl c6In_len_short (fun q hq => (hparsed q hq).2),
    (by simpa [mkTurn, wsCall6, hba] using filesBounded_of_validFileList hb_valid),
    (fun h => nomatch h), Or.inr hb.symm, (peerOf_bob_eq ha).symm, rfl,
    Or.inr ⟨hb.symm, Or.inl c6In_head_ne_whisper, fun q hq => pqFromHonest_of_mem (hparsed q hq).1⟩⟩

private theorem wsTrace_decomp : wsTrace = [.run (rawRunAt 0), .run (rawRunAt 1), .run (rawRunAt 2),
    .run (rawRunAt 3), .run (rawRunAt 4), .run (rawRunAt 5), .run (rawRunAt 6)] := rfl

private theorem runEvent_eq_mk {e1 e2 : RunEvent} (hp : e1.party = e2.party) (hc : e1.cmd = e2.cmd)
    (hi : e1.input = e2.input) (hco : e1.coins = e2.coins) (hex : e1.exit = e2.exit) : e1 = e2 := by
  cases e1; cases e2; dsimp only at hp hc hi hco hex; subst hp hc hi hco hex; rfl

private theorem rawExit_eq {k : Nat} (hk : ∃ out, (rawRunAt k).exit = some (0, out)) :
    (rawRunAt k).exit = some (0, rawExitOutAt k) := by obtain ⟨out, hout⟩ := hk; simp [rawExitOutAt, hout]

private theorem wsTrace_events_eq :
    [.run (runEventOf wsCall0 (some (0, []))), .run (runEventOf wsCall1 (some (0, c1Out))),
     .run (runEventOf wsCall2 (some (0, c2Out))), .run (runEventOf wsCall3 (some (0, pt3Out))),
     .run (runEventOf wsCall4 (some (0, []))), .run (runEventOf wsCall5 (some (0, c5Out))),
     .run (runEventOf wsCall6 (some (0, pt6Out)))] = wsTrace := by
  rw [wsTrace_decomp]
  have he0 : runEventOf wsCall0 (some (0, [])) = rawRunAt 0 := runEvent_eq_mk rfl rfl
    (by dsimp only [runEventOf, runInput, wsCall0]; rw [parseBundle_wsBundle]
        dsimp only [Option.map, Option.getD]; rw [bundleBlob_wsBundle_eq_c0In, rawRun0_in_eq])
    rawRun0_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun0_out_eq]; rfl)
  have he1 : runEventOf wsCall1 (some (0, c1Out)) = rawRunAt 1 := runEvent_eq_mk rfl rfl
    rawRun1_in_eq.symm rawRun1_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun1_out_eq])
  have he2 : runEventOf wsCall2 (some (0, c2Out)) = rawRunAt 2 := runEvent_eq_mk rfl rfl
    rawRun2_in_eq.symm rawRun2_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun2_out_eq])
  have he3 : runEventOf wsCall3 (some (0, pt3Out)) = rawRunAt 3 := runEvent_eq_mk rfl rfl
    rawRun3_in_eq.symm rawRun3_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun3_out_eq])
  have he4 : runEventOf wsCall4 (some (0, [])) = rawRunAt 4 := runEvent_eq_mk rfl rfl
    (by dsimp only [runEventOf, runInput, wsCall4]; rw [parseBundle_wsBundle]
        dsimp only [Option.map, Option.getD]; rw [bundleBlob_wsBundle_eq_c4In, rawRun4_in_eq])
    rawRun4_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun4_out_eq]; rfl)
  have he5 : runEventOf wsCall5 (some (0, c5Out)) = rawRunAt 5 := runEvent_eq_mk rfl rfl
    rawRun5_in_eq.symm rawRun5_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun5_out_eq])
  have he6 : runEventOf wsCall6 (some (0, pt6Out)) = rawRunAt 6 := runEvent_eq_mk rfl rfl
    rawRun6_in_eq.symm rawRun6_coins_eq.symm (by dsimp only [runEventOf]; rw [rawExit_eq ⟨_, rfl⟩, rawRun6_out_eq])
  rw [he0, he1, he2, he3, he4, he5, he6]

private theorem unpack_validStepFiles {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (h : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    validFileList f0 = true ∧ validFileList f1 = true ∧ validFileList f2 = true ∧
    validFileList f3 = true ∧ validFileList f4 = true ∧ validFileList f5 = true ∧
    validFileList f6 = true ∧ hasNonEmptySession (scrubList f0) wsAliceSessPath = true ∧
    hasNonEmptySession (scrubList f1) wsAliceSessPath = true ∧
    hasNoMatchBobSession (scrubList f3) = true ∧
    hasNonEmptySession (scrubList f4) wsAliceSessPath = true := by
  unfold ValidStepFiles at h; simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem argv_init_bob : ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] =
    (Cmd.init ⟨bobUuid, 1⟩ bundleDir).argv := by simp [Cmd.argv, Address.text, bobUuid, nat_repr_one]
private theorem argv_send_bob : ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] =
    (Cmd.send ⟨bobUuid, 1⟩).argv := by simp [Cmd.argv, Address.text, bobUuid, nat_repr_one]
private theorem argv_recv_alice : ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] =
    (Cmd.recv ⟨aliceUuid, 1⟩).argv := by simp [Cmd.argv, Address.text, aliceUuid, nat_repr_one]

/-- Reduces `(cliCompShapePlaced mpl mmpl).ImplHalf` at `cliCompFitsPinned setup` on `H` to the
seven `cliRunPlacedSig mpl mmpl H compHooks0` runs and `ValidStepFiles`. -/
theorem impl_half_pinned_of_seven_calls_placed (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 files3 files4 files5 files6 : FileList)
    (hValid : ValidStepFiles files0 files1 files2 files3 files4 files5 files6 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 wsInp0 = some (wsOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp1 files0) = some (wsOut1 files1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp2 files1) = some (wsOut2 files2))
    (hRun3 : cliRunPlacedSig mpl mmpl H compHooks0 wsInp3 = some (wsOut3 files3))
    (hRun4 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp4 files2) = some (wsOut4 files4))
    (hRun5 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp5 files4) = some (wsOut5 files5))
    (hRun6 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp6 files3) = some (wsOut6 files6)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup)
      H Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, _hv6, hs0, hs1, hnm3, hs4⟩ := unpack_validStepFiles hValid
  obtain ⟨⟨_, _⟩, r, hcomp, _, _⟩ := cliCompFitsPinned_satisfiable_ws1
  rcases hcomp.2.1 with rfl; obtain ⟨ha, hb⟩ := hcomp.2.2.2.1
  have hPin : cliCompFitsPinned wsSetup (compI0, compHooks0) r :=
    ⟨hcomp, compI0_externContractsHoldCli, compI0_hooksAgree⟩
  refine ⟨(compI0, compHooks0), r, hPin, ⟨compI0_externContractsHoldCli, compI0_hooksAgree⟩,
    ?_, wsTrace_invertsGuarded r⟩
  have hba : ("bob" : String) ≠ "alice" := by decide
  let a0 := wsAliceBaseList; let b0 := wsBobBaseList
  let a1 := scrubList files0; let a2 := scrubList files1; let a3 := scrubList files2
  let b3 := scrubList files3; let a4 := clearSessionList wsAliceSessPath a3
  let a5 := scrubList files4; let a6 := scrubList files5
  have hv_a1 := scrubList_valid hv0; have hv_a2 := scrubList_valid hv1
  have hv_a3 := scrubList_valid hv2; have hv_b3 := scrubList_valid hv3
  have hv_a4 := clearSessionList_valid wsAliceSessPath hv_a3
  have hv_a5 := scrubList_valid hv4; have _hv_a6 := scrubList_valid hv5
  have ha4_nosess : evalFileList a4 wsAliceSessPath = none := by
    simpa [a4, clearSessionList] using
      evalFileList_filterOutPath (fun np => np == normalizePath wsAliceSessPath) a3 wsAliceSessPath
  let t0 := mkTurn (filesOf a0) (filesOf b0) [] false
  let t1 := mkTurn (filesOf a1) (filesOf b0) [] false
  let t2 := mkTurn (filesOf a2) (filesOf b0) [s1] false
  let t3 := mkTurn (filesOf a3) (filesOf b0) [s1, s2] false
  let t4Pre := mkTurn (filesOf a3) (filesOf b3) [s1, s2] false
  let t4 := mkTurn (filesOf a4) (filesOf b3) [s1, s2] false
  let t5 := mkTurn (filesOf a5) (filesOf b3) [s1, s2] false
  let t6 := mkTurn (filesOf a6) (filesOf b3) [s1, s2, s5] false
  have _ : PreKeyNoMatch r t6 wsCall6 :=
    preKeyNoMatch_call6_of_files3 ha hb hv3 hnm3 (filesOf a6) [s1, s2, s5] false
  have hinit : CliTurn.init (initDirs compI0 r) = t0 := by
    unfold CliTurn.init t0 mkTurn; rw [initDirs_eq_wsBase hcomp]
  change CliTraces (elfRelPlaced mpl mmpl H compI0 compHooks0) compI0 r (CliTurn.init (initDirs compI0 r)) wsTrace
  rw [hinit, ← wsTrace_events_eq]
  have ht01 : t0.after r wsCall0 0 [] (filesOf files0) = t1 := by
    simpa [t0, t1, a1, show wsCall0.cmd = .init ⟨bobUuid, 1⟩ bundleDir from rfl] using
      after_alice_mkTurn hb (aDir := filesOf a0) (bDir := filesOf b0) (sent := []) (c := wsCall0) (out := []) rfl hv0
  have ht12 : t1.after r wsCall1 0 c1Out (filesOf files1) = t2 := by
    simpa [t1, t2, a2, show wsCall1.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c1Out] using
      after_alice_mkTurn hb (aDir := filesOf a1) (bDir := filesOf b0) (sent := []) (c := wsCall1) (out := c1Out) rfl hv1
  have ht23 : t2.after r wsCall2 0 c2Out (filesOf files2) = t3 := by
    simpa [t2, t3, a3, show wsCall2.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c2Out] using
      after_alice_mkTurn hb (aDir := filesOf a2) (bDir := filesOf b0) (sent := [s1]) (c := wsCall2) (out := c2Out) rfl hv2
  have ht34Pre : t3.after r wsCall3 0 pt3Out (filesOf files3) = t4Pre := after_bob_call3 ha hb hv3
  have hclr : t4Pre.clearSession r "alice" = t4 := clearSession_alice_mkTurn ha hv_a3 (filesOf b3) [s1, s2]
  have ht45 : t4.after r wsCall4 0 [] (filesOf files4) = t5 := by
    simpa [t4, t5, a5, show wsCall4.cmd = .init ⟨bobUuid, 1⟩ bundleDir from rfl] using
      after_alice_mkTurn hb (aDir := filesOf a4) (bDir := filesOf b3) (sent := [s1, s2]) (c := wsCall4) (out := []) rfl hv4
  have ht56 : t5.after r wsCall5 0 c5Out (filesOf files5) = t6 := by
    simpa [t5, t6, a6, show wsCall5.cmd = .send ⟨bobUuid, 1⟩ from rfl, sentBody_c5Out] using
      after_alice_mkTurn hb (aDir := filesOf a5) (bDir := filesOf b3) (sent := [s1, s2]) (c := wsCall5) (out := c5Out) rfl hv5
  have hwsBundle_len : (wsBundle.files bundleDir).all (fun x => decide (x.2.length < 2 ^ 31)) = true :=
    List.all_eq_true.mpr fun x hx => decide_eq_true (wsBundle_flat x hx).2
  let Rel := elfRelPlaced mpl mmpl H compI0 compHooks0
  have hs6 : CliTraces Rel compI0 r t6 _ :=
    CliTraces.step (leaks := []) (i := wsInp6 files3) (fun _ h => nomatch h)
      (validCall6 ha hb hv_b3 (filesOf a6))
      (by simp only [t6, mkTurn, show wsCall6.party = "bob" from rfl, hba, ↓reduceIte, b3, wsInp6]
          exact inputsFor_mkInpArgv _ wsCall6 b3 argv_recv_alice hv_b3 rfl rfl
            (by have := coins6_len; dsimp only [wsCall6]; omega)) hRun6 (CliTraces.done _)
  have hs5 : CliTraces Rel compI0 r t5 _ :=
    CliTraces.step (leaks := []) (i := wsInp5 files4) (fun _ h => nomatch h)
      (validCall_send ha hv_a5 hs4 (by decide) rfl coins5_len pt5_len_lt)
      (by simp only [t5, mkTurn, show wsCall5.party = "alice" from rfl, ↓reduceIte, a5, wsInp5]
          exact inputsFor_mkInpArgv _ wsCall5 a5 argv_send_bob hv_a5 rfl rfl
            (by have := coins5_len; dsimp only [wsCall5]; omega)) hRun5 (ht56.symm ▸ hs6)
  have hs4_tr : CliTraces Rel compI0 r t4 _ :=
    CliTraces.step (leaks := []) (i := wsInp4 files2) (fun _ h => nomatch h)
      (validCall_init hcomp hv_a4 ha4_nosess rfl coins4_len)
      (by simp only [t4, mkTurn, show wsCall4.party = "alice" from rfl, ↓reduceIte, a4, a3, wsInp4]
          exact inputsFor_mkInpArgv _ wsCall4 a4 argv_init_bob hv_a4 wsBundle_paths_valid hwsBundle_len
            (by have := coins4_len; dsimp only [wsCall4]; omega)) hRun4 (ht45.symm ▸ hs5)
  have hs_clr : CliTraces Rel compI0 r t4Pre _ := CliTraces.clear "alice" (hclr.symm ▸ hs4_tr)
  have hs3 : CliTraces Rel compI0 r t3 _ :=
    CliTraces.step (leaks := []) (i := wsInp3) (fun _ h => nomatch h) (validCall3 ha hb (filesOf a3))
      (by simp only [t3, mkTurn, show wsCall3.party = "bob" from rfl, hba, ↓reduceIte, b0, wsInp3]
          exact inputsFor_mkInpArgv _ wsCall3 b0 argv_recv_alice wsBobBaseList_valid rfl rfl
            (by have := coins3_len; dsimp only [wsCall3]; omega)) hRun3 (ht34Pre.symm ▸ hs_clr)
  have hs2_tr : CliTraces Rel compI0 r t2 _ :=
    CliTraces.step (leaks := []) (i := wsInp2 files1) (fun _ h => nomatch h)
      (validCall_send ha hv_a2 hs1 (by decide) rfl coins2_len pt2_len_lt)
      (by simp only [t2, mkTurn, show wsCall2.party = "alice" from rfl, ↓reduceIte, a2, wsInp2]
          exact inputsFor_mkInpArgv _ wsCall2 a2 argv_send_bob hv_a2 rfl rfl
            (by have := coins2_len; dsimp only [wsCall2]; omega)) hRun2 (ht23.symm ▸ hs3)
  have hs1_tr : CliTraces Rel compI0 r t1 _ :=
    CliTraces.step (leaks := []) (i := wsInp1 files0) (fun _ h => nomatch h)
      (validCall_send ha hv_a1 hs0 (by decide) rfl coins1_len pt1_len_lt)
      (by simp only [t1, mkTurn, show wsCall1.party = "alice" from rfl, ↓reduceIte, a1, wsInp1]
          exact inputsFor_mkInpArgv _ wsCall1 a1 argv_send_bob hv_a1 rfl rfl
            (by have := coins1_len; dsimp only [wsCall1]; omega)) hRun1 (ht12.symm ▸ hs2_tr)
  exact CliTraces.step (leaks := []) (i := wsInp0) (fun _ h => nomatch h)
    (validCall_init hcomp wsAliceBaseList_valid wsAliceBaseList_no_sess rfl coins0_len)
    (by simp only [t0, mkTurn, show wsCall0.party = "alice" from rfl, ↓reduceIte, a0, wsInp0]
        exact inputsFor_mkInpArgv _ wsCall0 a0 argv_init_bob wsAliceBaseList_valid wsBundle_paths_valid hwsBundle_len
          (by have := coins0_len; dsimp only [wsCall0]; omega))
    hRun0 (ht01.symm ▸ hs1_tr)

/-- Specialization of `impl_half_pinned_of_seven_calls_placed` to `Cheval26WeakStateIdx1Cli.fits`. -/
theorem impl_half_of_seven_calls_placed (mpl mmpl : Arm64.Obj.MultiPlacement)
    (H : Arm64.Process.ElfImage)
    (files0 files1 files2 files3 files4 files5 files6 : FileList)
    (hValid : ValidStepFiles files0 files1 files2 files3 files4 files5 files6 = true)
    (hRun0 : cliRunPlacedSig mpl mmpl H compHooks0 wsInp0 = some (wsOut0 files0))
    (hRun1 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp1 files0) = some (wsOut1 files1))
    (hRun2 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp2 files1) = some (wsOut2 files2))
    (hRun3 : cliRunPlacedSig mpl mmpl H compHooks0 wsInp3 = some (wsOut3 files3))
    (hRun4 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp4 files2) = some (wsOut4 files4))
    (hRun5 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp5 files4) = some (wsOut5 files5))
    (hRun6 : cliRunPlacedSig mpl mmpl H compHooks0 (wsInp6 files3) = some (wsOut6 files6)) :
    (cliCompShapePlaced mpl mmpl).ImplHalf Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.fits
      H Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  obtain ⟨iw, r, hpin, hc, htr⟩ := impl_half_pinned_of_seven_calls_placed mpl mmpl H
    files0 files1 files2 files3 files4 files5 files6 hValid
    hRun0 hRun1 hRun2 hRun3 hRun4 hRun5 hRun6
  exact ⟨iw, r, ⟨hpin.1.1, hpin.2.1, hpin.2.2⟩, hc, htr⟩

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTracePlaced
