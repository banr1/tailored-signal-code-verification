/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.Proofs.SpecLemmas.ElfBindingFixed
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins

/-!
# 7-Call Weak-State CLI Implementation Trace Builder

Reduces `cliCompShape.ImplHalf` (at both `cliCompFitsPinned` and `cliCompFits`) for
`Witnesses.Cheval26WeakStateIdx1Cli` on any `H : Arm64.Process.ElfImage` to seven
`cliRunAbortOnPanic H compHooks0` runs (`wsInp0`..`wsInp6` → `wsOut0`..`wsOut6`) validated by
`ValidStepFiles`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace

open Arm64 (FsPath FsEntry FsState normalizePath)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF HonestBundle EligibleForSessionPromotion ecKey kyberKey pubBytes
   clamp secretBytes setupPublic parsePreKeyWire preKeyWire sentBody PqFromHonest slice
   recordBytes bytesField msgField u32Field chainBytes)
open DY.Libsignal.PQXDH.Refinement (preKeyBundleByteLength)
open DY.Libsignal.Refinement (encodeField paddedVarint)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot ValidCall InputsFor FilesVisible FilesBounded StdinBounded
   BobCallAllowed PreKeyNoMatch LeaksFrom CliTraces InvertsGuarded SamePath scrub parseBundleFiles
   bundleBlob BundleFilesFlat HonestBundleFiles aliceUuid bobUuid addrOf peerOf nameOf peerNameOf
   sessionPathOf textBytes idSecret peerIdSecret regIdOf commonFiles bobPreKeyFiles initDirs
   runInput runEventOf coinsLen elfRel HooksMatchInterpretation ExternContractsHoldCli
   runFnToRelation)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure SignedPreKeyRecordStructure)
open CryptoVerification.SignalSession
  (Inputs Outcome CliHooks Cmd PublicBundle Address cliRunAbortOnPanic filesOf fsView stdioPaths
   partyDirs bundleDir coinsFile addressFile identityKeyPairFile registrationIdFile identityFile
   sessionFile signedPreKeyFile lastResortKyberPreKeyFile baseKeysFile le32)
open Symbolic.BugInjection (PQXDHSpqrSetup cliCompShape cliCompFits hexBytes compFitsPinned)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compLookupPub)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliCompFitsPinned compHooks0 compI0_externContractsHoldCli compI0_hooksAgree
   cliCompFitsPinned_satisfiable_ws1)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_publicKey)

abbrev FileList := List (String × HwBytes)

abbrev wsSetup : PQXDHSpqrSetup := Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup
abbrev wsTrace : List CliEvent := Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace

def rawRunAt (k : Nat) : RunEvent := match wsTrace[k]? with
  | some (.run ev) => ev | _ => { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }
def rawExitOutAt (k : Nat) : HwBytes := match (rawRunAt k).exit with | some (_, out) => out | none => []
private theorem rawExitOutAt_of_some {k : Nat} {c : Nat} {out : HwBytes}
    (h : (rawRunAt k).exit = some (c, out)) : rawExitOutAt k = out := by
  unfold rawExitOutAt; rw [h]

def hexBytesChars (cs : List Char) : HwBytes :=
  Symbolic.BugInjection.hexBytes.go
    (fun c => if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10) cs
theorem hexBytes_eq_hexBytesChars (s : String) : hexBytes s = hexBytesChars s.toList := rfl

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem hexBytes_of_ofList (s : String) (cs : List Char) (bs : HwBytes)
    (hs : s = String.ofList cs) (hb : hexBytesChars cs = bs) : hexBytes s = bs := by
  rw [hexBytes_eq_hexBytesChars, hs, String.toList_ofList, hb]

section FastHex
open Lean Meta Elab Command

private meta def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

private meta def parseHexStr (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (16 * hexDigitVal a + hexDigitVal b) :: go rest | _ => []
  go s.toList

private meta def buildByteListExpr (s : String) : Expr := Id.run do
  let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let mut bsExpr := mkApp (mkConst ``List.nil [0]) bv8Ty
  for b in (parseHexStr s).reverse do
    bsExpr := mkApp3 (mkConst ``List.cons [0]) bv8Ty
      (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit b.toNat)) bsExpr
  return bsExpr

private meta def precompiledStrEqs : List Name :=
  [ ``PtPrefixInv35.bundle0Str_eq, ``PtPrefixInv38.wire37Str_eq, ``SpecTop.recv40Str_eq,
    ``SpecTop.recv81Str_eq, ``Wire80.wire80Str_eq, ``CompRSchedBSeedPins.schedBCall1SendStr_eq,
    ``CompRSchedBSeedPins.schedBCall2SendStr_eq, ``CompRSchedBSeedPins.schedBCall5SendStr_eq,
    ``CompRSchedBSeedPins.schedBCall6RecvStr_eq ]

private meta def findPrecompiledStrEq (s : String) : MetaM (Option (Expr × Expr)) := do
  for nm in precompiledStrEqs do
    let ty := (← getConstInfo nm).type
    if ty.isAppOfArity ``Eq 3 then
      if let .lit (.strVal candS) := ty.getAppArgs[1]! then
        let rhs := ty.getAppArgs[2]!
        if candS == s && rhs.isAppOfArity ``String.ofList 1 then
          return some (rhs.getAppArgs[0]!, mkConst nm)
  return none

private meta def buildFastHexProof (s : String) (defConst : Expr) : MetaM Expr := do
  let charTy := mkConst ``Char; let strTy := mkConst ``String
  let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let sLit := mkStrLit s; let hbPrf := mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty defConst
  if let some (csConst, hsPrf) ← findPrecompiledStrEq s then
    return mkApp5 (mkConst ``hexBytes_of_ofList) sLit csConst defConst hsPrf hbPrf
  if s.length > 512 then throwError "no precompiled Str_eq matches string of length {s.length}"
  let mut csExpr := mkApp (mkConst ``List.nil [0]) charTy
  for c in s.toList.reverse do csExpr := mkApp3 (mkConst ``List.cons [0]) charTy (toExpr c) csExpr
  let hsPrf := mkApp2 (mkConst ``Eq.refl [1]) strTy sLit
  return mkApp5 (mkConst ``hexBytes_of_ofList) sLit csExpr defConst hsPrf hbPrf

local elab "fast_hex_bytes " rhs:term : term => do
  let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let rhsExpr ← instantiateMVars (← Term.elabTermEnsuringType rhs listBv8Ty)
  let .lit (.strVal s) ← whnf (← whnf rhsExpr).getAppArgs[0]! | throwError "expected hex string literal"
  return buildByteListExpr s

local elab "def_fast_hex_eq " thmId:ident " : " rhs:term " := " defId:ident : command => do
  liftTermElabM do
    let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
    let rhsExpr ← instantiateMVars (← Term.elabTermEnsuringType rhs listBv8Ty)
    let defConst := mkConst (← realizeGlobalConstNoOverloadWithInfo defId)
    let .lit (.strVal s) ← whnf (← whnf rhsExpr).getAppArgs[0]! | throwError "expected hex string literal"
    let hexStrExpr := mkApp (mkConst ``Symbolic.BugInjection.hexBytes) (mkStrLit s)
    let eqEv ← if rhsExpr.isAppOfArity ``rawExitOutAt 1 then
        let kExpr := rhsExpr.getAppArgs[0]!
        let hExit ← mkEqRefl (mkProj ``RunEvent 4 (mkApp (mkConst ``rawRunAt) kExpr))
        pure <| mkApp4 (mkConst ``rawExitOutAt_of_some) kExpr (mkNatLit 0) hexStrExpr hExit
      else pure <| mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty rhsExpr
    let eqHexGo ← buildFastHexProof s defConst
    let fullPrf := mkAppN (mkConst ``Eq.trans [1]) #[listBv8Ty, rhsExpr, hexStrExpr, defConst, eqEv, eqHexGo]
    let declName := (← getCurrNamespace) ++ thmId.getId
    let fullTy := mkApp3 (mkConst ``Eq [1]) listBv8Ty rhsExpr defConst
    addDecl <| .thmDecl { name := declName, levelParams := [], type := fullTy, value := fullPrf }

def c0InFast : HwBytes := fast_hex_bytes (rawRunAt 0).input
def coins0 : HwBytes := fast_hex_bytes (rawRunAt 0).coins
def pt1 : HwBytes := fast_hex_bytes (rawRunAt 1).input
def coins1 : HwBytes := fast_hex_bytes (rawRunAt 1).coins
def c1Out : HwBytes := fast_hex_bytes (rawExitOutAt 1)
def pt2 : HwBytes := fast_hex_bytes (rawRunAt 2).input
def coins2 : HwBytes := fast_hex_bytes (rawRunAt 2).coins
def c2Out : HwBytes := fast_hex_bytes (rawExitOutAt 2)
def c3In : HwBytes := fast_hex_bytes (rawRunAt 3).input
def coins3 : HwBytes := fast_hex_bytes (rawRunAt 3).coins
def pt3Out : HwBytes := fast_hex_bytes (rawExitOutAt 3)
def c4InFast : HwBytes := fast_hex_bytes (rawRunAt 4).input
def coins4 : HwBytes := fast_hex_bytes (rawRunAt 4).coins
def pt5 : HwBytes := fast_hex_bytes (rawRunAt 5).input
def coins5 : HwBytes := fast_hex_bytes (rawRunAt 5).coins
def c5Out : HwBytes := fast_hex_bytes (rawExitOutAt 5)
def c6In : HwBytes := fast_hex_bytes (rawRunAt 6).input
def coins6 : HwBytes := fast_hex_bytes (rawRunAt 6).coins
def pt6Out : HwBytes := fast_hex_bytes (rawExitOutAt 6)
def nilBytes : HwBytes := []
set_option maxRecDepth 20000
def_fast_hex_eq rawRun0_in_eq : (rawRunAt 0).input := c0InFast
def_fast_hex_eq rawRun0_coins_eq : (rawRunAt 0).coins := coins0
def_fast_hex_eq rawRun0_out_eq : rawExitOutAt 0 := nilBytes
def_fast_hex_eq rawRun1_in_eq : (rawRunAt 1).input := pt1
def_fast_hex_eq rawRun1_coins_eq : (rawRunAt 1).coins := coins1
def_fast_hex_eq rawRun1_out_eq : rawExitOutAt 1 := c1Out
def_fast_hex_eq rawRun2_in_eq : (rawRunAt 2).input := pt2
def_fast_hex_eq rawRun2_coins_eq : (rawRunAt 2).coins := coins2
def_fast_hex_eq rawRun2_out_eq : rawExitOutAt 2 := c2Out
def_fast_hex_eq rawRun3_in_eq : (rawRunAt 3).input := c3In
def_fast_hex_eq rawRun3_coins_eq : (rawRunAt 3).coins := coins3
def_fast_hex_eq rawRun3_out_eq : rawExitOutAt 3 := pt3Out
def_fast_hex_eq rawRun4_in_eq : (rawRunAt 4).input := c4InFast
def_fast_hex_eq rawRun4_coins_eq : (rawRunAt 4).coins := coins4
def_fast_hex_eq rawRun4_out_eq : rawExitOutAt 4 := nilBytes
def_fast_hex_eq rawRun5_in_eq : (rawRunAt 5).input := pt5
def_fast_hex_eq rawRun5_coins_eq : (rawRunAt 5).coins := coins5
def_fast_hex_eq rawRun5_out_eq : rawExitOutAt 5 := c5Out
def_fast_hex_eq rawRun6_in_eq : (rawRunAt 6).input := c6In
def_fast_hex_eq rawRun6_coins_eq : (rawRunAt 6).coins := coins6
def_fast_hex_eq rawRun6_out_eq : rawExitOutAt 6 := pt6Out
end FastHex

def noInvertEvent : CliEvent → Bool | .env (.invertDH ..) | .env (.invertKEM ..) => false | _ => true

theorem invertsGuarded_of_noInverts {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs : List CliEvent} (h : evs.all noInvertEvent = true) : InvertsGuarded interp r evs := by
  intro pre post e heq
  have hok := List.all_eq_true.mp h (.env e) (by rw [heq]; simp)
  cases e <;> simp [noInvertEvent] at hok ⊢

theorem wsTrace_invertsGuarded (r : ProtocolSetup) : InvertsGuarded compI0 r wsTrace :=
  invertsGuarded_of_noInverts (by decide +kernel)

def cliDirPaths : List FsPath := partyDirs.map normalizePath ++ [[bundleDir]]

def isCliFilePath (p : String) : Bool :=
  let np := normalizePath p
  !np.isEmpty && !(stdioPaths.map normalizePath).contains np && !cliDirPaths.contains np &&
    ((FsPath.nonEmptyPrefixes np).dropLast).all (fun pref => cliDirPaths.contains pref) &&
    !Arm64.hasLeadingSlash p && !Arm64.hasDotDot p

def validFileList (l : FileList) : Bool := l.all (fun x => isCliFilePath x.1 && decide (x.2.length < 2 ^ 31))
def foldStep (np : FsPath) (acc : Option HwBytes) (x : String × HwBytes) : Option HwBytes :=
  if np == normalizePath x.1 then some x.2 else acc
def evalFileList (l : FileList) (p : String) : Option HwBytes := l.foldl (foldStep (normalizePath p)) none

private def entryFileBytes : Option FsEntry → Option HwBytes | some (.file bs) => some bs | _ => none
private def fsStepFile (fs : FsState) (x : String × HwBytes) : FsState :=
  (((FsPath.nonEmptyPrefixes (normalizePath x.1)).dropLast).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile x.1 (some (.file x.2))

private theorem setDir_foldl_nonFile {ancs : List FsPath} {np : FsPath} (fs : FsState)
    (h0 : entryFileBytes (fs.entries np) = none) :
    entryFileBytes ((ancs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries np) = none := by
  induction ancs generalizing fs with
  | nil => exact h0
  | cons a rest ih => apply ih; unfold FsState.setEntry; dsimp only; split <;> [rfl; exact h0]

private theorem setDir_foldl_outside {ancs : List FsPath} {np : FsPath} (fs : FsState)
    (hancs : ∀ pref ∈ ancs, pref ∈ cliDirPaths) (hnp : np ∉ cliDirPaths) :
    (ancs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries np = fs.entries np := by
  induction ancs generalizing fs with
  | nil => rfl
  | cons a rest ih =>
    have ha : a ∈ cliDirPaths := hancs a (List.mem_cons_self ..)
    have hne : (np == a) = false := beq_eq_false_iff_ne.mpr (fun h => hnp (h ▸ ha))
    have hstep : (fs.setEntry a (some .dir)).entries np = fs.entries np := by
      unfold FsState.setEntry; dsimp only; rw [hne]; rfl
    rw [List.foldl_cons, ih _ (fun p hp => hancs p (List.mem_cons_of_mem a hp)), hstep]

private theorem isCliFilePath_props {p : String} (h : isCliFilePath p = true) :
    normalizePath p ≠ [] ∧ normalizePath p ∉ stdioPaths.map normalizePath ∧
    normalizePath p ∉ cliDirPaths ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast, pref ∈ cliDirPaths) ∧
    Arm64.hasLeadingSlash p = false ∧ Arm64.hasDotDot p = false := by
  unfold isCliFilePath at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨(fun hemp => by rw [hemp] at h; cases h.1.1.1.1.1), h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem foldl_fsStepFile_nonFile {l : FileList} {np : FsPath} (fs : FsState)
    (hl : ∀ x ∈ l, isCliFilePath x.1 = true) (hnp : np = [] ∨ np ∈ cliDirPaths)
    (h0 : entryFileBytes (fs.entries np) = none) :
    entryFileBytes ((l.foldl fsStepFile fs).entries np) = none := by
  induction l generalizing fs with
  | nil => exact h0
  | cons x rest ih =>
    obtain ⟨hne_nil, _, hnot_dir, _⟩ := isCliFilePath_props (hl x (List.mem_cons_self ..))
    have hne : (np == normalizePath x.1) = false := beq_eq_false_iff_ne.mpr fun heq =>
      hnp.elim (fun h => hne_nil (heq.symm.trans h)) (fun hdir => hnot_dir (heq ▸ hdir))
    apply ih _ (fun y hy => hl y (List.mem_cons_of_mem x hy))
    unfold fsStepFile FsState.setFile; rw [FsState.setEntry]; dsimp only; rw [hne]
    exact setDir_foldl_nonFile fs h0

private theorem foldl_fsStepFile_file {l : FileList} {np : FsPath} (fs : FsState) (acc : Option HwBytes)
    (hl : ∀ x ∈ l, isCliFilePath x.1 = true) (hnot_dir : np ∉ cliDirPaths)
    (h0 : entryFileBytes (fs.entries np) = acc) :
    entryFileBytes ((l.foldl fsStepFile fs).entries np) = l.foldl (foldStep np) acc := by
  induction l generalizing fs acc with
  | nil => exact h0
  | cons x rest ih =>
    have hanc_eq := setDir_foldl_outside fs (isCliFilePath_props (hl x (List.mem_cons_self ..))).2.2.2.1 hnot_dir
    have hstep : entryFileBytes ((fsStepFile fs x).entries np) = foldStep np acc x := by
      unfold fsStepFile FsState.setFile; rw [FsState.setEntry]; dsimp only; unfold foldStep
      split <;> [rfl; rw [hanc_eq, h0]]
    exact ih (fsStepFile fs x) _ (fun y hy => hl y (List.mem_cons_of_mem x hy)) hstep

private theorem foldStep_eq_none_of_not_match {l : FileList} {np : FsPath}
    (h : ∀ x ∈ l, (np == normalizePath x.1) = false) : l.foldl (foldStep np) none = none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.foldl_cons]; unfold foldStep; rw [h x (List.mem_cons_self ..)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem filesOf_eq_evalFileList {l : FileList}
    (hl : l.all (fun x => isCliFilePath x.1) = true) (p : String) : filesOf l p = evalFileList l p := by
  have hall : ∀ x ∈ l, isCliFilePath x.1 = true := fun x hx => List.all_eq_true.mp hl x hx
  unfold filesOf fsView Arm64.Process.initFsState evalFileList
  dsimp only [FsState.files, FsState.getEntry, FsState.setFd]
  by_cases hstd : normalizePath p ∈ stdioPaths.map normalizePath
  · simp only [hstd, ↓reduceIte]; exact (foldStep_eq_none_of_not_match fun x hx =>
      beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).2.1 (heq ▸ hstd)).symm
  · simp only [hstd, ↓reduceIte]; by_cases hemp : (normalizePath p).isEmpty = true
    · simp only [hemp, ↓reduceIte]; have hnil : normalizePath p = [] := List.isEmpty_iff.mp hemp
      exact (foldStep_eq_none_of_not_match fun x hx =>
        beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).1 (heq.symm.trans hnil)).symm
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hempty_init : entryFileBytes (({} : FsState).entries (normalizePath p)) = none := by
        show entryFileBytes (if (normalizePath p).isEmpty then some .dir else none) = none
        simp [hemp, entryFileBytes]
      by_cases hdir : normalizePath p ∈ cliDirPaths
      · have lhs_none := foldl_fsStepFile_nonFile ({} : FsState) hall (Or.inr hdir) hempty_init
        have rhs_none := foldStep_eq_none_of_not_match fun x hx =>
          beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).2.2.1 (heq ▸ hdir)
        change entryFileBytes ((l.foldl fsStepFile ({} : FsState)).entries (normalizePath p)) = _
        rw [lhs_none, rhs_none]
      · change entryFileBytes ((l.foldl fsStepFile ({} : FsState)).entries (normalizePath p)) = _
        exact foldl_fsStepFile_file ({} : FsState) none hall hdir hempty_init

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

def scrubPred (np : FsPath) : Bool := (np == normalizePath coinsFile) || (np.head? == some bundleDir)
def scrubList (l : FileList) : FileList := l.filter (fun x => !scrubPred (normalizePath x.1))
def clearSessionList (sessPath : String) (l : FileList) : FileList :=
  l.filter (fun x => !(normalizePath x.1 == normalizePath sessPath))

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

def mkInpArgv (argv : List String) (c : CliCall) (base : FileList) : Inputs :=
  { argv, dirs := partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => []),
    files := base ++ c.extra, stdin := c.stdin }

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

def wsAliceSessPath : String := "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"
def wsBobSessPath : String := "sessions/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"
def wsPub (sk : HwBytes) : HwBytes := compLookupPub (clamp sk)
def textBytesFast (s : String) : HwBytes :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

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
def wsBundle : PublicBundle :=
  { identityKey := ecKey (wsPub wsSetup.bobId), registrationId := wsSetup.regIdB
    signedId := wsSetup.spkId, signedKey := ecKey (wsPub wsSetup.spk), signedSig := wsSetup.spkSig
    kyberId := wsSetup.kpkId, kyberKey := kyberKey wsSetup.kyberPk, kyberSig := wsSetup.kyberPkSig, oneTime := none }
def wsAliceBaseList : FileList :=
  [(addressFile, textBytesFast "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"),
   (identityKeyPairFile, IdentityKeyPairStructure.encode ⟨ecKey (wsPub wsSetup.aliceId), wsSetup.aliceId⟩),
   (registrationIdFile, le32 wsSetup.regIdA), (identityFile bobUuid, ecKey (wsPub wsSetup.bobId))]
def wsBobBaseList : FileList :=
  [(addressFile, textBytesFast "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"),
   (identityKeyPairFile, IdentityKeyPairStructure.encode ⟨ecKey (wsPub wsSetup.bobId), wsSetup.bobId⟩),
   (registrationIdFile, le32 wsSetup.regIdB), (identityFile aliceUuid, ecKey (wsPub wsSetup.aliceId)),
   ("signed-pre-keys/7", SignedPreKeyRecordStructure.encode
     ⟨wsSetup.spkId, ecKey (wsPub wsSetup.spk), wsSetup.spk, wsSetup.spkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9", SignedPreKeyRecordStructure.encode
     ⟨wsSetup.kpkId, kyberKey wsSetup.kyberPk, kyberKey (wsSetup.kyberSec.drop 1), wsSetup.kyberPkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9.base-keys", [])]
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
private theorem pubBytes_compI0 (sk : HwBytes) : pubBytes compI0 sk = wsPub sk := by rw [pubBytes, compI0_publicKey]; rfl
private theorem wsBundle_honest_slices :
    slice (bundleBlob wsBundle) 46 33 = ecKey (wsPub wsSetup.spk) ∧ slice (bundleBlob wsBundle) 79 64 = wsSetup.spkSig ∧
    slice (bundleBlob wsBundle) 147 1569 = kyberKey wsSetup.kyberPk ∧ slice (bundleBlob wsBundle) 1716 64 = wsSetup.kyberPkSig ∧
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

def s1 : HwBytes := ((parsePreKeyWire c1Out).map (·.message)).getD []
def s2 : HwBytes := ((parsePreKeyWire c2Out).map (·.message)).getD []
def s5 : HwBytes := ((parsePreKeyWire c5Out).map (·.message)).getD []
def c6BaseKey : HwBytes := ((parsePreKeyWire c6In).map (fun q => q.baseKey.take 33)).getD []

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

def startsWith : HwBytes → HwBytes → Bool
  | [], _ => true | _ :: _, [] => false | a :: as, b :: bs => (a == b) && startsWith as bs
def hasSublist (pat : HwBytes) : HwBytes → Bool
  | [] => pat.isEmpty | x :: xs => startsWith pat (x :: xs) || hasSublist pat xs
private theorem startsWith_append (pat rest : HwBytes) : startsWith pat (pat ++ rest) = true := by
  induction pat with | nil => rfl | cons a as ih => simp [startsWith, ih]
private theorem hasSublist_append (pre pat post : HwBytes) : hasSublist pat (pre ++ pat ++ post) = true := by
  induction pre with
  | nil =>
    cases pat with
    | nil => cases post <;> rfl
    | cons a as =>
      simp only [List.nil_append, List.cons_append, hasSublist]
      exact Bool.or_eq_true _ _ |>.mpr (Or.inl (startsWith_append (a :: as) post))
  | cons x xs ih => simp only [List.cons_append, hasSublist, ih, Bool.or_true]
private theorem bytesField13_sublist_recordBytes (rr : DY.Libsignal.Rust.RecordRec) :
    hasSublist (bytesField 13 rr.current.aliceBaseKey) (recordBytes rr) = true := by
  let s := rr.current
  let innerPre := u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
    bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
    u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
    s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
    ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
    u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId
  let innerPost := ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++ bytesField 15 s.pqRatchetState
  let inner := innerPre ++ bytesField 13 s.aliceBaseKey ++ innerPost
  have hrec : recordBytes rr = (paddedVarint (1 * 8 + 2) 0 ++ paddedVarint inner.length 0 ++ innerPre) ++
      bytesField 13 s.aliceBaseKey ++ (innerPost ++ rr.previous.flatMap (msgField 2)) := by
    dsimp only [inner, innerPre, innerPost, s]; unfold recordBytes msgField encodeField; simp only [List.append_assoc]
  rw [hrec]; exact hasSublist_append _ _ _

/-- Rules out `EligibleForSessionPromotion` when `rec_` omits the protobuf field-13 tag of `c6BaseKey`. -/
theorem not_eligibleForSessionPromotion_of_no_sublist {rec_ : HwBytes}
    (hno : hasSublist (bytesField 13 c6BaseKey) rec_ = false) : ¬ EligibleForSessionPromotion rec_ c6In := by
  rintro ⟨rr, p, hrec, _, hp, hbk⟩
  have hok := c6In_parsed_ok; rw [hp, Option.map_some, Option.some.injEq] at hok
  have hbk_eq : p.baseKey.take 33 = c6BaseKey := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hok).2
  have hsub := bytesField13_sublist_recordBytes rr; rw [← hrec, hbk, hbk_eq, hno] at hsub; cases hsub

def wsCall0 : CliCall := { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := wsBundle.files bundleDir, stdin := [], coins := coins0 }
def wsCall1 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt1, coins := coins1 }
def wsCall2 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt2, coins := coins2 }
def wsCall3 : CliCall := { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c3In, coins := coins3 }
def wsCall4 : CliCall := { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := wsBundle.files bundleDir, stdin := [], coins := coins4 }
def wsCall5 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt5, coins := coins5 }
def wsCall6 : CliCall := { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c6In, coins := coins6 }

def wsInp0 : Inputs := mkInpArgv ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] wsCall0 wsAliceBaseList
def wsInp1 (files0 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall1 (scrubList files0)
def wsInp2 (files1 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall2 (scrubList files1)
def wsInp3 : Inputs := mkInpArgv ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] wsCall3 wsBobBaseList
def wsInp4 (files2 : FileList) : Inputs := mkInpArgv ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] wsCall4 (clearSessionList wsAliceSessPath (scrubList files2))
def wsInp5 (files4 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall5 (scrubList files4)
def wsInp6 (files3 : FileList) : Inputs := mkInpArgv ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] wsCall6 (scrubList files3)

def wsOut0 (files0 : FileList) : Outcome := .exited 0 [] (filesOf files0)
def wsOut1 (files1 : FileList) : Outcome := .exited 0 c1Out (filesOf files1)
def wsOut2 (files2 : FileList) : Outcome := .exited 0 c2Out (filesOf files2)
def wsOut3 (files3 : FileList) : Outcome := .exited 0 pt3Out (filesOf files3)
def wsOut4 (files4 : FileList) : Outcome := .exited 0 [] (filesOf files4)
def wsOut5 (files5 : FileList) : Outcome := .exited 0 c5Out (filesOf files5)
def wsOut6 (files6 : FileList) : Outcome := .exited 0 pt6Out (filesOf files6)

def hasNonEmptySession (l : FileList) (sessPath : String) : Bool :=
  match evalFileList l sessPath with | some b => !b.isEmpty | none => false

def hasNoMatchBobSession (l : FileList) : Bool :=
  match evalFileList l wsBobSessPath with
  | some rec_ => !rec_.isEmpty && !hasSublist (bytesField 13 c6BaseKey) rec_ | none => false

/-- Decidable side-condition on post-call file lists `f0`..`f6`: valid bounded paths, non-empty
Alice sessions after calls 0, 1, and 4, and a non-matching Bob session after call 3. -/
def ValidStepFiles (f0 f1 f2 f3 f4 f5 f6 : FileList) : Bool :=
  validFileList f0 && validFileList f1 && validFileList f2 && validFileList f3 &&
  validFileList f4 && validFileList f5 && validFileList f6 &&
  hasNonEmptySession (scrubList f0) wsAliceSessPath && hasNonEmptySession (scrubList f1) wsAliceSessPath &&
  hasNoMatchBobSession (scrubList f3) && hasNonEmptySession (scrubList f4) wsAliceSessPath

private theorem validStepFiles_smoke :
    let aF := [(wsAliceSessPath, [1#8])]; let bF := [(wsBobSessPath, [1#8])]
    ValidStepFiles aF aF [] bF aF [] [] = true := by decide +kernel

def mkTurn (aDir bDir : DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) : CliTurn :=
  { dirs := fun q => if q = "alice" then aDir else if q = "bob" then bDir else fun _ => none, sent, bobOff }

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

theorem preKeyNoMatch_call6_of_files3 {r : ProtocolSetup} (ha : r.alice = "alice") (hb : r.bob = "bob")
    {files3 : FileList} (hv3 : validFileList files3 = true)
    (hnm3 : hasNoMatchBobSession (scrubList files3) = true)
    (aDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    PreKeyNoMatch r (mkTurn aDir (filesOf (scrubList files3)) sent off) wsCall6 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hv3s := scrubList_valid hv3; unfold hasNoMatchBobSession at hnm3
  cases hev : evalFileList (scrubList files3) wsBobSessPath <;> rw [hev] at hnm3
  · cases hnm3
  · rename_i rec_; obtain ⟨hne_bool, hnosub_bool⟩ := (Bool.and_eq_true _ _).mp hnm3
    have hrec_ne : rec_ ≠ [] := fun h => by rw [h] at hne_bool; cases hne_bool
    refine ⟨hb.symm, ⟨_, rfl⟩, c6In_head_ne_whisper, rec_, ?_,
      not_eligibleForSessionPromotion_of_no_sublist ((Bool.not_eq_true' _).mp hnosub_bool)⟩
    simp [CliTurn.records, mkTurn, hb, hba, sessPath_bob_eq ha,
      filesOf_eq_evalFileList (validFileList_paths hv3s), hev, hrec_ne]
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

private theorem ValidStepFiles.unpack {f0 f1 f2 f3 f4 f5 f6 : FileList}
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

/-- Reduces `cliCompShape.ImplHalf` at `cliCompFitsPinned` to seven `cliRunAbortOnPanic` runs
satisfying `ValidStepFiles`. -/
theorem impl_half_pinned_of_seven_calls (H : Arm64.Process.ElfImage)
    (files0 files1 files2 files3 files4 files5 files6 : FileList)
    (hValid : ValidStepFiles files0 files1 files2 files3 files4 files5 files6 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 wsInp0 = some (wsOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (wsInp1 files0) = some (wsOut1 files1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 (wsInp2 files1) = some (wsOut2 files2))
    (hRun3 : cliRunAbortOnPanic H compHooks0 wsInp3 = some (wsOut3 files3))
    (hRun4 : cliRunAbortOnPanic H compHooks0 (wsInp4 files2) = some (wsOut4 files4))
    (hRun5 : cliRunAbortOnPanic H compHooks0 (wsInp5 files4) = some (wsOut5 files5))
    (hRun6 : cliRunAbortOnPanic H compHooks0 (wsInp6 files3) = some (wsOut6 files6)) :
    cliCompShape.ImplHalf
      (cliCompFitsPinned Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup)
      H Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  obtain ⟨hv0, hv1, hv2, hv3, hv4, hv5, _hv6, hs0, hs1, hnm3, hs4⟩ := ValidStepFiles.unpack hValid
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
  change CliTraces (elfRel H compI0 compHooks0) compI0 r (CliTurn.init (initDirs compI0 r)) wsTrace
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
  let Rel := elfRel H compI0 compHooks0
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

/-- Unpinned `cliCompShape.ImplHalf` for `Cheval26WeakStateIdx1Cli` from seven
`cliRunAbortOnPanic` runs. -/
theorem impl_half_of_seven_calls (H : Arm64.Process.ElfImage)
    (files0 files1 files2 files3 files4 files5 files6 : FileList)
    (hValid : ValidStepFiles files0 files1 files2 files3 files4 files5 files6 = true)
    (hRun0 : cliRunAbortOnPanic H compHooks0 wsInp0 = some (wsOut0 files0))
    (hRun1 : cliRunAbortOnPanic H compHooks0 (wsInp1 files0) = some (wsOut1 files1))
    (hRun2 : cliRunAbortOnPanic H compHooks0 (wsInp2 files1) = some (wsOut2 files2))
    (hRun3 : cliRunAbortOnPanic H compHooks0 wsInp3 = some (wsOut3 files3))
    (hRun4 : cliRunAbortOnPanic H compHooks0 (wsInp4 files2) = some (wsOut4 files4))
    (hRun5 : cliRunAbortOnPanic H compHooks0 (wsInp5 files4) = some (wsOut5 files5))
    (hRun6 : cliRunAbortOnPanic H compHooks0 (wsInp6 files3) = some (wsOut6 files6)) :
    cliCompShape.ImplHalf Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.fits
      H Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  obtain ⟨iw, r, hpin, hc, htr⟩ := impl_half_pinned_of_seven_calls H files0 files1 files2 files3
    files4 files5 files6 hValid hRun0 hRun1 hRun2 hRun3 hRun4 hRun5 hRun6
  exact ⟨iw, r, ⟨hpin.1.1, hpin.2.1, hpin.2.2⟩, hc, htr⟩

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
