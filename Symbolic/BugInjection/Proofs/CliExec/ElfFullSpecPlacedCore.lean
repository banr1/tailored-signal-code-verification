/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore

/-!
# Image-Free Placed ELF Checkpoint Specification and Chunk Runners

Defines the image-free pre-elaborated specification `ElfFullSpecPlaced` for relocatable
(`MultiPlacement`-parametric) CLI execution, together with depth-3/4 `BinTree` split helpers,
per-chunk execution wrappers, and the multi-chunk reachability predicate `ElfCkptReachablePlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore

open Arm64 Arm64.Process
open CryptoVerification.SignalSession (Inputs)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (FastProgPlaced FastReachablePlaced
  PrebuiltElfPlaced checkFastAborted checkFastExited checkFastExited0 fastRunChunkCachedPlaced
  fastRunChunkCachedPlaced_eq initFastStateFromBasePlaced initFastStateFromBasePlacedProcess)

export Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)

/-- Pre-elaborated specification of a placed CLI `ElfImage`: 12 header and placement scalars,
the hooked stub tree `hooks`, and token-patched `baseLines`. -/
structure ElfFullSpecPlaced where
  entry          : BitVec 64
  phdrVaddr      : BitVec 64
  phnum          : Nat
  brkStart       : BitVec 64
  tokStorageAddr : BitVec 64
  tokOnceAddr    : BitVec 64
  callocAddr     : BitVec 64
  callocSentinel : BitVec 64
  mallocAddr     : BitVec 64
  mallocSentinel : BitVec 64
  freeAddr       : BitVec 64
  freeSentinel   : BitVec 64
  hooks          : BinTree String
  baseLines      : BinTree Line64

/-- Header-only `ElfImage` agreeing with `fs` on `(entry, phdrVaddr, phent = 56, phnum, brkStart)`
with empty `segments` and `symbols`. -/
def headerElfOfFullPlaced (fs : ElfFullSpecPlaced) : ElfImage :=
  { entry     := fs.entry
    phdrVaddr := fs.phdrVaddr
    phent     := 56
    phnum     := fs.phnum
    segments  := []
    brkStart  := fs.brkStart
    symbols   := [] }

def addrsOfFullPlaced (fs : ElfFullSpecPlaced) : MallocngCallAddrs :=
  { callocAddr     := fs.callocAddr
    callocSentinel := fs.callocSentinel
    mallocAddr     := fs.mallocAddr
    mallocSentinel := fs.mallocSentinel
    freeAddr       := fs.freeAddr
    freeSentinel   := fs.freeSentinel }

def prebuiltOfFullPlaced (fs : ElfFullSpecPlaced) : PrebuiltElfPlaced :=
  { baseLines := fs.baseLines
    prog      := { addrs := addrsOfFullPlaced fs, hooks := fs.hooks, rxLines := fs.baseLines } }

abbrev MkCkpt : Type := PrebuiltElfPlaced → FastState → FastState

def ckptInit : MkCkpt := fun _ fs0 => fs0

private theorem buildInitialStack_congr {e1 e2 : ElfImage} (pinputs : ProcessInputs)
    (hentry : e1.entry = e2.entry) (hphdr : e1.phdrVaddr = e2.phdrVaddr)
    (hphent : e1.phent = e2.phent) (hphnum : e1.phnum = e2.phnum)
    (hbrk : e1.brkStart = e2.brkStart) :
    buildInitialStack e1 pinputs = buildInitialStack e2 pinputs := by
  unfold buildInitialStack
  simp only [hentry, hphdr, hphent, hphnum, hbrk]

/-- `initFastStateFromBasePlaced` depends on `elf` only through `(entry, phdrVaddr, phent, phnum, brkStart)`. -/
theorem initFastStateFromBasePlaced_congr {e1 e2 : ElfImage} (pb : PrebuiltElfPlaced) (inp : Inputs)
    (hentry : e1.entry = e2.entry) (hphdr : e1.phdrVaddr = e2.phdrVaddr)
    (hphent : e1.phent = e2.phent) (hphnum : e1.phnum = e2.phnum)
    (hbrk : e1.brkStart = e2.brkStart) :
    initFastStateFromBasePlaced e1 pb inp = initFastStateFromBasePlaced e2 pb inp := by
  unfold initFastStateFromBasePlaced initFastStateFromBasePlacedProcess
  rw [buildInitialStack_congr _ hentry hphdr hphent hphnum hbrk, hentry, hbrk]

def treeL {α : Type} : BinTree α → BinTree α
  | .branch l _ => l
  | _ => .empty

def treeR {α : Type} : BinTree α → BinTree α
  | .branch _ r => r
  | _ => .empty

def isFullDepth3 {α : Type} : BinTree α → Bool
  | .branch (.branch (.branch _ _) (.branch _ _))
            (.branch (.branch _ _) (.branch _ _)) => true
  | _ => false

/-- Extract depth-3 subtree `m ∈ 0..7` for low-bit residue `hi % 8 = m`. -/
def treeSub3 {α : Type} (m : Nat) (t : BinTree α) : BinTree α :=
  match m with
  | 0 => treeL (treeL (treeL t))
  | 1 => treeL (treeL (treeR t))
  | 2 => treeL (treeR (treeL t))
  | 3 => treeL (treeR (treeR t))
  | 4 => treeR (treeL (treeL t))
  | 5 => treeR (treeL (treeR t))
  | 6 => treeR (treeR (treeL t))
  | _ => treeR (treeR (treeR t))

/-- Reassemble a depth-3 `BinTree` from its 8 low-bit residue subtrees `b0..b7` (`hi % 8 = m`). -/
def mkDepth3 {α : Type} (b0 b1 b2 b3 b4 b5 b6 b7 : BinTree α) : BinTree α :=
  .branch
    (.branch (.branch b0 b4) (.branch b2 b6))
    (.branch (.branch b1 b5) (.branch b3 b7))

theorem eq_mkDepth3 {α : Type} {t b0 b1 b2 b3 b4 b5 b6 b7 : BinTree α}
    (hf : isFullDepth3 t = true)
    (h0 : treeSub3 0 t = b0) (h1 : treeSub3 1 t = b1)
    (h2 : treeSub3 2 t = b2) (h3 : treeSub3 3 t = b3)
    (h4 : treeSub3 4 t = b4) (h5 : treeSub3 5 t = b5)
    (h6 : treeSub3 6 t = b6) (h7 : treeSub3 7 t = b7) :
    t = mkDepth3 b0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold isFullDepth3 at hf
  split at hf
  · dsimp only [treeSub3, treeL, treeR] at h0 h1 h2 h3 h4 h5 h6 h7
    subst h0 h1 h2 h3 h4 h5 h6 h7
    rfl
  · nomatch hf

def isFullDepth4 {α : Type} : BinTree α → Bool
  | .branch l r => isFullDepth3 l && isFullDepth3 r
  | _ => false

/-- Extract depth-4 subtree `m ∈ 0..15` for low-bit residue `hi % 16 = m`. -/
def treeSub4 {α : Type} (m : Nat) (t : BinTree α) : BinTree α :=
  match m with
  | 0  => treeSub3 0 (treeL t)
  | 1  => treeSub3 0 (treeR t)
  | 2  => treeSub3 1 (treeL t)
  | 3  => treeSub3 1 (treeR t)
  | 4  => treeSub3 2 (treeL t)
  | 5  => treeSub3 2 (treeR t)
  | 6  => treeSub3 3 (treeL t)
  | 7  => treeSub3 3 (treeR t)
  | 8  => treeSub3 4 (treeL t)
  | 9  => treeSub3 4 (treeR t)
  | 10 => treeSub3 5 (treeL t)
  | 11 => treeSub3 5 (treeR t)
  | 12 => treeSub3 6 (treeL t)
  | 13 => treeSub3 6 (treeR t)
  | 14 => treeSub3 7 (treeL t)
  | _  => treeSub3 7 (treeR t)

/-- Reassemble a depth-4 `BinTree` from its 16 low-bit residue subtrees `b0..b15` (`hi % 16 = m`). -/
def mkDepth4 {α : Type}
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree α) : BinTree α :=
  .branch
    (mkDepth3 b0 b2 b4 b6 b8 b10 b12 b14)
    (mkDepth3 b1 b3 b5 b7 b9 b11 b13 b15)

theorem eq_mkDepth4 {α : Type}
    {t b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree α}
    (hf : isFullDepth4 t = true)
    (h0 : treeSub4 0 t = b0) (h1 : treeSub4 1 t = b1)
    (h2 : treeSub4 2 t = b2) (h3 : treeSub4 3 t = b3)
    (h4 : treeSub4 4 t = b4) (h5 : treeSub4 5 t = b5)
    (h6 : treeSub4 6 t = b6) (h7 : treeSub4 7 t = b7)
    (h8 : treeSub4 8 t = b8) (h9 : treeSub4 9 t = b9)
    (h10 : treeSub4 10 t = b10) (h11 : treeSub4 11 t = b11)
    (h12 : treeSub4 12 t = b12) (h13 : treeSub4 13 t = b13)
    (h14 : treeSub4 14 t = b14) (h15 : treeSub4 15 t = b15) :
    t = mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  cases t with
  | empty => nomatch hf
  | twig _ _ => nomatch hf
  | branch l r =>
    simp only [isFullDepth4, Bool.and_eq_true] at hf
    dsimp only [treeSub4, treeL, treeR] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [eq_mkDepth3 hf.1 h0 h2 h4 h6 h8 h10 h12 h14,
        eq_mkDepth3 hf.2 h1 h3 h5 h7 h9 h11 h13 h15]
    rfl

def runElfChunkPlacedLHS (fs : ElfFullSpecPlaced) (inp : Inputs) (k : Nat) (src : MkCkpt) :
    Option FastState :=
  let pb := prebuiltOfFullPlaced fs
  match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
  | none => none
  | some fs0 => fastRunChunkCachedPlaced pb.prog k (src pb fs0)

def runElfChunkPlacedRHS (fs : ElfFullSpecPlaced) (inp : Inputs) (dst : MkCkpt) :
    Option FastState :=
  let pb := prebuiltOfFullPlaced fs
  match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
  | none => none
  | some fs0 => some (dst pb fs0)

def checkElfFinalChunkPlacedExited0 (fs : ElfFullSpecPlaced) (inp : Inputs) (k : Nat) (src : MkCkpt)
    (outStdout : List (BitVec 8)) (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFullPlaced fs
  match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlaced pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastExited0 fsf outStdout outFiles

def checkElfFinalChunkPlacedExited (fs : ElfFullSpecPlaced) (inp : Inputs) (k : Nat) (src : MkCkpt)
    (code : BitVec 64) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFullPlaced fs
  match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlaced pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastExited fsf code outStdout outFiles

def checkElfFinalChunkPlacedAborted (fs : ElfFullSpecPlaced) (inp : Inputs) (k : Nat)
    (src : MkCkpt) : Bool :=
  let pb := prebuiltOfFullPlaced fs
  match initFastStateFromBasePlaced (headerElfOfFullPlaced fs) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlaced pb.prog k (src pb fs0) with
    | none => false
    | some fsf => checkFastAborted fsf

/-- Reachability from the initial placed fast state `fs0` to `dst (prebuiltOfFullPlaced fs) fs0`. -/
def ElfCkptReachablePlaced (fs : ElfFullSpecPlaced) (inp : Inputs) (dst : MkCkpt) : Prop :=
  ∀ fs0 : FastState,
    initFastStateFromBasePlaced (headerElfOfFullPlaced fs) (prebuiltOfFullPlaced fs) inp =
      some fs0 →
    FastReachablePlaced (prebuiltOfFullPlaced fs).prog fs0 (dst (prebuiltOfFullPlaced fs) fs0)

theorem ElfCkptReachablePlaced.init {fs : ElfFullSpecPlaced} {inp : Inputs} :
    ElfCkptReachablePlaced fs inp ckptInit := by
  intro fs0 _
  exact .refl fs0

theorem ElfCkptReachablePlaced.step {fs : ElfFullSpecPlaced} {inp : Inputs} {src dst : MkCkpt}
    {k : Nat}
    (hprev : ElfCkptReachablePlaced fs inp src)
    (hchunk : runElfChunkPlacedLHS fs inp k src = runElfChunkPlacedRHS fs inp dst) :
    ElfCkptReachablePlaced fs inp dst := by
  intro fs0 hinit
  have h1 := hprev fs0 hinit
  unfold runElfChunkPlacedLHS runElfChunkPlacedRHS at hchunk
  dsimp only at hchunk
  rw [hinit] at hchunk
  dsimp only at hchunk
  exact .trans h1 (.pow2 k (fastRunChunkCachedPlaced_eq hchunk))

end Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
