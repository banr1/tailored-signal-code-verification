/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
meta import ProofLib.TestFiles

/-!
# Shared ELF64 Process Tour Fixture

Embeds `echo_stdin.elf` (`echoStdinBytes` and `echoStdinElf`), states the whole-binary safety and
functional contracts (`EchoStdinElfSafeStmt` and `EchoStdinElfCorrectStmt`), and provides a
balanced-tree initial-state constructor (`fastRawState`) equal to `ElfImage.rawState`.
-/

@[expose] public section

namespace Arm64.Testing.ProcessSemanticsTour

open Arm64 Arm64.Process

set_option autoImplicit false

requires_test_files ["../Regression/fixtures/echo_stdin.elf"]

set_option maxRecDepth 2000000 in
/-- Raw ELF64 (`ET_EXEC`) file bytes of `echo_stdin.elf`, compiled from `echo_stdin.c` with stock
    `zig cc -target aarch64-linux-musl -static`. -/
noncomputable def echoStdinBytes : List (BitVec 8) :=
  file_bytes% "../Regression/fixtures/echo_stdin.elf" sha256 "f68a8a20df9f37e96a023fb7aec0fcea44a1f48329655601a864571533c98e9f"

/-- Universal whole-binary `ElfSafe` statement for `echoStdinBytes` across all valid Linux
    `execve(2)` inputs (`inputs.Valid`): parsing and loading succeed, execution from `crt1.o`
    `_start` through `__libc_start_main` and `main` reaches `SYS_exit_group(0)`, and no reachable
    state ever faults. -/
def EchoStdinElfSafeStmt : Prop :=
  ElfSafe echoStdinBytes (fun inputs => inputs.Valid) (minPhysMem := fun _ => 0)

/-- Universal whole-binary `ElfCorrect` functional statement for `echoStdinBytes` across all valid
    Linux `execve(2)` inputs (`inputs.Valid`): exits with code `0`, writes `inputs.stdin` to
    `stdout`, and writes nothing to `stderr`. -/
def EchoStdinElfCorrectStmt : Prop :=
  ElfCorrect echoStdinBytes (fun inputs => inputs.Valid)
    (fun inputs out => out.stdout = inputs.stdin ∧ out.stderr = [])
    (minPhysMem := fun _ => 0)

set_option maxRecDepth 2000000 in
/-- Parsed `ElfImage` witness for `echo_stdin.elf` (`4,024` B). -/
noncomputable def echoStdinElf : ElfImage :=
  elf_image% "../Regression/fixtures/echo_stdin.elf"

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
theorem echoStdin_parse : ElfImage.parse echoStdinBytes = .ok echoStdinElf :=
  ElfImage.parse_of_fastParse rfl

end_requires_test_files

/-! ## Balanced Byte-Lookup Tree -/

/-- Balanced binary tree over a `List (BitVec 8)` built bottom-up so every `.node stride l r`
    satisfies `l.toList.length = stride`, giving $O(\log N)$ indexed byte lookup in the kernel. -/
inductive ByteTree where
  | empty
  | leaf (b : BitVec 8)
  | linear (bs : List (BitVec 8))
  | node (stride : Nat) (left right : ByteTree)

def ByteTree.toList : ByteTree → List (BitVec 8)
  | .empty => []
  | .leaf b => [b]
  | .linear bs => bs
  | .node _ l r => l.toList ++ r.toList

/-- $O(\log N)$ indexed byte lookup in a `ByteTree`. -/
def ByteTree.get? : ByteTree → Nat → Option (BitVec 8)
  | .empty, _ => none
  | .leaf b, 0 => some b
  | .leaf _, _ + 1 => none
  | .linear bs, i => bs[i]?
  | .node stride l r, i =>
    if i < stride then l.get? i else r.get? (i - stride)

/-- Well-formedness invariant: every `.node stride l r` has left subtree byte length `stride`. -/
def ByteTree.WF : ByteTree → Prop
  | .empty => True
  | .leaf _ => True
  | .linear _ => True
  | .node stride l r => l.WF ∧ r.WF ∧ l.toList.length = stride

private theorem ByteTree.get?_eq_getElem? {t : ByteTree} (ht : t.WF) (i : Nat) :
    t.get? i = t.toList[i]? := by
  induction t generalizing i with
  | empty => rfl
  | leaf b => cases i <;> rfl
  | linear bs => rfl
  | node stride l r ihl ihr =>
    obtain ⟨hl, hr, hlen⟩ := ht
    simp only [ByteTree.get?, ByteTree.toList]
    split
    · next h =>
      rw [ihl hl, List.getElem?_append_left (hlen ▸ h)]
    · next h =>
      have hle : l.toList.length ≤ i := by omega
      rw [ihr hr, List.getElem?_append_right hle, hlen]

def flatToList : List ByteTree → List (BitVec 8)
  | [] => []
  | t :: ts => t.toList ++ flatToList ts

private def ListWF (stride : Nat) : List ByteTree → Prop
  | [] => True
  | [t] => t.WF
  | t1 :: t2 :: rest => t1.WF ∧ t1.toList.length = stride ∧ ListWF stride (t2 :: rest)

def pairPass (stride : Nat) : List ByteTree → List ByteTree
  | [] => []
  | [t] => [t]
  | t1 :: t2 :: rest => .node stride t1 t2 :: pairPass stride rest

private theorem pairPass_nonEmpty {stride : Nat} :
    ∀ {ts : List ByteTree}, ts ≠ [] → pairPass stride ts ≠ []
  | [], h => absurd rfl h
  | [_], _ => List.cons_ne_nil _ _
  | _ :: _ :: _, _ => List.cons_ne_nil _ _

private theorem pairPass_flatToList (stride : Nat) :
    ∀ (ts : List ByteTree), flatToList (pairPass stride ts) = flatToList ts
  | [] => rfl
  | [_] => rfl
  | t1 :: t2 :: rest => by
    simp only [pairPass, flatToList, ByteTree.toList, List.append_assoc, pairPass_flatToList stride rest]

private theorem pairPass_wf (stride : Nat) :
    ∀ (ts : List ByteTree), ListWF stride ts → ListWF (stride + stride) (pairPass stride ts)
  | [], _ => trivial
  | [_], ht => ht
  | t1 :: t2 :: [], ⟨ht1, hlen1, ht2⟩ => ⟨ht1, ht2, hlen1⟩
  | t1 :: t2 :: t3 :: rest, ⟨ht1, hlen1, ht2, hlen2, hrest⟩ => by
    have ih := pairPass_wf stride (t3 :: rest) hrest
    have hne := pairPass_nonEmpty (stride := stride) (List.cons_ne_nil t3 rest)
    dsimp only [pairPass]
    cases hp : pairPass stride (t3 :: rest) with
    | nil => exact absurd hp hne
    | cons u us =>
      rw [hp] at ih
      refine ⟨⟨ht1, ht2, hlen1⟩, ?_, ih⟩
      simp only [ByteTree.toList, List.length_append, hlen1, hlen2]

def buildTreeLoop : Nat → Nat → List ByteTree → ByteTree
  | 0, _, ts => .linear (flatToList ts)
  | _, _, [] => .empty
  | _, _, [t] => t
  | fuel + 1, stride, ts => buildTreeLoop fuel (stride + stride) (pairPass stride ts)

private theorem buildTreeLoop_spec (fuel : Nat) :
    ∀ (stride : Nat) (ts : List ByteTree), ListWF stride ts →
      (buildTreeLoop fuel stride ts).WF ∧ (buildTreeLoop fuel stride ts).toList = flatToList ts := by
  induction fuel with
  | zero =>
    intro stride ts _
    exact ⟨trivial, rfl⟩
  | succ fuel ih =>
    intro stride ts hwf
    cases ts with
    | nil => exact ⟨trivial, rfl⟩
    | cons t1 rest =>
      cases rest with
      | nil =>
        dsimp only [buildTreeLoop, flatToList]
        rw [List.append_nil]
        exact ⟨hwf, rfl⟩
      | cons t2 rest' =>
        dsimp only [buildTreeLoop]
        obtain ⟨hwf', hlist⟩ := ih (stride + stride) (pairPass stride (t1 :: t2 :: rest'))
          (pairPass_wf stride (t1 :: t2 :: rest') hwf)
        exact ⟨hwf', hlist.trans (pairPass_flatToList stride (t1 :: t2 :: rest'))⟩

def initLeaves : List (BitVec 8) → List ByteTree
  | [] => []
  | b :: bs => .leaf b :: initLeaves bs

private theorem initLeaves_flatToList : ∀ (bs : List (BitVec 8)), flatToList (initLeaves bs) = bs
  | [] => rfl
  | b :: bs => congrArg (b :: ·) (initLeaves_flatToList bs)

private theorem initLeaves_wf : ∀ (bs : List (BitVec 8)), ListWF 1 (initLeaves bs)
  | [] => trivial
  | [_] => trivial
  | _ :: b2 :: bs => ⟨trivial, rfl, initLeaves_wf (b2 :: bs)⟩

/-- Build a balanced `ByteTree` (up to `2 ^ 24` bytes before linear fallback) from `bs`. -/
def ByteTree.ofList (bs : List (BitVec 8)) : ByteTree :=
  buildTreeLoop 24 1 (initLeaves bs)

theorem ByteTree.get?_ofList (bs : List (BitVec 8)) (i : Nat) :
    (ByteTree.ofList bs).get? i = bs[i]? := by
  obtain ⟨hwf, hlist⟩ := buildTreeLoop_spec 24 1 (initLeaves bs) (initLeaves_wf bs)
  change (buildTreeLoop 24 1 (initLeaves bs)).get? i = bs[i]?
  rw [ByteTree.get?_eq_getElem? hwf, hlist, initLeaves_flatToList]

/-- Pre-indexed `Snapshot.Region` with pre-forced byte length and balanced `ByteTree`. -/
structure FastRegion where
  start      : BitVec 64
  perm       : Perm
  len        : Nat
  nonAnonLen : Nat
  tree       : ByteTree

/-- Convert a `Snapshot.Region` to a `FastRegion`, forcing `len` and `tree` to WHNF once. -/
def FastRegion.ofRegion (r : Snapshot.Region) : FastRegion :=
  let len := r.bytes.length
  let tree := ByteTree.ofList r.bytes
  match len, tree with
  | 0, .empty => { start := r.start, perm := r.perm, len := 0, nonAnonLen := r.nonAnonLen, tree := .empty }
  | 0, .leaf b => { start := r.start, perm := r.perm, len := 0, nonAnonLen := r.nonAnonLen, tree := .leaf b }
  | 0, .linear bs => { start := r.start, perm := r.perm, len := 0, nonAnonLen := r.nonAnonLen, tree := .linear bs }
  | 0, .node s l rt => { start := r.start, perm := r.perm, len := 0, nonAnonLen := r.nonAnonLen, tree := .node s l rt }
  | n + 1, .empty => { start := r.start, perm := r.perm, len := n + 1, nonAnonLen := r.nonAnonLen, tree := .empty }
  | n + 1, .leaf b => { start := r.start, perm := r.perm, len := n + 1, nonAnonLen := r.nonAnonLen, tree := .leaf b }
  | n + 1, .linear bs => { start := r.start, perm := r.perm, len := n + 1, nonAnonLen := r.nonAnonLen, tree := .linear bs }
  | n + 1, .node s l rt => { start := r.start, perm := r.perm, len := n + 1, nonAnonLen := r.nonAnonLen, tree := .node s l rt }

private theorem FastRegion.ofRegion_eq (r : Snapshot.Region) :
    FastRegion.ofRegion r =
      { start := r.start, perm := r.perm, len := r.bytes.length,
        nonAnonLen := r.nonAnonLen, tree := ByteTree.ofList r.bytes } := by
  unfold FastRegion.ofRegion
  dsimp only
  cases r.bytes.length <;> cases ByteTree.ofList r.bytes <;> rfl

def mapFastRegions : List Snapshot.Region → List FastRegion
  | [] => []
  | r :: rs =>
    match FastRegion.ofRegion r, mapFastRegions rs with
    | fr, [] => [fr]
    | fr, fr2 :: frs => fr :: fr2 :: frs

private theorem mapFastRegions_eq :
    ∀ (rs : List Snapshot.Region), mapFastRegions rs = rs.map FastRegion.ofRegion
  | [] => rfl
  | r :: rs => by
    simp only [mapFastRegions, List.map, mapFastRegions_eq rs]
    cases rs.map FastRegion.ofRegion <;> rfl

/-- Fast cell lookup over `List FastRegion`, matching `Snapshot.loadCellAt`. -/
def fastCellAt (frs : List FastRegion) (a : BitVec 64) : Option (Option Perm × BitVec 8) :=
  frs.findSome? fun fr =>
    let i := (a - fr.start).toNat
    if i < fr.len then
      let p := { fr.perm with lazyFree := false, anon := if i < fr.nonAnonLen then false else fr.perm.anon }
      match fr.tree.get? i with
      | some b => some (some p, b)
      | none => none
    else none

private theorem fastCellAt_mapFastRegions (regions : List Snapshot.Region) (a : BitVec 64) :
    fastCellAt (mapFastRegions regions) a = Snapshot.loadCellAt regions a := by
  rw [mapFastRegions_eq]
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    unfold fastCellAt Snapshot.loadCellAt
    rw [List.map_cons, List.findSome?_cons, List.findSome?_cons, FastRegion.ofRegion_eq]
    dsimp only
    let p : Perm :=
      { r.perm with
        lazyFree := false
        anon := if (a - r.start).toNat < r.nonAnonLen then false else r.perm.anon }
    have hhead :
        (if (a - r.start).toNat < r.bytes.length then
          match (ByteTree.ofList r.bytes).get? (a - r.start).toNat with
          | some b => some (some p, b)
          | none => none
        else none) =
        (if h : (a - r.start).toNat < r.bytes.length then
          some (some p, r.bytes[(a - r.start).toNat])
        else none) := by
      split
      · next h =>
        rw [ByteTree.get?_ofList, List.getElem?_eq_getElem h]
      · rfl
    rw [hhead]
    cases (if h : (a - r.start).toNat < r.bytes.length then
        some (some p, r.bytes[(a - r.start).toNat])
      else none) with
    | some _ => rfl
    | none => exact ih

/-- Computable initial-state constructor matching `ElfImage.rawState` with $O(\log N)$ kernel
    byte reads via `ByteTree`. -/
def fastRawState (img : ElfImage) (inputs : ProcessInputs := {}) : State :=
  match buildInitialStack img inputs with
  | .error _ => {}
  | .ok (sp, stackRegion) =>
    let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
    let symtab : String → String → Option (BitVec 64) :=
      fun _ name => (img.symbols.find? (·.1 == name)).map (·.2)
    let mkState (frs : List FastRegion) : State :=
      let baseMem : Memory := ⟨fastCellAt frs⟩
      let mem := baseMem.mapZero stackBase inputs.init.stackSize
      { regs      := RegFile.empty
        vregs     := VRegFile.empty
        sp        := sp
        pc        := img.entry
        pstate    := PState.zero
        mem       := mem
        tpidrEl0  := 0#64
        brkStart  := img.brkStart
        brk       := img.brkStart
        fs        := initFsState inputs
        oracle    := inputs.init.oracle
        oracleIdx := 0
        exclFails := inputs.init.oracle.exclFails
        physMemAvail := inputs.init.physMemAvail
        trace     := []
        status    := .Running
        symtab    := symtab }
    match mapFastRegions (img.segments ++ [stackRegion]) with
    | [] => mkState []
    | fr :: frs => mkState (fr :: frs)

theorem fastRawState_eq_rawState (img : ElfImage) (inputs : ProcessInputs) :
    fastRawState img inputs = img.rawState inputs := by
  unfold fastRawState ElfImage.rawState
  cases buildInitialStack img inputs with
  | error _ => rfl
  | ok pair =>
    rcases pair with ⟨sp, stackRegion⟩
    have hmem : (⟨fastCellAt (mapFastRegions (img.segments ++ [stackRegion]))⟩ : Memory) =
        ⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩ := by
      congr 1
      funext a
      exact fastCellAt_mapFastRegions (img.segments ++ [stackRegion]) a
    cases hm : mapFastRegions (img.segments ++ [stackRegion]) <;>
      simp only [hm] at hmem ⊢ <;>
      simp only [hmem]

end Arm64.Testing.ProcessSemanticsTour
