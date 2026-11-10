/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun
public import LibsignalBinary.Proofs.E2E.HooksE.Common
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import all Init.Data.String.Defs
import all Init.Data.List.SplitOn.Basic
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Run

/-!
# `main` I/O Callee Contracts and `cliIo` Model Facts

Constructs the concrete `IoModel` `cliIo` from `CliRun`'s I/O hooks (`readFileHook`, `writeFileHook`,
`readStdinHook`, `writeStdoutHook`) at `A₀ = E2E.HooksE.A0`, discharges `MainIo` (`mainIo_of_cliHooks`
and `mainIo_of_externsOk`), and proves the `MainIoFacts` obligations (`cliIo_stdin`,
`cliIo_coinsPath`, `cliIo_coins`, and the `commitFiles` ↔ `writeAll` bridge `cliIo_commit`).
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.HooksE.HooksOkAux

/-! ## Generic Hook Plumbing -/

/-- `HookOk f spec` restricted to entry states `s0` satisfying `c x s0`. -/
def HookOkOn {α : Type} (c : α → State → Prop) (f : State → State) (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 : State), c x s0 →
    s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
    s0.mem.KeepsFrozen (f s0).mem ∧ (f s0).symtab = s0.symtab ∧
    SubroutineOutcome spec x R s0 (f s0)

/-- Combines complementary `HookOkOn` halves into `HookOk`. -/
theorem hookOk_of_on {α : Type} {c : α → State → Prop} {f : State → State} {spec : Spec α}
    (h1 : HookOkOn c f spec) (h2 : HookOkOn (fun x s => ¬ c x s) f spec) : HookOk f spec := by
  intro x R s0 hrun hpre hsp
  by_cases hc : c x s0
  · exact h1 x R s0 hc hrun hpre hsp
  · exact h2 x R s0 hc hrun hpre hsp

/-- Decodes path bytes as a Latin-1 `String` key matching `readPath`. -/
def pathStr (p : List (BitVec 8)) : String := String.ofList (p.map fun b => Char.ofNat b.toNat)

theorem readPath_eq_pathStr {m : Memory} {ptr len : BitVec 64} {p : List (BitVec 8)}
    (hlen : len.toNat = p.length) (hrd : m.readBytes ptr p.length = p) :
    readPath m ptr len = pathStr p := by
  unfold readPath pathStr
  rw [hlen, hrd]

theorem traceStreamBytes_append (st : OutputStream) (t1 t2 : List TraceEvent) :
    ProcessOutcome.traceStreamBytes st (t1 ++ t2) =
      ProcessOutcome.traceStreamBytes st t1 ++ ProcessOutcome.traceStreamBytes st t2 := by
  unfold ProcessOutcome.traceStreamBytes
  exact List.filterMap_append

theorem traceStreamBytes_ofBytes_stdout (bs : List (BitVec 8)) :
    ProcessOutcome.traceStreamBytes .stdout (TraceEvent.ofBytes .stdout bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    unfold ProcessOutcome.traceStreamBytes TraceEvent.ofBytes at *
    change b :: List.filterMap _ (List.map _ bs) = b :: bs
    rw [ih]

theorem traceStreamBytes_fileChanged (st : OutputStream) (p : String) :
    ProcessOutcome.traceStreamBytes st [.fileChanged p] = [] := rfl

/-! ## Concrete `IoModel` (`cliIo`) -/

/-- File-map-only counterpart of `blockingAncestor?`. -/
def blockingAncestorF (F : FsFiles) (p : String) : Option (Option FsEntry) :=
  ((ancestors p).find? fun q => match F q with | some .dir => false | _ => true).map F

theorem blockingAncestor?_eq (fs : FsState) (p : String) :
    blockingAncestor? fs p = blockingAncestorF fs.files p := rfl

/-- File-map-only counterpart of `readView`. -/
def readViewF (F : FsFiles) (p : String) : Option (List (BitVec 8)) :=
  match blockingAncestorF F p with
  | some (some _) => none
  | some none => some []
  | none =>
    match F p with
    | some (.file bs) => if bs.length ≤ fileCapBytes then some bs else none
    | some .dir => none
    | none => some []

theorem readView_eq_readViewF (fs : FsState) (p : String) :
    readView fs p = readViewF fs.files p := rfl

def cliRd : ReadRule := fun F path =>
  match readViewF F (pathStr path) with
  | none => .error ()
  | some bs => .ok bs

/-- Write rule of `writeFileHook` on `FsFiles`: returns `none` on a blocking ancestor or directory,
else writes `bs` at `normalizePath (pathStr path)`. -/
def cliWr : WriteRule := fun F path bs =>
  match blockingAncestorF F (pathStr path), F (pathStr path) with
  | some _, _ => none
  | none, some .dir => none
  | none, _ => some fun q =>
      if (normalizePath q).isEmpty then some .dir
      else if normalizePath q = normalizePath (pathStr path) then some (.file bs) else F q

/-- Remaining stdin bytes read by `readStdinHook` when fd 0 is a readable `.stdio` descriptor. -/
def cliStdin (fs : FsState) : Option (List (BitVec 8)) :=
  match fs.fds 0#64 with
  | some e =>
    if e.kind == .stdio && e.accMode.canRead then
      some (fs.stdin.drop e.offset)
    else none
  | none => none

/-- Concrete `IoModel` of `CliRun`'s hooks; `pathOk` requires `PathOk`, ASCII bytes (where Latin-1
`pathStr` agrees with `String.fromUTF8!`), and length `< cliPathMaxBytes`. -/
def cliIo : IoModel where
  rd := cliRd
  wr := cliWr
  stdin := cliStdin
  pathOk path :=
    PathOk (pathStr path) = true ∧
      ((∀ b ∈ path, b.toNat < 128) ∧
        ((pathComps (pathStr path)).all fun c => decide (c.length ≤ NAME_MAX)) = true) ∧
      path.length < cliPathMaxBytes

/-! ## Hook Step Equations -/

theorem writeStdoutHook_eq {s : State} {bs : List (BitVec 8)}
    (hn : (s.readReg64 .x1).toNat = bs.length)
    (hcan : s.mem.canRead (s.readReg64 .x0) bs.length = true)
    (hrd : s.mem.readBytes (s.readReg64 .x0) bs.length = bs) :
    writeStdoutHook s = unitResult true (s.appendTrace (TraceEvent.ofBytes .stdout bs)) := by
  unfold writeStdoutHook
  simp only [hn, hcan, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem writeFileHook_eq {s : State} {path bs : List (BitVec 8)}
    (hlen : (s.readReg64 .x1).toNat = path.length) (hn : (s.readReg64 .x3).toNat = bs.length)
    (hcan : (s.mem.canRead (s.readReg64 .x0) path.length &&
      s.mem.canRead (s.readReg64 .x2) bs.length) = true)
    (hrdp : s.mem.readBytes (s.readReg64 .x0) path.length = path)
    (hrdb : s.mem.readBytes (s.readReg64 .x2) bs.length = bs)
    (hok : PathOk (pathStr path) = true)
    (hlt : path.length < cliPathMaxBytes) :
    writeFileHook s =
      let s1 := s.appendTrace [.fileChanged (pathStr path)]
      match blockingAncestorF s.fs.files (pathStr path), s.fs.files (pathStr path) with
      | some _, _ => unitResult false s1
      | none, some .dir => unitResult false s1
      | none, _ =>
        unitResult true (s1.setFs (s.fs.setFile (pathStr path) (some (.file bs)))) := by
  have hp : readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1) = pathStr path :=
    readPath_eq_pathStr hlen hrdp
  have hle : decide (cliPathMaxBytes ≤ path.length) = false := decide_eq_false (by omega)
  have hcz : path.contains 0#8 = false := contains_zero_eq_false_of_pathOk hok
  unfold writeFileHook
  simp only [hlen, hn, hcan, hrdp, hrdb, hle, hcz, hp, hok, Bool.or_self, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, ProofLib.State.fs_appendTrace,
    ProofLib.State.mem_appendTrace, blockingAncestor?_eq]
  rfl

/-- Characterizes `readStdinHook` as `vecOk` (`≤ stdinCapBytes`) or `vecErr` (`> stdinCapBytes`)
preserving `fs.files`. -/
theorem readStdinHook_eq {s : State} {bs : List (BitVec 8)}
    (hw : s.mem.canWrite (s.readReg64 .x8) 24 = true) (hin : cliStdin s.fs = some bs) :
    ∃ fs' : FsState, fs'.files = s.fs.files ∧
      readStdinHook s =
        (if bs.length ≤ stdinCapBytes then vecOk bs (s.setFs fs') else vecErr (s.setFs fs')) := by
  unfold cliStdin at hin
  unfold readStdinHook
  simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases he : s.fs.fds 0#64 with
  | none => simp [he] at hin
  | some e =>
    simp only [he] at hin ⊢
    by_cases hc : (e.kind == .stdio && e.accMode.canRead) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hin ⊢
      subst hin
      by_cases hcap : (s.fs.stdin.drop e.offset).length ≤ stdinCapBytes <;>
        simp only [hcap, ↓reduceIte] <;> refine ⟨_, ?_, rfl⟩ <;> rfl
    · simp [hc] at hin

/-! ## `vecOk` and `vecErr` against `ioVecAt` -/

/-- `vecErr` writes the `Err` layout (`ioVecAt _ ret (.error ())`) into the 24-byte `sret` slot. -/
theorem vecErr_ok {s : State} {ret : BitVec 64} {F : SepProp}
    (hx8 : s.readReg64 .x8 = ret) (hmem : s.mem ⊨ memRegion ret 24 ∗ F) :
    ∃ m, vecErr s = (s.setMem m).setPC (s.readReg64 .lr) ∧ s.mem.KeepsFrozen m ∧
      (m ⊨ ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (ret + 8#64) 16) ∗ F) := by
  rw [memRegion_split' (N := 24) (n := 8) (k := 16) (b' := ret + 8#64) rfl rfl (by decide),
    ProofLib.memRegion_eight ret] at hmem
  simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨s.mem.write64 ret 0xFFFFFFFFFFFFFFFF#64, ?_, keepsFrozen_write64_of_pointsTo64 _ hw, ?_⟩
  · rw [← hx8]; rfl
  · rw [sepConj_assoc]
    exact satisfies_write64_of_pointsTo64 _ hw

/-- `vecOk bs` writes `Ok(bs)` (`vecU8 A₀ ret bs`) when a bump-allocator block fits nonempty `bs`. -/
theorem vecOk_ok {s : State} {ret : BitVec 64} {F : SepProp} {bs : List (BitVec 8)}
    (hx8 : s.readReg64 .x8 = ret) (hmem : s.mem ⊨ memRegion ret 24 ∗ F)
    (hfit : bs ≠ [] → E2E.bumpAddr? s.mem bs.length 1 ≠ none) :
    ∃ m, vecOk bs s = (s.setMem m).setPC (s.readReg64 .lr) ∧ s.mem.KeepsFrozen m ∧
      (m ⊨ vecU8 E2E.HooksE.A0 ret bs ∗ F) := by
  cases bs with
  | nil =>
    refine ⟨E2E.writeVecHeader s.mem ret 0#64 1#64 0#64, ?_,
      keepsFrozen_writeVecHeader_of_memRegion _ _ _ hmem,
      satisfies_vecU8_empty (by decide) (satisfies_writeVecHeader_of_memRegion _ _ _ hmem)⟩
    rw [← hx8]; rfl
  | cons b bs' =>
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (hfit (List.cons_ne_nil b bs'))
    have hspec := bumpAddr?_spec hp
    have hbase : E2E.heapBase.toNat = 2 ^ 60 := heapBase_toNat
    have hsize : E2E.heapSize = 2 ^ 60 := rfl
    have hlt : (b :: bs').length < 2 ^ 63 := by omega
    obtain ⟨hkf, hm⟩ := vecOutThen_some hlt hp hmem
    refine ⟨_, ?_, hkf, hm⟩
    unfold vecOk E2E.bumpThen
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hp]
    rw [← hx8]; rfl

/-! ## Individual I/O Hook Contracts -/

theorem writeStdoutHook_ok (img : Obj.Image) (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpec img stk) := by
  intro x R s0 hrun hpre _
  simp only [writeStdoutSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1⟩, hmem⟩ := hpre
  obtain ⟨hlen, hrd⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.buf x.bs).canRead hlen hmem
  rw [← hx0] at hrd hcan
  rw [writeStdoutHook_eq hx1 hcan hrd]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeStdoutSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl, List.prefix_append _ _, ?_⟩, hmem⟩
  change ProcessOutcome.traceStreamBytes .stdout (s0.trace ++ TraceEvent.ofBytes .stdout x.bs) = _
  rw [traceStreamBytes_append, traceStreamBytes_ofBytes_stdout]

theorem writeFile_outcome {img : Obj.Image} {stk : Nat} {x : WriteFileGhost} {R : SepProp}
    {s0 : State} {ok : Bool} {fs' : FsState} (hrun : s0.status = .Running)
    (hmem : s0.mem ⊨ (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ R)
    (hpost :
      let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
      match cliIo.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) :
    let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (writeFileSpec cliIo img stk) x R s0 sf := by
  intro sf
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeFileSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpost, List.prefix_append _ _, ?_⟩, hmem⟩
  change ProcessOutcome.traceStreamBytes .stdout (s0.trace ++ [.fileChanged (pathStr x.path)]) = _
  rw [traceStreamBytes_append, traceStreamBytes_fileChanged, List.append_nil]

theorem writeFileHook_ok (img : Obj.Image) (stk : Nat) :
    HookOk writeFileHook (writeFileSpec cliIo img stk) := by
  intro x R s0 hrun hpre _
  simp only [writeFileSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1, hx2, hx3, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemB : s0.mem ⊨ (x.buf ↦ₛ x.bs) ∗ (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ R := by
    rw [sepConj_left_comm]; exact hmem
  obtain ⟨hlenB, hrdB⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmemB
  have hcanB := (IsBlock.pointsToBytes x.buf x.bs).canRead hlenB hmemB
  rw [← hx0] at hrdP hcanP
  rw [← hx2] at hrdB hcanB
  rw [writeFileHook_eq hx1 hx3 (by rw [hcanP, hcanB]; rfl) hrdP hrdB hpok' hpok.2.2]
  simp only
  cases hA : blockingAncestorF s0.fs.files (pathStr x.path) with
  | some a =>
    exact writeFile_outcome hrun hmem (by simp only [cliIo, cliWr, hA]; exact ⟨rfl, rfl⟩)
  | none =>
    cases hB : s0.fs.files (pathStr x.path) with
    | none =>
      exact writeFile_outcome hrun hmem
        (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)
    | some e =>
      cases e with
      | dir =>
        exact writeFile_outcome hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, rfl⟩)
      | file b =>
        exact writeFile_outcome hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)

/-- Entry states where `read_file` hits bump-allocator OOM (nonempty file bytes with `bumpAddr? = none`). -/
def ReadFileOom (x : ReadFileLitGhost) (s0 : State) : Prop :=
  ∃ bs, readView s0.fs (pathStr x.path) = some bs ∧ bs ≠ [] ∧
    E2E.bumpAddr? s0.mem bs.length 1 = none

/-- Entry states where `read_stdin` hits bump-allocator OOM (`0 < |bs| ≤ stdinCapBytes` with `bumpAddr? = none`). -/
def ReadStdinOom (x : ReadStdinGhost) (s0 : State) : Prop :=
  x.bs.length ≤ stdinCapBytes ∧ x.bs ≠ [] ∧ E2E.bumpAddr? s0.mem x.bs.length 1 = none

theorem readFileHook_okOn (img : Obj.Image) (stk : Nat) :
    HookOkOn (fun x s => ¬ ReadFileOom x s) readFileHook
      (readFileLitSpec cliIo E2E.HooksE.A0 img stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readFileLitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  have hlenP : x.path.length ≤ 2 ^ 64 := by omega
  have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
  have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    rw [sepConj_left_comm]; exact hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
  rw [hp] at heq
  have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
      cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
    intro r hr
    show cliRd s0.fs.files x.path = _
    unfold cliRd
    rw [← readView_eq_readViewF, hr]
  cases hv : readView s0.fs (pathStr x.path) with
  | none =>
    rw [hv] at heq
    dsimp only at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileLitSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨rfl, (hrd none hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt, sepConj_assoc] at hm ⊢
    exact hm
  | some bs =>
    rw [hv] at heq
    dsimp only at heq
    have hfit : bs ≠ [] → E2E.bumpAddr? s0.mem bs.length 1 ≠ none :=
      fun hne hnone => hnoom ⟨bs, hv, hne, hnone⟩
    obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok hx8 hmemR hfit
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileLitSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok bs, ⟨rfl, (hrd (some bs) hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm

theorem readStdinHook_okOn (img : Obj.Image) (stk : Nat) :
    HookOkOn (fun x s => ¬ ReadStdinOom x s) readStdinHook
      (readStdinSpec cliIo E2E.HooksE.A0 img stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readStdinSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx8, hin⟩, hmem⟩ := hpre
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
  rw [← hx8] at hcanW
  obtain ⟨fs', hfs', heq⟩ := readStdinHook_eq hcanW hin
  by_cases hcap : x.bs.length ≤ stdinCapBytes
  · simp only [hcap, ↓reduceIte] at heq
    have hfit : x.bs ≠ [] → E2E.bumpAddr? (s0.setFs fs').mem x.bs.length 1 ≠ none :=
      fun hne hnone => hnoom ⟨hcap, hne, hnone⟩
    obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok (s := s0.setFs fs') hx8 hmem hfit
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readStdinSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok x.bs, ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm
  · simp only [hcap, ↓reduceIte] at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok (s := s0.setFs fs') hx8 hmem
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readStdinSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
    simp only [ioVecAt, sepConj_assoc] at hm ⊢
    exact hm

/-- On bump-allocator OOM for nonempty `bs`, `vecOk bs` reduces to `E2E.allocPanicHook`. -/
theorem vecOk_oom {s : State} {bs : List (BitVec 8)} (hne : bs ≠ [])
    (hnone : E2E.bumpAddr? s.mem bs.length 1 = none) : vecOk bs s = E2E.allocPanicHook s := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b bs' =>
    unfold vecOk E2E.bumpThen
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hnone]

theorem readFileHook_okOom (img : Obj.Image) (stk : Nat) :
    HookOkOn ReadFileOom readFileHook (readFileLitSpec cliIo E2E.HooksE.A0 img stk) := by
  intro x R s0 hoom hrun hpre0 hsp
  have hpre := hpre0
  simp only [readFileLitSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  have hlenP : x.path.length ≤ 2 ^ 64 := by omega
  have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
  have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    rw [sepConj_left_comm]; exact hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
  rw [hp] at heq
  obtain ⟨bs, hv, hne, hnone⟩ := hoom
  rw [hv] at heq
  dsimp only at heq
  rw [heq, vecOk_oom hne hnone]
  exact CryptoVerification.E2E.HooksE.HooksOkAux.allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp

theorem readStdinHook_okOom (img : Obj.Image) (stk : Nat) :
    HookOkOn ReadStdinOom readStdinHook (readStdinSpec cliIo E2E.HooksE.A0 img stk) := by
  intro x R s0 ⟨hcap, hne, hnone⟩ _ hpre0 _
  have hpre := hpre0
  simp only [readStdinSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx8, hin⟩, hmem⟩ := hpre
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
  rw [← hx8] at hcanW
  obtain ⟨fs', -, heq⟩ := readStdinHook_eq hcanW hin
  simp only [hcap, ↓reduceIte] at heq
  rw [heq, vecOk_oom (s := s0.setFs fs') hne hnone]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
  simp only [readStdinSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨allocFailedIn_allocPanicHook (s0.setFs fs'), trace_prefix_allocPanicHook (s0.setFs fs')⟩,
    Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpre0⟩

theorem readFileHook_ok (img : Obj.Image) (stk : Nat) :
    HookOk readFileHook (readFileLitSpec cliIo E2E.HooksE.A0 img stk) :=
  hookOk_of_on (readFileHook_okOom img stk) (readFileHook_okOn img stk)

theorem readStdinHook_ok (img : Obj.Image) (stk : Nat) :
    HookOk readStdinHook (readStdinSpec cliIo E2E.HooksE.A0 img stk) :=
  hookOk_of_on (readStdinHook_okOom img stk) (readStdinHook_okOn img stk)

/-! ## `MainIo` Assembly -/

theorem readStdin_fnOff :
    libsignalSessionCode.fnOff mainReadStdinName =
      num% (ls_off% "libsignal_cli_io::read_stdin") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "libsignal_cli_io::read_stdin")

theorem writeFile_fnOff :
    libsignalSessionCode.fnOff mainWriteFileName =
      num% (ls_off% "libsignal_cli_io::write_file") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "libsignal_cli_io::write_file")

theorem writeStdout_fnOff :
    libsignalSessionCode.fnOff mainWriteStdoutName =
      num% (ls_off% "libsignal_cli_io::write_stdout") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "libsignal_cli_io::write_stdout")

theorem readFile_row (W : CliHooks) : (SignalSession.readFileName, readFileHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 10) rfl)

theorem writeFile_row (W : CliHooks) : (writeFileName, writeFileHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 11) rfl)

theorem readStdin_row (W : CliHooks) : (readStdinName, readStdinHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 12) rfl)

theorem writeStdout_row (W : CliHooks) : (writeStdoutName, writeStdoutHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 13) rfl)

/-- Discharges `MainIo` at `A₀` on `cliExterns W` from `CliRun`'s four I/O hooks. -/
theorem mainIo_of_cliHooks (W : CliHooks) (img : Obj.Image) (stk : Nat) :
    MainIo img E2E.HooksE.A0 (cliExterns W) cliIo stk where
  readStdin := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
      (hname := readStdinName) (k := 0) readStdin_fnOff (Nat.add_zero _) (by decide)
      (ls_hook% "libsignal_cli_io::read_stdin") (by simp [Rust.isPanicSymbol, readStdinName])
      ⟨_, cliExterns_row W (readStdin_row W), readStdinHook_ok img stk⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  readFile := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
      (hname := SignalSession.readFileName) (k := 0) readFile_fnOff (Nat.add_zero _) (by decide)
      (ls_hook% "libsignal_cli_io::read_file")
      (by simp [Rust.isPanicSymbol, SignalSession.readFileName])
      ⟨_, cliExterns_row W (readFile_row W), readFileHook_ok img stk⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  writeFile := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
      (hname := writeFileName) (k := 0) writeFile_fnOff (Nat.add_zero _) (by decide)
      (ls_hook% "libsignal_cli_io::write_file") (by simp [Rust.isPanicSymbol, writeFileName])
      ⟨_, cliExterns_row W (writeFile_row W), writeFileHook_ok img stk⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  writeStdout := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
      (hname := writeStdoutName) (k := 0) writeStdout_fnOff (Nat.add_zero _) (by decide)
      (ls_hook% "libsignal_cli_io::write_stdout") (by simp [Rust.isPanicSymbol, writeStdoutName])
      ⟨_, cliExterns_row W (writeStdout_row W), writeStdoutHook_ok img stk⟩
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

/-! ## Initial File-System Facts (`stdin` and `"coins"`) -/

theorem pathStr_utf8_coins : pathStr (utf8 "coins") = "coins" := by decide +kernel

theorem ancestors_coins : ancestors "coins" = [] := by decide +kernel

theorem cliIo_pathOk_coins : cliIo.pathOk (utf8 "coins") := by
  refine ⟨?_, ⟨by decide +kernel, by rw [pathStr_utf8_coins]; decide +kernel⟩, by decide +kernel⟩
  rw [pathStr_utf8_coins]
  decide +kernel

theorem cliIo_stdin_init (i : Inputs) : cliIo.stdin (initFsState (cliInputs i)) = some i.stdin :=
  rfl

theorem cliIo_rd_coins (i : Inputs) :
    ∀ r, cliIo.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
      r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i) := by
  intro r hr
  subst hr
  show cliRd _ _ = _ ∨ (cliRd _ _ = _ ∧ _)
  have hb : blockingAncestorF (initFsState (cliInputs i)).files "coins" = none := by
    unfold blockingAncestorF; rw [ancestors_coins]; rfl
  have hstdioN : normalizePath "coins" ∉ stdioPaths.map normalizePath := by decide
  unfold cliRd readViewF
  rw [pathStr_utf8_coins, hb]
  dsimp only
  have hfs : fsView (initFsState (cliInputs i)) "coins" = filesOf i.files "coins" :=
    congrFun (fsView_initFsState (cliInputs i)) "coins"
  simp only [fsView, hstdioN, ↓reduceIte] at hfs
  unfold coinsOf CoinsReadable
  rw [← hfs]
  cases he : (initFsState (cliInputs i)).files "coins" with
  | none => left; rfl
  | some e =>
    cases e with
    | file bs =>
      by_cases hc : bs.length ≤ fileCapBytes
      · left; simp only [hc, ↓reduceIte]; rfl
      · right; simp only [hc, ↓reduceIte]; exact ⟨by simp, fun h => hc (h.2 bs rfl)⟩
    | dir => right; exact ⟨rfl, fun h => h.1 rfl⟩

/-- Bundles `stdin`, `pathOk "coins"`, and `rd "coins"` for `cliIo` on `initFsState (cliInputs i)`. -/
theorem cliIo_m3_facts (i : Inputs) :
    cliIo.stdin (initFsState (cliInputs i)) = some i.stdin ∧ cliIo.pathOk (utf8 "coins") ∧
      ∀ r, cliIo.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
        r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i) :=
  ⟨cliIo_stdin_init i, cliIo_pathOk_coins, cliIo_rd_coins i⟩

/-! ## `memrchr` Hook Lookup -/

theorem memrchr_row (W : CliHooks) :
    ("core::slice::memchr::memrchr", memrchrHook) ∈ cliHookTable W :=
  List.mem_append_right _ (List.mem_of_getElem? (i := 14) rfl)

theorem cliExterns_memrchr (W : CliHooks) :
    cliExterns W "core::slice::memchr::memrchr" = some memrchrHook :=
  cliExterns_row W (memrchr_row W)

/-! ## Store Commit Bridge (`commitFiles cliWr = writeAll`) -/

theorem utf8EncodeChar_ascii : ∀ n, n < 128 →
    String.utf8EncodeChar (Char.ofNat n) = [n.toUInt8] := by
  decide

theorem flatMap_utf8EncodeChar_ascii (p : List (BitVec 8)) (h : ∀ b ∈ p, b.toNat < 128) :
    (p.map fun b => Char.ofNat b.toNat).flatMap String.utf8EncodeChar =
      p.map fun b => b.toNat.toUInt8 := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    rw [List.map_cons, List.flatMap_cons, List.map_cons,
      utf8EncodeChar_ascii _ (h b (List.mem_cons_self ..)),
      ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]
    rfl

/-- On ASCII byte slices, `String.fromUTF8!` agrees with Latin-1 `pathStr`. -/
theorem fromUTF8!_eq_pathStr (p : List (BitVec 8)) (h : ∀ b ∈ p, b.toNat < 128) :
    String.fromUTF8! ⟨p.toArray.map fun b => b.toNat.toUInt8⟩ = pathStr p := by
  have he : (⟨p.toArray.map fun b => b.toNat.toUInt8⟩ : ByteArray) =
      (p.map fun b => Char.ofNat b.toNat).utf8Encode := by
    rw [List.utf8Encode, flatMap_utf8EncodeChar_ascii p h]
    apply ByteArray.ext
    simp only [List.data_toByteArray, List.map_toArray]
  have hv : ByteArray.IsValidUTF8 ⟨p.toArray.map fun b => b.toNat.toUInt8⟩ :=
    he ▸ ByteArray.isValidUTF8_utf8Encode
  unfold String.fromUTF8!
  split
  next =>
    rw [← String.toByteArray_inj]
    unfold pathStr
    rw [String.toByteArray_ofList, ← he]
    rfl
  next hn => exact absurd hv hn

theorem namedWrites_ascii (ws : List (List (BitVec 8) × List (BitVec 8)))
    (h : ∀ pw ∈ ws, ∀ b ∈ pw.1, b.toNat < 128) :
    namedWrites ws = ws.map fun w => (pathStr w.1, w.2) := by
  unfold namedWrites
  exact List.map_congr_left fun w hw => by rw [fromUTF8!_eq_pathStr w.1 (h w hw)]

theorem slash_not_mem_stdinPath : '/' ∉ "<stdin>".toList := by decide
theorem slash_not_mem_stdoutPath : '/' ∉ "<stdout>".toList := by decide
theorem slash_not_mem_stderrPath : '/' ∉ "<stderr>".toList := by decide

/-- No proper ancestor of a `PathOk` path is `<stdin>`, `<stdout>`, or `<stderr>`. -/
theorem ancestor_not_stdio {p q : String} (hp : PathOk p = true) (hq : q ∈ ancestors p) :
    q ≠ "<stdin>" ∧ q ≠ "<stdout>" ∧ q ≠ "<stderr>" := by
  unfold ancestors at hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  rw [List.mem_range] at hk
  unfold PathOk at hp
  generalize pathComps p = cs at hk hp
  rcases cs with _ | ⟨c0, _ | ⟨c1, cs⟩⟩
  · simp at hk
  · simp at hk
  · rcases k with _ | k
    · have h0 := List.all_eq_true.mp hp c0 (List.mem_cons_self ..)
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h0
      have h1 := h0.2
      simp only [List.take_succ_cons, List.take_zero, List.intercalate_singleton]
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> rw [e] at h1 <;> revert h1 <;>
        decide +kernel
    · have hsl : '/' ∈ (['/'].intercalate ((c0 :: c1 :: cs).take (k + 1 + 1))) := by
        rw [List.take_succ_cons, List.take_succ_cons, List.intercalate_cons_cons]
        simp
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · have := congrArg String.toList e
        rw [String.toList_ofList] at this
        rw [this] at hsl; exact slash_not_mem_stdinPath hsl
      · have := congrArg String.toList e
        rw [String.toList_ofList] at this
        rw [this] at hsl; exact slash_not_mem_stdoutPath hsl
      · have := congrArg String.toList e
        rw [String.toList_ofList] at this
        rw [this] at hsl; exact slash_not_mem_stderrPath hsl

theorem cliWr_ok {F : FsFiles} {path bs : List (BitVec 8)}
    (hb : blockingAncestorF F (pathStr path) = none) (hnd : F (pathStr path) ≠ some .dir) :
    cliWr F path bs = some fun q =>
      if (normalizePath q).isEmpty then some .dir
      else if normalizePath q = normalizePath (pathStr path) then some (.file bs) else F q := by
  unfold cliWr
  rw [hb]
  cases hF : F (pathStr path) with
  | none => rfl
  | some e =>
    cases e with
    | dir => exact absurd hF hnd
    | file b => rfl

private theorem files_congr_norm (fs : FsState) {p q : String}
    (h : normalizePath p = normalizePath q) : fs.files p = fs.files q := by
  rw [files_eq_entries fs p, files_eq_entries fs q, h]

/-- `commitFiles cliWr` agrees with `writeAll` whenever every target path in `ws` is non-directory
and has only directory proper ancestors in `fs`. -/
theorem commitFiles_cliWr :
    ∀ (ws : List (List (BitVec 8) × List (BitVec 8))) (fs : FsState),
    (∀ w ∈ ws, fs.files (pathStr w.1) ≠ some .dir ∧
      ∀ q ∈ ancestors (pathStr w.1), fs.files q = some .dir) →
    commitFiles cliWr fs.files ws =
      some (MainPost.writeAll fs (ws.map fun w => (pathStr w.1, w.2))).files
  | [], fs, _ => rfl
  | (p, bs) :: ws, fs, hw => by
    obtain ⟨hnd, hanc⟩ := hw (p, bs) (List.mem_cons_self ..)
    have hb : blockingAncestorF fs.files (pathStr p) = none := by
      unfold blockingAncestorF
      rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro q hq
      rw [hanc q hq]
      decide
    have hwr : cliWr fs.files p bs = some (fs.setFile (pathStr p) (some (.file bs))).files := by
      rw [cliWr_ok (bs := bs) hb hnd]
      exact congrArg some (funext fun q => (files_setFile fs (pathStr p) (some (.file bs)) q).symm)
    have hstep : commitFiles cliWr fs.files ((p, bs) :: ws) =
        commitFiles cliWr (fs.setFile (pathStr p) (some (.file bs))).files ws := by
      simp only [commitFiles, hwr]
    rw [hstep]
    refine commitFiles_cliWr ws (fs.setFile (pathStr p) (some (.file bs))) fun w hw' => ?_
    obtain ⟨hw_nd, hw_anc⟩ := hw w (List.mem_cons_of_mem _ hw')
    refine ⟨?_, fun q hq => ?_⟩
    · rw [files_setFile]
      cases he : (normalizePath (pathStr w.1)).isEmpty with
      | true =>
        exfalso
        apply hw_nd
        simp only [files_eq_entries, he, ↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · intro h; injection h with h; cases h
        · exact hw_nd
    · rw [files_setFile]
      cases he : (normalizePath q).isEmpty with
      | true => simp only [↓reduceIte]
      | false =>
        have hne : normalizePath q ≠ normalizePath (pathStr p) :=
          fun hn => hnd (files_congr_norm fs hn ▸ hw_anc q hq)
        simp only [Bool.false_eq_true, hne, ↓reduceIte]
        exact hw_anc q hq

/-- `MainIoFacts.commit` specialized to `io := cliIo`. -/
theorem cliIo_commit : ∀ i, CliInputsOk i → ∀ ws : List (List (BitVec 8) × List (BitVec 8)),
    (∀ pw ∈ ws, cliIo.pathOk pw.1) →
    (∀ pw ∈ namedWrites ws, WriteOk i pw.1) →
    commitFiles cliIo.wr (initFsState (cliInputs i)).files ws =
      some (MainPost.writeAll (initFsState (cliInputs i)) (namedWrites ws)).files := by
  intro i _ ws hpath hw
  rw [namedWrites_ascii ws fun pw hpw => (hpath pw hpw).2.1.1] at hw ⊢
  exact commitFiles_cliWr ws _ fun w hw' =>
    let h := hw _ (List.mem_map_of_mem hw'); ⟨h.2.1, h.2.2.1⟩

/-! ## `MainIoFacts` Fields at `cliIo` -/

theorem cliIo_stdin : ∀ i, CliInputsOk i → cliIo.stdin (initFsState (cliInputs i)) = some i.stdin :=
  fun i _ => cliIo_stdin_init i

theorem cliIo_coinsPath : cliIo.pathOk (utf8 "coins") := cliIo_pathOk_coins

theorem cliIo_coins : ∀ i, CliInputsOk i → ∀ r,
    cliIo.rd (initFsState (cliInputs i)).files (utf8 "coins") = r →
    r = .ok (coinsOf i) ∨ (r = .error () ∧ ¬ CoinsReadable i) :=
  fun i _ => cliIo_rd_coins i

/-! ## Parametric `CliExternsOk` Generalizations -/

private theorem stackAt_split_ext_io (sp : BitVec 64) {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

private theorem ext_io_stub_ok {α : Type} {ext : String → Option (State → State)} (img : Obj.Image)
    {name : String} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hnpe : E2E.isImagePanicSymbol name = false)
    (hsat : HookSat ext name spec) :
    subroutine_ok (mProg img (cliExternsWith ext))
      ((mProg img (cliExternsWith ext)).fnAddr name) spec := by
  have hnp : Rust.isPanicSymbol name = false := (Bool.or_eq_false_iff.mp hnpe).1
  have hsat' : HookSat (cliExternsWith ext) name spec := by
    rcases hsat with ⟨f, hf, hh⟩
    exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnpe).trans hf, hh⟩
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnp hsat'
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

/-- `HookSat` for `memrchr` on `cliExternsWith ext` from `CliExternsOk`. -/
theorem cliExternsWith_memrchr {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    HookSat (cliExternsWith ext) "core::slice::memchr::memrchr" CliExt.memrchrSpec := by
  rcases hOk.memrchr with ⟨f, hf, hh⟩
  have hnpe : E2E.isImagePanicSymbol "core::slice::memchr::memrchr" = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol]
  exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnpe).trans hf, hh⟩

/-- Discharges `MainIo` on `cliExternsWith ext` from `CliExternsOk P A ext` for `extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem mainIo_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (stk : Nat := extHookStack)
    (hle : extHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    MainIo img A (cliExternsWith ext) cliIo stk where
  readStdin := by
    rcases hOk.readStdin img with ⟨f, hf, hh⟩
    have hh' : HookOk f (readStdinSpec cliIo A img stk) := by
      intro x R s0 hrun hpre hsp
      have hsplit := stackAt_split_ext_io s0.sp hle hmax
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      have hpre' : s0.mem ⊨ (CliExt.readStdinSpec A img).pre ⟨x.ret, x.bs⟩ s0 ∗ R' := by
        dsimp only [readStdinSpec, CliExt.readStdinSpec, Spec.inImage, R'] at hpre ⊢
        rw [hsplit] at hpre
        ac_nf at hpre ⊢
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.ret, x.bs⟩ R' s0 hrun hpre' hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hs, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [readStdinSpec, CliExt.readStdinSpec, Spec.inImage, R'] at hpost ⊢
        rw [hsplit]
        ac_nf at hpost ⊢
      · refine Or.inr (Or.inl ⟨hs, ?_⟩)
        dsimp only [readStdinSpec, CliExt.readStdinSpec, Spec.inImage, R'] at hpan ⊢
        have hpan' : (f s0).mem ⊨
            (⌜allocFailedIn s0 (f s0) ∧ s0.trace <+: (f s0).trace⌝ ∗
              (anyHeap ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R := by
          ac_nf at hpan ⊢
        exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hpan'
      · dsimp only [CliExt.readStdinSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.readStdinSpec, Spec.inImage] at hoom
        rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim
    exact ext_io_stub_ok img readStdin_fnOff (by decide)
      (ls_hook% "libsignal_cli_io::read_stdin")
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol,
        mainReadStdinName, readStdinName])
      ⟨f, hf, hh'⟩
  readFile := by
    rcases hOk.readFile img with ⟨f, hf, hh⟩
    have hh' : HookOk f (readFileLitSpec cliIo A img stk) := by
      intro x R s0 hrun hpre hsp
      have hsplit := stackAt_split_ext_io s0.sp hle hmax
      have h_bytesAt : CliExt.bytesAt true x.pathA x.path = (x.pathA ↦ᵣ x.path) := rfl
      have h_pathOk : cliIo.pathOk = CliExt.cliPathOk := rfl
      have h_rd : cliIo.rd = CliExt.readFileResult := rfl
      have h_iov : CliExt.ioVecAt = ioVecAt := rfl
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      have hpre' : s0.mem ⊨ (CliExt.readFileSpec A img).pre ⟨x.pathA, true, x.path, x.ret⟩ s0 ∗
          R' := by
        dsimp only [readFileLitSpec, CliExt.readFileSpec, Spec.inImage, R'] at hpre ⊢
        rw [hsplit, h_pathOk] at hpre
        rw [h_bytesAt]
        ac_nf at hpre ⊢
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.pathA, true, x.path, x.ret⟩ R' s0 hrun hpre' hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hs, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [readFileLitSpec, CliExt.readFileSpec, Spec.inImage, R'] at hpost ⊢
        rw [h_bytesAt, ← h_rd, h_iov] at hpost
        rw [hsplit]
        ac_nf at hpost ⊢
      · refine Or.inr (Or.inl ⟨hs, ?_⟩)
        dsimp only [readFileLitSpec, CliExt.readFileSpec, Spec.inImage, R'] at hpan ⊢
        have hpan' : (f s0).mem ⊨
            (⌜allocFailedIn s0 (f s0) ∧ s0.trace <+: (f s0).trace⌝ ∗
              (anyHeap ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R := by
          ac_nf at hpan ⊢
        exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) hpan'
      · dsimp only [CliExt.readFileSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.readFileSpec, Spec.inImage] at hoom
        rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim
    exact ext_io_stub_ok img Cli.readFile_fnOff (by decide)
      (ls_hook% "libsignal_cli_io::read_file")
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, Cli.readFileName])
      ⟨f, hf, hh'⟩
  writeFile := by
    rcases hOk.writeFile img with ⟨f, hf, hh⟩
    have hh' : HookOk f (writeFileSpec cliIo img stk) := by
      intro x R s0 hrun hpre hsp
      have hsplit := stackAt_split_ext_io s0.sp hle hmax
      have h_pathOk : cliIo.pathOk = CliExt.cliPathOk := rfl
      have h_wr : cliIo.wr = CliExt.writeFileResult := rfl
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      have hpre' : s0.mem ⊨ (CliExt.writeFileSpec img).pre ⟨x.pathA, x.path, x.buf, x.bs⟩ s0 ∗
          R' := by
        dsimp only [writeFileSpec, CliExt.writeFileSpec, Spec.inImage, R'] at hpre ⊢
        rw [hsplit, h_pathOk] at hpre
        ac_nf at hpre ⊢
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.pathA, x.path, x.buf, x.bs⟩ R' s0 hrun hpre' hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hex⟩ | ⟨_, _, hex⟩ | ⟨_, hex⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [writeFileSpec, CliExt.writeFileSpec, Spec.inImage, R'] at hpost ⊢
        rw [← h_wr] at hpost
        rw [hsplit]
        ac_nf at hpost ⊢
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
    exact ext_io_stub_ok img writeFile_fnOff (by decide)
      (ls_hook% "libsignal_cli_io::write_file")
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol,
        mainWriteFileName, writeFileName])
      ⟨f, hf, hh'⟩
  writeStdout := by
    rcases hOk.writeStdout img with ⟨f, hf, hh⟩
    have hh' : HookOk f (writeStdoutSpec img stk) := by
      intro x R s0 hrun hpre hsp
      have hsplit := stackAt_split_ext_io s0.sp hle hmax
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      have hpre' : s0.mem ⊨ (CliExt.writeStdoutSpec img).pre ⟨x.buf, x.bs⟩ s0 ∗ R' := by
        dsimp only [writeStdoutSpec, CliExt.writeStdoutSpec, Spec.inImage, R'] at hpre ⊢
        rw [hsplit] at hpre
        ac_nf at hpre ⊢
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.buf, x.bs⟩ R' s0 hrun hpre' hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hex⟩ | ⟨_, _, hex⟩ | ⟨_, hex⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [writeStdoutSpec, CliExt.writeStdoutSpec, Spec.inImage, R'] at hpost ⊢
        rw [hsplit]
        ac_nf at hpost ⊢
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex
        rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
    exact ext_io_stub_ok img writeStdout_fnOff (by decide)
      (ls_hook% "libsignal_cli_io::write_stdout")
      (by simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol,
        mainWriteStdoutName, writeStdoutName])
      ⟨f, hf, hh'⟩

theorem mainIo_of_cliExternsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (stk : Nat := extHookStack)
    (hle : extHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    MainIo img A (cliExternsWith ext) cliIo stk :=
  mainIo_of_externsOk hOk img stk hle hmax

end CryptoVerification.SignalSession.Cli.MainHops
