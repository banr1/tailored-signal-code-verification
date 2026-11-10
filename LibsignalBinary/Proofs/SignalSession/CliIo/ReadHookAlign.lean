/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinProof
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed

/-!
# Semantic and Spatial Alignment of `CliIo` Read Proofs with CLI Contracts

Aligns `CliIo` read postconditions with the `signal-session` CLI contracts:
1. Spatial conversion from `ioResultVecOk` and the `-1#64` error word to `ioVecAt`.
2. Path and VFS alignment (`cPathOf = pathStr`, `0#8 ∉ path` from `cliPathOk`, `FsState.allocFd`
   availability, and equivalence between `classifyOpenRdonly` and `readFileResult`).
3. Postcondition alignment extracting `ioVecAt`, `sf.fs`, and `A.pool` from `cliIoStdinLoopResult`
   and `cliIoReadFileResult`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign

open Arm64 Arm64.Process ProofLib
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At)
open CryptoVerification.SignalSession (
  PathOk blockingAncestor?
)
open CryptoVerification.SignalSession.CliExt (
  pathStr cliPathOk blockingAncestorF readViewF readFileResult stdinBytes ioVecAt
)
open VerifiedLibraries.RustStd (
  RustStdAlloc ioVecBuf ioResultVecOk cPathOf allocSeqPool
)
open LibsignalBinary.Proofs.SignalSession.CliIo.MuslOpenDeterministic (
  OpenRdonlyDetResult classifyOpenRdonly classifyOpenRdonly_err_cases
  classifyOpenRdonly_ok_spec goodComp_of_mem_pathComps intercalate_splitOn
  normalizePath_of_pathOk isEmpty_false_of_pathOk
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  cliIoStdinCap cliIoFileCap cliIoReadCaps cliIoFinalCap
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinLoop (
  cliIoStdinLoopResult
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileLoop (
  cliIoFileLoopResult
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileProof (
  cliIoOpenEntry cliIoReadFileResult
)

/-! ## 1. Spatial Alignment (`ioResultVecOk` ↔ `ioVecAt`) -/

/-- Convert `ioResultVecOk A sret cap ptr bs` into `ioVecAt R_alloc sret (.ok bs)` under any
    live-block entailment `∀ p n al, A.live p n al ⊢ R_alloc.live p n al`. -/
theorem ioResultVecOk_entails_vecU8At {oom : State → State → Prop}
    (A : RustStdAlloc oom) (R_alloc : RustAlloc)
    (hlive : ∀ p n al, A.live p n al ⊢ R_alloc.live p n al)
    (sret cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ioResultVecOk A sret cap ptr bs ⊢ vecU8At R_alloc sret cap ptr bs := by
  unfold ioResultVecOk ioVecBuf vecU8At
  have hvh : VerifiedLibraries.RustStd.vecHeader = CryptoVerification.RustHeap.vecHeader := rfl
  have hz : (0 : BitVec 64) = 0#64 := rfl
  rw [hvh, hz]
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (hlive ptr cap.toNat 1)))

theorem exists_ioResultVecOk_entails_ioVecAt_ok {oom : State → State → Prop}
    (A : RustStdAlloc oom) (R_alloc : RustAlloc)
    (hlive : ∀ p n al, A.live p n al ⊢ R_alloc.live p n al)
    (sret cap : BitVec 64) (bs : List (BitVec 8)) :
    (∃∗ ptr : BitVec 64, ioResultVecOk A sret cap ptr bs) ⊢
      ioVecAt R_alloc sret (.ok bs) := by
  unfold ioVecAt vecU8
  refine Entails.sepExists_elim fun ptr => ?_
  exact Entails.sepExists_right cap
    (Entails.sepExists_right ptr (ioResultVecOk_entails_vecU8At A R_alloc hlive sret cap ptr bs))

theorem ioResultErr_eq_ioVecAt_err (R_alloc : RustAlloc) (sret : BitVec 64) :
    ((sret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sret + 8#64) 16) =
      ioVecAt R_alloc sret (.error ()) :=
  rfl

/-! ## 2. Path, Descriptor, and VFS Classification Alignment -/

theorem cPathOf_eq_pathStr (path : List (BitVec 8)) :
    cPathOf path = pathStr path :=
  rfl

private theorem mem_intercalate_of_mem_ne {x : Char} {sep : Char}
    {xss : List (List Char)} (hm : x ∈ [sep].intercalate xss) (hne : x ≠ sep) :
    ∃ cs ∈ xss, x ∈ cs := by
  induction xss with
  | nil => simp [List.intercalate_nil] at hm
  | cons hd tl ih =>
    cases tl with
    | nil =>
      rw [List.intercalate_singleton] at hm
      exact ⟨hd, List.mem_cons_self .., hm⟩
    | cons hd2 tl2 =>
      rw [List.intercalate_cons_cons] at hm
      rcases List.mem_append.mp hm with hhd | hrest
      · rcases List.mem_append.mp hhd with hhd' | hsep
        · exact ⟨hd, List.mem_cons_self .., hhd'⟩
        · exact absurd (List.mem_singleton.mp hsep) hne
      · obtain ⟨cs, hcs, hx⟩ := ih hrest
        exact ⟨cs, List.mem_cons_of_mem _ hcs, hx⟩

/-- `cliPathOk path` implies both `0#8 ∉ path` and `PathOk (cPathOf path) = true`. -/
theorem zero_not_mem_of_cliPathOk {path : List (BitVec 8)}
    (hp : cliPathOk path) :
    (0#8 : BitVec 8) ∉ path ∧ PathOk (cPathOf path) = true := by
  have hpOk : PathOk (cPathOf path) = true := by rw [cPathOf_eq_pathStr]; exact hp.1
  refine ⟨?_, hpOk⟩
  intro hz
  have hchar : ('\x00' : Char) ∈ (cPathOf path).toList := by
    rw [LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps.toList_cPathOf, List.mem_map]
    exact ⟨0#8, hz, rfl⟩
  rw [← intercalate_splitOn (cPathOf path).toList] at hchar
  obtain ⟨cs, hcs, hx⟩ := mem_intercalate_of_mem_ne hchar (by decide)
  exact (goodComp_of_mem_pathComps hpOk hcs).2.2.2.1 hx

/-- Any closed descriptor slot `fd ∈ [3, FsState.maxOpenFds)` guarantees `fs.allocFd ≠ none`. -/
theorem allocFd_ne_none_of_fds_none {fs : FsState} {fd : BitVec 64}
    (hlo : 3 ≤ fd.toNat) (hhi : fd.toNat < FsState.maxOpenFds) (hnone : fs.fds fd = none) :
    fs.allocFd ≠ none := by
  unfold FsState.allocFd
  have hlt : fd.toNat - 3 < FsState.maxOpenFds - 3 := by omega
  generalize FsState.maxOpenFds - 3 = n at hlt ⊢
  intro hall
  have hall' : List.find? (fun i => fs.fds (BitVec.ofNat 64 (i + 3)) == none) (List.range n) =
      none := Option.map_eq_none_iff.mp hall
  have hmem : fd.toNat - 3 ∈ List.range n := List.mem_range.mpr hlt
  have hpred := List.find?_eq_none.mp hall' (fd.toNat - 3) hmem
  have hfd_eq : BitVec.ofNat 64 (fd.toNat - 3 + 3) = fd := by
    apply BitVec.eq_of_toNat_eq
    have hlt64 : fd.toNat < 2 ^ 64 := fd.isLt
    have : fd.toNat - 3 + 3 = fd.toNat := by omega
    rw [BitVec.toNat_ofNat, this, Nat.mod_eq_of_lt hlt64]
  rw [hfd_eq, hnone] at hpred
  exact hpred rfl

/-- `blockingAncestor? fs p` equals `blockingAncestorF fs.files p`. -/
theorem blockingAncestor_eq_blockingAncestorF (fs : FsState) (p : String) :
    blockingAncestor? fs p = blockingAncestorF fs.files p :=
  rfl

private theorem fileCapBytes_eq_cliIoFileCap :
    CryptoVerification.SignalSession.fileCapBytes = cliIoFileCap :=
  rfl

/-- Exact correspondence between `classifyOpenRdonly fs (cPathOf path)` and
    `readFileResult fs.files path` whenever `fs.allocFd ≠ none`. -/
theorem classifyOpenRdonly_readFileResult {fs : FsState} {path : List (BitVec 8)}
    (halloc : fs.allocFd ≠ none) :
    (∀ bs, readFileResult fs.files path = .ok bs →
      (classifyOpenRdonly fs (cPathOf path) = .err 2 ∧ bs = []) ∨
      (∃ fd, classifyOpenRdonly fs (cPathOf path) = .ok fd .localFile ∧
        fs.files (cPathOf path) = some (.file bs) ∧ bs.length ≤ cliIoFileCap)) ∧
    (readFileResult fs.files path = .error () →
      classifyOpenRdonly fs (cPathOf path) = .err 20 ∨
      (∃ fd, classifyOpenRdonly fs (cPathOf path) = .ok fd .localDir) ∨
      (∃ fd fbs, classifyOpenRdonly fs (cPathOf path) = .ok fd .localFile ∧
        fs.files (cPathOf path) = some (.file fbs) ∧ ¬ fbs.length ≤ cliIoFileCap)) := by
  unfold readFileResult readViewF classifyOpenRdonly
  rw [← cPathOf_eq_pathStr, blockingAncestor_eq_blockingAncestorF, fileCapBytes_eq_cliIoFileCap]
  rcases hfd : fs.allocFd with _ | fd
  · exact absurd hfd halloc
  · constructor
    · intro bs hok
      cases hb : blockingAncestorF fs.files (cPathOf path) with
      | some a =>
        rw [hb] at hok
        cases a with
        | some _ => cases hok
        | none => injection hok with hbs; exact Or.inl ⟨rfl, hbs.symm⟩
      | none =>
        rw [hb] at hok
        cases hf : fs.files (cPathOf path) with
        | some entry =>
          rw [hf] at hok
          cases entry with
          | file fbs =>
            by_cases hcap : fbs.length ≤ cliIoFileCap
            · simp only [hcap, ↓reduceIte] at hok
              injection hok with hbs
              subst hbs
              exact Or.inr ⟨fd, rfl, rfl, hcap⟩
            · simp only [hcap, ↓reduceIte] at hok
              cases hok
          | dir => cases hok
        | none =>
          rw [hf] at hok
          injection hok with hbs
          exact Or.inl ⟨rfl, hbs.symm⟩
    · intro herr
      cases hb : blockingAncestorF fs.files (cPathOf path) with
      | some a =>
        rw [hb] at herr
        cases a with
        | some _ => exact Or.inl rfl
        | none => cases herr
      | none =>
        rw [hb] at herr
        cases hf : fs.files (cPathOf path) with
        | some entry =>
          rw [hf] at herr
          cases entry with
          | file fbs =>
            by_cases hcap : fbs.length ≤ cliIoFileCap
            · simp only [hcap, ↓reduceIte] at herr
              cases herr
            · exact Or.inr (Or.inr ⟨fd, fbs, rfl, rfl, hcap⟩)
          | dir => exact Or.inr (Or.inl ⟨fd, rfl⟩)
        | none => rw [hf] at herr; cases herr

/-! ## 3. Postcondition Alignment (`cliIoStdinLoopResult` & `cliIoReadFileResult` → `ioVecAt`) -/

private theorem fdKind_beq_stdio_iff (k : FdKind) : (k == .stdio) = true ↔ k = .stdio := by
  cases k <;> constructor <;> intro h <;> cases h <;> rfl

theorem stdinBytes_eq_some_iff {fs : FsState} {bs : List (BitVec 8)} :
    stdinBytes fs = some bs ↔
      ∃ d0 : FdEntry, fs.fds 0#64 = some d0 ∧ d0.kind = .stdio ∧
        d0.accMode.canRead = true ∧ fs.stdin.drop d0.offset = bs := by
  unfold stdinBytes
  cases hf : fs.fds 0#64 with
  | none => simp
  | some d0 =>
    simp only [Bool.and_eq_true, fdKind_beq_stdio_iff]
    constructor
    · intro h
      split at h
      · rename_i hc
        injection h with hbs
        exact ⟨d0, rfl, hc.1, hc.2, hbs⟩
      · cases h
    · rintro ⟨d0', hd0', hk, hr, hbs⟩
      injection hd0' with heq
      subst heq
      simp [hk, hr, hbs]

theorem cliIoStdinLoopResult_entails_ok {oom : State → State → Prop}
    (A : RustStdAlloc oom) (R_alloc : RustAlloc)
    (hlive : ∀ p n al, A.live p n al ⊢ R_alloc.live p n al)
    (sret : BitVec 64) (d0 : FdEntry) (lb lk : Nat) (s0 sf : State)
    {bs : List (BitVec 8)} (hbs : s0.fs.stdin.drop d0.offset = bs)
    (hcap : bs.length ≤ cliIoStdinCap) :
    cliIoStdinLoopResult A sret d0 lb lk s0 sf ⊢
      ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + bs.length }) ∧
        sf.fs.files = s0.fs.files⌝ ∗
        ioVecAt R_alloc sret (.ok bs) ∗
        A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 8 bs.length)).1
          (allocSeqPool A 1 lb lk (cliIoReadCaps 8 bs.length)).2 sf := by
  unfold cliIoStdinLoopResult
  dsimp only []
  rw [hbs]
  simp only [hcap, ↓reduceIte]
  refine Entails.pure_left fun hfs => ?_
  have hfiles : sf.fs.files = s0.fs.files := by rw [hfs]; rfl
  refine Entails.pure_right ⟨hfs, hfiles⟩ ?_
  exact sepConj_mono_left (exists_ioResultVecOk_entails_ioVecAt_ok A R_alloc hlive sret _ bs)

theorem cliIoStdinLoopResult_entails_overCap {oom : State → State → Prop}
    (A : RustStdAlloc oom) (R_alloc : RustAlloc)
    (sret : BitVec 64) (d0 : FdEntry) (lb lk : Nat) (s0 sf : State)
    {bs : List (BitVec 8)} (hbs : s0.fs.stdin.drop d0.offset = bs)
    (hover : cliIoStdinCap < bs.length) :
    cliIoStdinLoopResult A sret d0 lb lk s0 sf ⊢
      ⌜sf.fs = s0.fs.setFd 0#64 (some { d0 with offset := d0.offset + (cliIoStdinCap + 1) }) ∧
        sf.fs.files = s0.fs.files⌝ ∗
        ioVecAt R_alloc sret (.error ()) ∗
        A.pool lb lk sf := by
  have hncap : ¬ bs.length ≤ cliIoStdinCap := Nat.not_le_of_gt hover
  unfold cliIoStdinLoopResult
  dsimp only []
  rw [hbs]
  simp only [hncap, ↓reduceIte]
  refine Entails.pure_left fun hfs => ?_
  have hfiles : sf.fs.files = s0.fs.files := by rw [hfs]; rfl
  rw [ioResultErr_eq_ioVecAt_err R_alloc sret]
  exact Entails.pure_right ⟨hfs, hfiles⟩ (Entails.refl _)

/-- Cap-aware outcome of `signal_session_io::read_file`: rejects `4096 ≤ path.length`,
    `0#8 ∈ path`, directory/blocking-ancestor errors, and files exceeding `cliIoFileCap` (`2^21`). -/
def cliIoReadFileExpected (files : String → Option FsEntry) (path : List (BitVec 8)) :
    Except Unit (List (BitVec 8)) :=
  if 4096 ≤ path.length ∨ 0#8 ∈ path then .error ()
  else
    match readFileResult files path with
    | .ok bs => if bs.length ≤ cliIoFileCap then .ok bs else .error ()
    | .error () => .error ()

/-- Postcondition alignment for `cliIoReadFileResult`: whenever `s0.fs.allocFd ≠ none`,
    `cliIoReadFileResult` yields `sf.fs = s0.fs`, `ioVecAt R_alloc sret (cliIoReadFileExpected ...)`,
    and the updated pool state (`allocSeqPool` on `Ok(bs)` with `bs ≠ []`, or `(lb, lk)` on empty/error). -/
theorem cliIoReadFileResult_entails_ioVecAt {oom : State → State → Prop}
    (A : RustStdAlloc oom) (R_alloc : RustAlloc)
    (hlive : ∀ p n al, A.live p n al ⊢ R_alloc.live p n al)
    (sret : BitVec 64) (path : List (BitVec 8)) (lb lk : Nat) (s0 sf : State)
    (halloc : s0.fs.allocFd ≠ none) :
    cliIoReadFileResult A sret path lb lk s0 sf ⊢
      ⌜sf.fs = s0.fs⌝ ∗
        ioVecAt R_alloc sret (cliIoReadFileExpected s0.fs.files path) ∗
        (match cliIoReadFileExpected s0.fs.files path with
         | .ok bs =>
           A.pool (allocSeqPool A 1 lb lk (cliIoReadCaps 9 bs.length)).1
             (allocSeqPool A 1 lb lk (cliIoReadCaps 9 bs.length)).2 sf
         | .error () => A.pool lb lk sf) := by
  unfold cliIoReadFileResult cliIoReadFileExpected
  by_cases hbad : 4096 ≤ path.length ∨ 0#8 ∈ path
  · simp only [hbad, ↓reduceIte, ioResultErr_eq_ioVecAt_err R_alloc sret]
    exact Entails.refl _
  · simp only [hbad, ↓reduceIte]
    have hcorr := classifyOpenRdonly_readFileResult (path := path) halloc
    cases hr : readFileResult s0.fs.files path with
    | error u =>
      cases u
      rcases hcorr.2 hr with herr20 | ⟨fd, hdir⟩ | ⟨fd, fbs, hfile, hfbs, hncap⟩
      · rw [herr20, ioResultErr_eq_ioVecAt_err R_alloc sret]
        exact Entails.refl _
      · rw [hdir, ioResultErr_eq_ioVecAt_err R_alloc sret]
        exact Entails.refl _
      · rw [hfile]
        unfold cliIoFileLoopResult
        dsimp only [cliIoOpenEntry]
        rw [LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps.fdBytes_open_localFile hfbs,
          List.drop_zero]
        simp only [hncap, ↓reduceIte, ioResultErr_eq_ioVecAt_err R_alloc sret]
        exact Entails.refl _
    | ok bs =>
      rcases hcorr.1 bs hr with ⟨herr2, rfl⟩ | ⟨fd, hfile, hfbs, hcap⟩
      · have hle0 : ([] : List (BitVec 8)).length ≤ cliIoFileCap := Nat.zero_le _
        rw [herr2]
        simp only [hle0, ↓reduceIte]
        have hcaps0 : cliIoReadCaps 9 ([] : List (BitVec 8)).length = [] := by
          simp [cliIoReadCaps]
        rw [hcaps0]
        dsimp only [allocSeqPool]
        exact sepConj_mono_right (sepConj_mono_left
          (exists_ioResultVecOk_entails_ioVecAt_ok A R_alloc hlive sret 0#64 []))
      · rw [hfile]
        unfold cliIoFileLoopResult
        dsimp only [cliIoOpenEntry]
        rw [LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileOpenSteps.fdBytes_open_localFile hfbs,
          List.drop_zero]
        simp only [hcap, ↓reduceIte]
        exact sepConj_mono_right (sepConj_mono_left
          (exists_ioResultVecOk_entails_ioVecAt_ok A R_alloc hlive sret _ bs))

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadHookAlign
