/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
import GeneratedLean.LibsignalSessionCode -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `signal_session_io::read_file`: Hook and Callee Contracts

Establishes `readFileSpec` for `signal_session_io::read_file` both from the concrete `readFileHook`
at `E2E.HooksE.A0` and `cliExterns W` (`cliReadFile_ok`, splitting on out-of-memory allocation
panic `CliReadFileOom` versus normal return) and from the contract-backed `CliExternsOk.readFile`
interface (`runCallees_readFile_of_externsOk`).
-/

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.E2E.HooksE.HooksOkAux

/-- Out-of-memory condition for `read_file`: `readView` returns non-empty bytes that do not fit in
bump memory (`vecOk` panics via `allocPanicHook`). -/
def CliReadFileOom (x : ReadFileGhost) (s0 : State) : Prop :=
  ∃ bs, readView s0.fs (pathStr x.path) = some bs ∧ bs ≠ [] ∧
    E2E.bumpAddr? s0.mem bs.length 1 = none

theorem cliReadFileHook_okOn (img : Obj.Image) (stk : Nat) :
    HookOkOn (fun x s => ¬ CliReadFileOom x s) readFileHook
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readFileSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1, hx8, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.1.2.2)
  rw [hp] at heq
  have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
      cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
    intro r hr
    show cliRd s0.fs.files x.path = _
    unfold cliRd
    rw [← readView_eq_readViewF, hr]
    rfl
  cases hv : readView s0.fs (pathStr x.path) with
  | none =>
    rw [hv] at heq
    dsimp only at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨(hrd none hv).symm, rfl⟩, ?_⟩
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
    simp only [readFileSpec, Spec.inImage, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok bs, ⟨(hrd (some bs) hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm

theorem cliReadFileHook_okOom (img : Obj.Image) (stk : Nat) :
    HookOkOn CliReadFileOom readFileHook
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) := by
  intro x R s0 hoom hrun hpre0 hsp
  have hpre := hpre0
  simp only [readFileSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨-, ⟨hx0, hx1, hx8, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.1.2.2)
  rw [hp] at heq
  obtain ⟨bs, hv, hne, hnone⟩ := hoom
  rw [hv] at heq
  dsimp only at heq
  rw [heq, vecOk_oom hne hnone]
  exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp

/-- `readFileHook` satisfies `readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk` at every stack budget `stk`. -/
theorem cliReadFileHook_ok (img : Obj.Image) (stk : Nat) :
    HookOk readFileHook (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) :=
  hookOk_of_on (cliReadFileHook_okOom img stk) (cliReadFileHook_okOn img stk)

theorem cliReadFile_hookSat (W : CliHooks) (img : Obj.Image) (stk : Nat) :
    HookSat (cliExterns W) Cli.readFileName
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) :=
  ⟨readFileHook, cliExterns_row W (readFile_row W), cliReadFileHook_ok img stk⟩

/-- `signal_session_io::read_file` satisfies `readFileSpec` on
`tripleRatchetProgAtExt img.base (cliExterns W)` at every stack budget `stk`. -/
theorem cliReadFile_ok (W : CliHooks) (img : Obj.Image) (stk : Nat) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img stk) := by
  have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExterns W)
    (hname := SignalSession.readFileName) (k := 0) Cli.readFile_fnOff (Nat.add_zero _) (by decide)
    (ls_hook% "libsignal_cli_io::read_file")
    (by simp [Rust.isPanicSymbol, SignalSession.readFileName])
    (cliReadFile_hookSat W img stk)
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

theorem runCallees_readFile_of_cliHooks (W : CliHooks) (img : Obj.Image)
    (_himg : Obj.Loads libsignalSessionImage img) (B : RunBudgets) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile) :=
  cliReadFile_ok W img B.readFile

example (W : CliHooks) (img : Obj.Image) (_himg : Obj.Loads libsignalSessionImage img)
    (B : RunBudgets) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk E2E.HooksE.A0 img B.readFile) :=
  cliReadFile_ok W img B.readFile

/-! ## Contract-backed `read_file` (`CliExternsOk.readFile`) -/

private theorem stackAt_le_two_pow_64_of_sep {m : Memory} {p sp : BitVec 64} {n stk : Nat}
    {R : SepProp} (hn : 0 < n) (hstk : 0 < stk)
    (h : m ⊨ memRegion p n ∗ (stackAt sp stk ∗ R)) : stk ≤ 2 ^ 64 := by
  have hdisj := (IsBlock.memRegion p n).disjoint
    (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk) hn hstk h
  have hlt := (p - (sp - BitVec.ofNat 64 stk)).isLt
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt hdisj.2 hlt)

private theorem hookOk_map_frame {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (hh : HookOk f s₁)
    (hmap : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R →
      ∃ x F, s0.mem ⊨ s₁.pre x s0 ∗ (F ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.post x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.post y s0 sf ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.onPanic x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R) ∧
        (∀ c sf, sf.mem ⊨ s₁.onExit x c s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R) ∧
        (∀ sf, sf.mem ⊨ s₁.onOom x s0 sf ∗ (F ∗ R) → sf.mem ⊨ s₂.onOom y s0 sf ∗ R)) :
    HookOk f s₂ := by
  intro y R s0 hrun hp hsp
  obtain ⟨x, F, hp₁, hpost, hpanic, hexit, hoom⟩ := hmap y R s0 hp
  obtain ⟨hkf, hsym, hout⟩ := hh x (F ∗ R) s0 hrun hp₁ hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hs, hq⟩ | ⟨c, hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hr, hc, hpost (f s0) hq⟩
  · exact Or.inr (Or.inl ⟨hs, hpanic (f s0) hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hs, hexit c (f s0) hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hs, hoom (f s0) hq⟩))

private theorem ioVecAt_eq_cli (A : RustAlloc) (r : BitVec 64)
    (res : Except Unit (List (BitVec 8))) :
    CliExt.ioVecAt A r res = Cli.ioVecAt A r res := by
  cases res <;> rfl

/-- Adapts `HookOk f (CliExt.readFileSpec A img)` to `readFileSpec cliIo.rd cliWrOk A img stk` for
any `stk ≥ extHookStack`. -/
theorem hookOk_cliReadFileSpec_of_ext {A : RustAlloc} {img : Obj.Image} {stk : Nat}
    {f : State → State} (hstk : extHookStack ≤ stk)
    (hf : HookOk f (CliExt.readFileSpec A img)) :
    HookOk f (readFileSpec cliIo.rd cliWrOk A img stk) := by
  refine hookOk_map_frame hf fun x R s0 hpre => ?_
  simp only [readFileSpec, Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨himg, ⟨hx0, hx1, hx8, hlen, hpok⟩, hmem⟩ := hpre
  have hmem_disj : s0.mem ⊨ memRegion x.ret 24 ∗
      (stackAt s0.sp stk ∗ ((x.pathA ↦ₛ x.path) ∗ A.pool ∗ R)) := by
    ac_nf at hmem ⊢
  have hstk64 : stk ≤ 2 ^ 64 :=
    stackAt_le_two_pow_64_of_sep (by decide)
      (Nat.lt_of_lt_of_le (by decide : 0 < extHookStack) hstk) hmem_disj
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt s0.sp extHookStack := by
    have hs := stackAt_split_bottom s0.sp extHookStack (stk - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstk] at hs
  refine ⟨⟨x.pathA, false, x.path, x.ret⟩,
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [CliExt.readFileSpec, Spec.inImage, CliExt.bytesAt, Bool.false_eq_true, ↓reduceIte,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg, ⟨hx0, hx1, hx8, hlen, hpok.1⟩, ?_⟩
    rw [hsplit] at hmem
    ac_nf at hmem ⊢
  · intro sf hq
    simp only [CliExt.readFileSpec, readFileSpec, Spec.inImage, CliExt.bytesAt,
      Bool.false_eq_true, ↓reduceIte, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨res, ⟨_, hres, htr⟩, hqmem⟩ := hq
    rw [ioVecAt_eq_cli] at hqmem
    refine ⟨res, ⟨hres, htr⟩, ?_⟩
    rw [hsplit]
    ac_nf at hqmem ⊢
  · intro sf hq
    simp only [CliExt.readFileSpec, readFileSpec, Spec.inImage] at hq ⊢
    exact satisfies_allowPanicWhen_frame id hq
  · intro _ _ hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · intro _ hq
    exact False.elim (not_satisfies_false_sepConj hq)

theorem cliReadFile_hookSat_of_hookSat {A : RustAlloc} {ext : String → Option (State → State)}
    {img : Obj.Image} {stk : Nat} (hstk : extHookStack ≤ stk := by decide)
    (h : HookSat ext Cli.readFileName (CliExt.readFileSpec A img)) :
    HookSat ext Cli.readFileName (readFileSpec cliIo.rd cliWrOk A img stk) := by
  obtain ⟨f, hf, hok⟩ := h
  exact ⟨f, hf, hookOk_cliReadFileSpec_of_ext hstk hok⟩

theorem cliReadFile_ok_of_hookSat {A : RustAlloc} {ext : String → Option (State → State)}
    (img : Obj.Image) {stk : Nat} (hstk : extHookStack ≤ stk := by decide)
    (h : HookSat ext Cli.readFileName (CliExt.readFileSpec A img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img stk) := by
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
    (hname := SignalSession.readFileName) (k := 0) Cli.readFile_fnOff (Nat.add_zero _) (by decide)
    (ls_hook% "libsignal_cli_io::read_file")
    (by simp [Rust.isPanicSymbol, SignalSession.readFileName])
    (cliReadFile_hookSat_of_hookSat hstk h)
  simpa only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

theorem cliReadFile_hookSat_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) {stk : Nat} (hstk : extHookStack ≤ stk := by decide) :
    HookSat ext Cli.readFileName (readFileSpec cliIo.rd cliWrOk A img stk) :=
  cliReadFile_hookSat_of_hookSat hstk (hOk.readFile img)

theorem cliReadFile_hookSat_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) {stk : Nat} (hstk : extHookStack ≤ stk := by decide) :
    HookSat (cliExternsWith ext) Cli.readFileName
      (readFileSpec cliIo.rd cliWrOk A img stk) := by
  obtain ⟨f, hf, hok⟩ := cliReadFile_hookSat_ext hOk img hstk
  have hnp : E2E.isImagePanicSymbol Cli.readFileName = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, Cli.readFileName]
  exact ⟨f, (withCliPanics_of_isImagePanicSymbol_false ext hnp).trans hf, hok⟩

theorem cliReadFile_ok_ext {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) {stk : Nat} (hstk : extHookStack ≤ stk := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img stk) :=
  cliReadFile_ok_of_hookSat img hstk (hOk.readFile img)

/-- Contract-backed `subroutine_ok` for `signal_session_io::read_file` on `cliExternsWith ext` for
`stk ≥ extHookStack`. -/
theorem cliReadFile_ok_cliExternsWith {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) {stk : Nat} (hstk : extHookStack ≤ stk := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img stk) := by
  obtain ⟨f, hf, hok⟩ := hOk.readFile img
  have hnp : E2E.isImagePanicSymbol Cli.readFileName = false := by
    simp [E2E.isImagePanicSymbol, E2E.extraImagePanicNames, Rust.isPanicSymbol, Cli.readFileName]
  exact cliReadFile_ok_of_hookSat img hstk
    ⟨f, by
      rw [cliExternsWith, withCliPanics_of_isImagePanicSymbol_false _ hnp]
      simpa [SignalSession.readFileName, Cli.readFileName] using hf, hok⟩

/-- Discharges `RunCallees.readFile` on `cliExternsWith ext` from `CliExternsOk P A ext` when
`extHookStack ≤ B.readFile`. -/
theorem runCallees_readFile_of_externsOk {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) (B : RunBudgets)
    (hB : extHookStack ≤ B.readFile := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) :=
  cliReadFile_ok_cliExternsWith hOk img hB

theorem runCallees_readFile_of_ok {P : E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext)
    (img : Obj.Image) (B : RunBudgets)
    (hB : extHookStack ≤ B.readFile := by decide) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Cli.readFileName)
      (readFileSpec cliIo.rd cliWrOk A img B.readFile) :=
  runCallees_readFile_of_externsOk hOk img B hB

end CryptoVerification.SignalSession.Cli.RunSkeleton
