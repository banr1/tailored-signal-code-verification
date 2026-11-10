/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import ProofLib.Hoare.MultiCodeROHook
public import VerifiedLibraries.Mallocng.Spec
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Filesystem Trace Soundness (`TraceFsSound`) at `cliExternsPlaced` and `cliGhostExterns`

Proves `HookFsTraced IsFsC` for every row of `cliHookTablePlaced mmpl W` and `CliGhostHooksFs`,
deriving `TraceFsSound` on `MultiPlacedLib.blockProgram`, `mProgPlaced`, and `cliProgPlaced` under
both `cliExternsPlaced mmpl W` and `cliGhostExterns g (cliExternsPlaced mmpl W)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunGlue

open Arm64 ProofLib
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState)
open CryptoVerification
open CryptoVerification.E2E (
  aesDecHookMallocng aesDecOut aesEncHookMallocng libcruxHmacHookMallocng
  stepRustAlloc1 stepRustDealloc1
)
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli

set_option linter.unusedSimpArgs false

/-- `Obj.MultiPlacedLib.codeROSubroutineHook` with `externs = none`, `overrides = none`, and
    `svc = Syscall.standard` is `HookFsTraced IsFsC`. -/
theorem codeROSubroutineHook_fsT (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (fnName : String) :
    HookFsTraced IsFsC
      (lib.codeROSubroutineHook mpl fnName (fun _ => none) (fun _ => none) Syscall.standard) := by
  classical
  intro s0
  unfold Obj.MultiPlacedLib.codeROSubroutineHook
  cases Obj.lookupBlockSym fnName lib.blocks with
  | none => exact FsTraced.refl s0
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    split
    · rename_i h
      let prog := lib.blockProgram mpl i (fun _ => none) (fun _ => none) Syscall.standard
      let s0' := multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0
      have h0 : FsTraced IsFsC s0 s0' := by
        dsimp only [s0', multiCodeROHookEntry]
        exact FsTraced.of_eq rfl rfl
      have hsteps : Steps prog s0' (Classical.choose h) := (Classical.choose_spec h).1.toSteps
      have hno : ∀ pc f, prog.externAt? pc = some f → HookFsTraced IsFsC f := by
        intro pc f he
        exact fsT_externAt (P := prog)
          (fun _ _ hg => by
            dsimp only [prog, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program] at hg
            exact nomatch hg)
          (fun _ _ hg => by
            dsimp only [prog, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program] at hg
            exact nomatch hg)
          he
      have htr : FsTraced IsFsC s0' (Classical.choose h) :=
        hsteps.fsTraced (isFs := IsFsC) (fun _ he => he) hno rfl
      have hexit : FsTraced IsFsC (Classical.choose h)
          (multiCodeROHookExit lib mpl i s0 (Classical.choose h)) := by
        unfold multiCodeROHookExit
        dsimp only
        split <;> exact FsTraced.of_eq rfl rfl
      exact (h0.trans htr).trans hexit
    · exact FsTraced.refl s0

theorem stepRustAlloc1_fsT (mpl : Obj.MultiPlacement) (zeroed : Bool) (frameBytes size : Nat)
    {k : State → BitVec 64 → State}
    (hk : ∀ t p, FsTraced IsFsC t (k t p)) :
    HookFsTraced IsFsC (stepRustAlloc1 mpl zeroed frameBytes size k) := by
  intro s
  cases zeroed with
  | false =>
    unfold stepRustAlloc1
    simp only [Bool.false_eq_true, ↓reduceIte]
    let spCall := s.sp - BitVec.ofNat 64 frameBytes
    let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
    have hsCall : FsTraced IsFsC s sCall := FsTraced.of_eq rfl rfl
    have hs1 : FsTraced IsFsC sCall
        (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "malloc"
          (fun _ => none) (fun _ => none) Syscall.standard sCall) :=
      codeROSubroutineHook_fsT VerifiedLibraries.mallocngLib mpl "malloc" sCall
    have hs01 := hsCall.trans hs1
    split
    · exact hs01
    · split
      · exact hs01.trans ((FsTraced.of_eq rfl rfl).trans (panicked_fsT _))
      · exact hs01.trans ((FsTraced.of_eq rfl rfl).trans (hk _ _))
  | true =>
    unfold stepRustAlloc1
    simp only [↓reduceIte]
    let spCall := s.sp - BitVec.ofNat 64 frameBytes
    let sCall :=
      ((s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)).writeReg64 .x1 1#64
    have hsCall : FsTraced IsFsC s sCall := FsTraced.of_eq rfl rfl
    have hs1 : FsTraced IsFsC sCall
        (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "calloc"
          (fun _ => none) (fun _ => none) Syscall.standard sCall) :=
      codeROSubroutineHook_fsT VerifiedLibraries.mallocngLib mpl "calloc" sCall
    have hs01 := hsCall.trans hs1
    split
    · exact hs01
    · split
      · exact hs01.trans ((FsTraced.of_eq rfl rfl).trans (panicked_fsT _))
      · exact hs01.trans ((FsTraced.of_eq rfl rfl).trans (hk _ _))

theorem stepRustDealloc1_fsT (mpl : Obj.MultiPlacement) (frameBytes : Nat) (ptr : BitVec 64)
    {k : State → State}
    (hk : ∀ t, FsTraced IsFsC t (k t)) :
    HookFsTraced IsFsC (stepRustDealloc1 mpl frameBytes ptr k) := by
  intro s
  unfold stepRustDealloc1
  dsimp only
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  have hsCall : FsTraced IsFsC s sCall := FsTraced.of_eq rfl rfl
  have hs1 : FsTraced IsFsC sCall
      (VerifiedLibraries.mallocngLib.codeROSubroutineHook mpl "free"
        (fun _ => none) (fun _ => none) Syscall.standard sCall) :=
    codeROSubroutineHook_fsT VerifiedLibraries.mallocngLib mpl "free" sCall
  have hs01 := hsCall.trans hs1
  split
  · exact hs01
  · exact hs01.trans ((FsTraced.of_eq rfl rfl).trans (hk _))

/-- `HookFsTraced IsFsC` for `aesEncHookMallocng mpl E`. -/
theorem aesEncHookMallocng_fsT (mpl : Obj.MultiPlacement) (E : AesKey → Block → Block) :
    HookFsTraced IsFsC (aesEncHookMallocng mpl E) := by
  intro s0
  unfold aesEncHookMallocng
  split
  · exact FsTraced.of_eq rfl rfl
  · dsimp only
    split
    · exact panicked_fsT s0
    · apply stepRustAlloc1_fsT
      intro _ _
      exact FsTraced.of_eq rfl rfl

/-- `HookFsTraced IsFsC` for `aesDecHookMallocng mpl D`. -/
theorem aesDecHookMallocng_fsT (mpl : Obj.MultiPlacement) (D : AesKey → Block → Block) :
    HookFsTraced IsFsC (aesDecHookMallocng mpl D) := by
  intro s0
  unfold aesDecHookMallocng
  split
  · exact FsTraced.of_eq rfl rfl
  · dsimp only
    split
    · exact FsTraced.of_eq rfl rfl
    · apply stepRustAlloc1_fsT
      intro s1 _
      cases haes : aesDecOut D s1 with
      | some _ => simp only []; exact FsTraced.of_eq rfl rfl
      | none =>
        simp only []
        apply stepRustDealloc1_fsT
        intro _
        exact FsTraced.of_eq rfl rfl

/-- `HookFsTraced IsFsC` for `libcruxHmacHookMallocng mpl F`. -/
theorem libcruxHmacHookMallocng_fsT (mpl : Obj.MultiPlacement)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookFsTraced IsFsC (libcruxHmacHookMallocng mpl F) := by
  intro s0
  unfold libcruxHmacHookMallocng
  split
  · exact FsTraced.of_eq rfl rfl
  · dsimp only
    split
    · exact panicked_fsT s0
    · apply stepRustAlloc1_fsT; intro _ _
      apply stepRustAlloc1_fsT; intro _ _
      apply stepRustAlloc1_fsT; intro _ _
      apply stepRustDealloc1_fsT; intro _
      apply stepRustDealloc1_fsT; intro _
      apply stepRustDealloc1_fsT; intro _
      apply stepRustAlloc1_fsT; intro _ _
      exact FsTraced.of_eq rfl rfl

/-- Every row of the `37`-row `cliHookTablePlaced mmpl W` satisfies `HookFsTraced IsFsC`. -/
theorem cliHookTablePlaced_fsT (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, HookFsTraced IsFsC p.2 := by
  simp only [cliHookTablePlaced, cliPqxdhHookTablePlaced, List.cons_append,
    List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, compress512Hook_fsT, toEdwardsHook_fsT, compressHook_fsT, edNegHook_fsT,
    torsionFreeHook_fsT, dsmbHook_fsT, scalarModHook_fsT, scalarWideHook_fsT,
    kemEncapsHook_fsT, kemDecapsHook_fsT, mlkemFromSeedHook_fsT, mlkemPk1Hook_fsT,
    mlkemPk2Hook_fsT, mlkemEncaps1Hook_fsT, mlkemEncaps2Hook_fsT, mlkemDecapsHook_fsT,
    mlkemValidatePkHook_fsT, libcruxHmacHookMallocng_fsT,
    hookMemmove_fsT, cliBcmpHook_fsT, strlenHook_fsT,
    writeFileHook_fsT, writeStdoutHook_fsT,
    memrchrHook_fsT, fromUtf8Hook_fsT, fmtWriteHook0_fsT,
    formatInnerHook0_fsT, durationSinceExactHook_fsT, timeAddHook_fsT, blackBoxHook_fsT,
    compress256Hook_fsT, aesEncHookMallocng_fsT, aesDecHookMallocng_fsT, pubFromSecretHook_fsT,
    diffieHellmanHook_fsT, zeroizeSecretHook_fsT]

/-- Every extern hook of `cliExternsPlaced mmpl W` satisfies `HookFsTraced IsFsC`. -/
theorem fsTHooks_cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    FsTHooks (cliExternsPlaced mmpl W) := by
  intro n f h
  unfold cliExternsPlaced at h
  split at h
  · cases h
    exact panicked_fsT
  · exact fsTHooks_lookup (cliHookTablePlaced_fsT mmpl W) n f h

/-- `TraceFsSound` for any `Program.rebase` program at `cliExternsPlaced mmpl W`. -/
theorem traceFsSound_rebase_cli (pc : Program) (b : BitVec 64) (mmpl : Obj.MultiPlacement)
    (W : CliHooks) (hsvc : pc.svc = Syscall.standard := by rfl) :
    TraceFsSound (pc.rebase b (cliExternsPlaced mmpl W)) :=
  traceFsSound_of_fsTHooks (fsTHooks_cliExternsPlaced mmpl W) fsTHooks_none hsvc

/-- `TraceFsSound` for any `MultiPlacedLib.blockProgram` at `cliExternsPlaced mmpl W`. -/
theorem traceFsSound_blockProgram_cli (lib : Obj.MultiPlacedLib) (pl : Obj.MultiPlacement)
    (i : Nat) (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    TraceFsSound (lib.blockProgram pl i (cliExternsPlaced mmpl W)) := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  exact traceFsSound_of_fsTHooks (fsTHooks_cliExternsPlaced mmpl W) fsTHooks_none

/-- `TraceFsSound` on any block program `prog` at `cliExternsPlaced mmpl W`. -/
theorem traceFsSound_lsProg_cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [hprog : IsLsBlockProg prog i (cliExternsPlaced mmpl W)] :
    TraceFsSound prog := by
  rw [hprog.eq_blockProgram]
  exact traceFsSound_blockProgram_cli libsignalSessionLib lsmpl i mmpl W

/-- `TraceFsSound` for `MainHops.mProgPlaced (cliExternsPlaced mmpl W)`. -/
theorem traceFsSound_mProgPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    TraceFsSound (MainHops.mProgPlaced (cliExternsPlaced mmpl W)) :=
  traceFsSound_lsProg_cli mmpl W

/-- `TraceFsSound` for `SpecsPlaced.cliProgPlaced mmpl W`. -/
theorem traceFsSound_cliProgPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    TraceFsSound (CryptoVerification.SignalSession.cliProgPlaced mmpl W) :=
  traceFsSound_blockProgram_cli libsignalSessionLib lsmpl 617 mmpl W

/-- Pure `HookFsTraced IsFsC` predicate on `g : CliGhostHooks` (cost-model-free). -/
structure CliGhostHooksFs (g : CliGhostHooks) : Prop where
  alloc_fsT : HookFsTraced IsFsC g.alloc
  dealloc_fsT : HookFsTraced IsFsC g.dealloc
  realloc_fsT : HookFsTraced IsFsC g.realloc
  allocZeroed_fsT : HookFsTraced IsFsC g.allocZeroed
  shim_fsT : HookFsTraced IsFsC g.shim
  stringClone_fsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f
  memset_fsT : ∀ f, g.memset = some f → HookFsTraced IsFsC f := by intro _ h; cases h
  memcpy_fsT : ∀ f, g.memcpy = some f → HookFsTraced IsFsC f := by intro _ h; cases h

theorem fsTHooks_cliGhostExterns_of_fs {g : CliGhostHooks} {baseExt : LibsignalHooks}
    (hFs : CliGhostHooksFs g) (hBase : FsTHooks baseExt) :
    FsTHooks (cliGhostExterns g baseExt) := by
  intro sym f h
  unfold cliGhostExterns at h
  split at h
  · cases h; exact hFs.alloc_fsT
  · split at h
    · cases h; exact hFs.dealloc_fsT
    · split at h
      · cases h; exact hFs.realloc_fsT
      · split at h
        · cases h; exact hFs.allocZeroed_fsT
        · split at h
          · cases h; exact hFs.shim_fsT
          · split at h
            · cases hsc : g.stringClone with
              | some fc =>
                rw [hsc] at h; cases h; exact hFs.stringClone_fsT f hsc
              | none =>
                rw [hsc] at h; exact hBase sym f h
            · split at h
              · cases hrf : g.readFile with
                | some rf =>
                  rw [hrf] at h; cases h; exact rf.2
                | none =>
                  rw [hrf] at h; exact hBase sym f h
              · split at h
                · cases hrs : g.readStdin with
                  | some rs =>
                    rw [hrs] at h; cases h; exact rs.2
                  | none =>
                    rw [hrs] at h; exact hBase sym f h
                · split at h
                  · cases hms : g.memset with
                    | some ms =>
                      rw [hms] at h; cases h; exact hFs.memset_fsT f hms
                    | none =>
                      rw [hms] at h; exact hBase sym f h
                  · split at h
                    · cases hmc : g.memcpy with
                      | some mc =>
                        rw [hmc] at h; cases h; exact hFs.memcpy_fsT f hmc
                      | none =>
                        rw [hmc] at h; exact hBase sym f h
                    · exact hBase sym f h

theorem traceFsSound_lsProg_ghost_of_fs [LibsignalPlacement]
    {g : CliGhostHooks} {baseExt : LibsignalHooks}
    (hFs : CliGhostHooksFs g) (hBase : FsTHooks baseExt)
    {prog : Program} {i : Nat} [hprog : IsLsBlockProg prog i (cliGhostExterns g baseExt)] :
    TraceFsSound prog := by
  rw [hprog.eq_blockProgram]
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  exact traceFsSound_of_fsTHooks (fsTHooks_cliGhostExterns_of_fs hFs hBase) fsTHooks_none rfl

theorem traceFsSound_lsProg_cli_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hFs : CliGhostHooksFs g)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))] :
    TraceFsSound prog :=
  traceFsSound_lsProg_ghost_of_fs hFs (fsTHooks_cliExternsPlaced mmpl W)

theorem traceFsSound_mProgPlaced_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hFs : CliGhostHooksFs g) :
    TraceFsSound (MainHops.mProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) :=
  traceFsSound_lsProg_cli_ghost mmpl g W hFs

end CryptoVerification.SignalSession.Cli.RunGlue
